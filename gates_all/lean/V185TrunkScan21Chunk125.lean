import V185TrunkScan21Chunk124

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1522353 : List Nat := [1, 2, 2, 6, 10]
def baseStart_1522353 : Nat := 118140960795 + 1522353 * 2 ^ 59
def prefixEnd_1522353 : Nat := 4983230072969 + 3 ^ 40 * 1522353 * 2
def baseEnd_1522353 : Nat := 4289156734234225078663

theorem tailTrace_1522353 : CollatzResearch.WordTrace tailWord_1522353 prefixEnd_1522353 4289156734234225078663 := by
  unfold tailWord_1522353
  simp only [CollatzResearch.WordTrace]
  refine ⟨55524775453782553038075713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37016516969188368692050475 55524775453782553038075713)
  ·
    refine ⟨41643581590336914778556785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55524775453782553038075713 41643581590336914778556785)
    ·
      refine ⟨31232686192752686083917589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41643581590336914778556785 31232686192752686083917589)
      ·
        refine ⟨1464032165285282160183637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31232686192752686083917589 1464032165285282160183637)
        ·
          refine ⟨4289156734234225078663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1464032165285282160183637 4289156734234225078663)
          ·
            rfl

theorem cell21_1522353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 10].length) (baseStart_1522353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1522353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1522353 prefixEnd_1522353 := by exact prefixLift 1522353
  have htrace : WordTrace (prefixWord ++ tailWord_1522353) baseStart_1522353 baseEnd_1522353 := by
    simpa [prefixWord, tailWord_1522353, baseEnd_1522353] using wordTrace_append hprefix tailTrace_1522353
  have hstable : (prefixWord ++ tailWord_1522353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522353).length < 2 ^ (prefixWord ++ tailWord_1522353).sum := by decide
  have hdescent : baseEnd_1522353 < baseStart_1522353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522359 : List Nat := [1, 1, 3, 1, 6, 2, 2, 2, 3]
def baseStart_1522359 : Nat := 118140960795 + 1522359 * 2 ^ 59
def prefixEnd_1522359 : Nat := 4983230072969 + 3 ^ 40 * 1522359 * 2
def baseEnd_1522359 : Nat := 347423064754717554271691

theorem tailTrace_1522359 : CollatzResearch.WordTrace tailWord_1522359 prefixEnd_1522359 347423064754717554271691 := by
  unfold tailWord_1522359
  simp only [CollatzResearch.WordTrace]
  refine ⟨55524994291760816062794131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37016662861173877375196087 55524994291760816062794131)
  ·
    refine ⟨83287491437641224094191197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55524994291760816062794131 83287491437641224094191197)
    ·
      refine ⟨31232809289115459035321699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83287491437641224094191197 31232809289115459035321699)
      ·
        refine ⟨46849213933673188552982549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31232809289115459035321699 46849213933673188552982549)
        ·
          refine ⟨2196056903140930713421057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46849213933673188552982549 2196056903140930713421057)
          ·
            refine ⟨1647042677355698035065793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2196056903140930713421057 1647042677355698035065793)
            ·
              refine ⟨1235282008016773526299345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1647042677355698035065793 1235282008016773526299345)
              ·
                refine ⟨926461506012580144724509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1235282008016773526299345 926461506012580144724509)
                ·
                  refine ⟨347423064754717554271691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 926461506012580144724509 347423064754717554271691)
                  ·
                    rfl

theorem cell21_1522359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2, 3].length) (baseStart_1522359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1522359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1522359 prefixEnd_1522359 := by exact prefixLift 1522359
  have htrace : WordTrace (prefixWord ++ tailWord_1522359) baseStart_1522359 baseEnd_1522359 := by
    simpa [prefixWord, tailWord_1522359, baseEnd_1522359] using wordTrace_append hprefix tailTrace_1522359
  have hstable : (prefixWord ++ tailWord_1522359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522359).length < 2 ^ (prefixWord ++ tailWord_1522359).sum := by decide
  have hdescent : baseEnd_1522359 < baseStart_1522359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522401 : List Nat := [1, 2, 3, 1, 4, 1, 1, 5, 3]
def baseStart_1522401 : Nat := 118140960795 + 1522401 * 2 ^ 59
def prefixEnd_1522401 : Nat := 4983230072969 + 3 ^ 40 * 1522401 * 2
def baseEnd_1522401 : Nat := 347432649726934814571605

theorem tailTrace_1522401 : CollatzResearch.WordTrace tailWord_1522401 prefixEnd_1522401 347432649726934814571605 := by
  unfold tailWord_1522401
  simp only [CollatzResearch.WordTrace]
  refine ⟨55526526157608657235823057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37017684105072438157215371 55526526157608657235823057)
  ·
    refine ⟨41644894618206492926867293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55526526157608657235823057 41644894618206492926867293)
    ·
      refine ⟨15616835481827434847575235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41644894618206492926867293 15616835481827434847575235)
      ·
        refine ⟨23425253222741152271362853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15616835481827434847575235 23425253222741152271362853)
        ·
          refine ⟨4392234979263966050880535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23425253222741152271362853 4392234979263966050880535)
          ·
            refine ⟨6588352468895949076320803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4392234979263966050880535 6588352468895949076320803)
            ·
              refine ⟨9882528703343923614481205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6588352468895949076320803 9882528703343923614481205)
              ·
                refine ⟨926487065938492838857613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9882528703343923614481205 926487065938492838857613)
                ·
                  refine ⟨347432649726934814571605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 926487065938492838857613 347432649726934814571605)
                  ·
                    rfl

theorem cell21_1522401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 3].length) (baseStart_1522401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1522401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1522401 prefixEnd_1522401 := by exact prefixLift 1522401
  have htrace : WordTrace (prefixWord ++ tailWord_1522401) baseStart_1522401 baseEnd_1522401 := by
    simpa [prefixWord, tailWord_1522401, baseEnd_1522401] using wordTrace_append hprefix tailTrace_1522401
  have hstable : (prefixWord ++ tailWord_1522401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522401).length < 2 ^ (prefixWord ++ tailWord_1522401).sum := by decide
  have hdescent : baseEnd_1522401 < baseStart_1522401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522415 : List Nat := [1, 1, 2, 1, 5, 2, 3, 2, 4]
def baseStart_1522415 : Nat := 118140960795 + 1522415 * 2 ^ 59
def prefixEnd_1522415 : Nat := 4983230072969 + 3 ^ 40 * 1522415 * 2
def baseEnd_1522415 : Nat := 347435844717673901338243

theorem tailTrace_1522415 : CollatzResearch.WordTrace tailWord_1522415 prefixEnd_1522415 347435844717673901338243 := by
  unfold tailWord_1522415
  simp only [CollatzResearch.WordTrace]
  refine ⟨55527036779557937626832699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37018024519705291751221799 55527036779557937626832699)
  ·
    refine ⟨83290555169336906440249049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55527036779557937626832699 83290555169336906440249049)
    ·
      refine ⟨62467916377002679830186787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83290555169336906440249049 62467916377002679830186787)
      ·
        refine ⟨93701874565504019745280181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62467916377002679830186787 93701874565504019745280181)
        ·
          refine ⟨8784550740516001851120017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93701874565504019745280181 8784550740516001851120017)
          ·
            refine ⟨6588413055387001388340013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8784550740516001851120017 6588413055387001388340013)
            ·
              refine ⟨2470654895770125520627505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6588413055387001388340013 2470654895770125520627505)
              ·
                refine ⟨1852991171827594140470629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2470654895770125520627505 1852991171827594140470629)
                ·
                  refine ⟨347435844717673901338243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1852991171827594140470629 347435844717673901338243)
                  ·
                    rfl

theorem cell21_1522415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 4].length) (baseStart_1522415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1522415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1522415 prefixEnd_1522415 := by exact prefixLift 1522415
  have htrace : WordTrace (prefixWord ++ tailWord_1522415) baseStart_1522415 baseEnd_1522415 := by
    simpa [prefixWord, tailWord_1522415, baseEnd_1522415] using wordTrace_append hprefix tailTrace_1522415
  have hstable : (prefixWord ++ tailWord_1522415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522415).length < 2 ^ (prefixWord ++ tailWord_1522415).sum := by decide
  have hdescent : baseEnd_1522415 < baseStart_1522415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522570 : List Nat := [3, 1, 2, 4, 1, 2, 2, 3, 3]
def baseStart_1522570 : Nat := 118140960795 + 1522570 * 2 ^ 59
def prefixEnd_1522570 : Nat := 4983230072969 + 3 ^ 40 * 1522570 * 2
def baseEnd_1522570 : Nat := 347471217829428076254593

theorem tailTrace_1522570 : CollatzResearch.WordTrace tailWord_1522570 prefixEnd_1522570 347471217829428076254593 := by
  unfold tailWord_1522570
  simp only [CollatzResearch.WordTrace]
  refine ⟨13883172523499099774681291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37021793395997599399150109 13883172523499099774681291)
  ·
    refine ⟨20824758785248649662021937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13883172523499099774681291 20824758785248649662021937)
    ·
      refine ⟨15618569088936487246516453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20824758785248649662021937 15618569088936487246516453)
      ·
        refine ⟨2928481704175591358721835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15618569088936487246516453 2928481704175591358721835)
        ·
          refine ⟨4392722556263387038082753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2928481704175591358721835 4392722556263387038082753)
          ·
            refine ⟨3294541917197540278562065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4392722556263387038082753 3294541917197540278562065)
            ·
              refine ⟨2470906437898155208921549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3294541917197540278562065 2470906437898155208921549)
              ·
                refine ⟨926589914211808203345581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2470906437898155208921549 926589914211808203345581)
                ·
                  refine ⟨347471217829428076254593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 926589914211808203345581 347471217829428076254593)
                  ·
                    rfl

theorem cell21_1522570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3, 3].length) (baseStart_1522570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1522570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1522570 prefixEnd_1522570 := by exact prefixLift 1522570
  have htrace : WordTrace (prefixWord ++ tailWord_1522570) baseStart_1522570 baseEnd_1522570 := by
    simpa [prefixWord, tailWord_1522570, baseEnd_1522570] using wordTrace_append hprefix tailTrace_1522570
  have hstable : (prefixWord ++ tailWord_1522570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522570).length < 2 ^ (prefixWord ++ tailWord_1522570).sum := by decide
  have hdescent : baseEnd_1522570 < baseStart_1522570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522595 : List Nat := [1, 1, 1, 4, 1, 2, 3, 3, 5]
def baseStart_1522595 : Nat := 118140960795 + 1522595 * 2 ^ 59
def prefixEnd_1522595 : Nat := 4983230072969 + 3 ^ 40 * 1522595 * 2
def baseEnd_1522595 : Nat := 347476923170033588337875

theorem tailTrace_1522595 : CollatzResearch.WordTrace tailWord_1522595 prefixEnd_1522595 347476923170033588337875 := by
  unfold tailWord_1522595
  simp only [CollatzResearch.WordTrace]
  refine ⟨55533601918905828368385239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37022401279270552245590159 55533601918905828368385239)
  ·
    refine ⟨83300402878358742552577859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55533601918905828368385239 83300402878358742552577859)
    ·
      refine ⟨124950604317538113828866789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83300402878358742552577859 124950604317538113828866789)
      ·
        refine ⟨23428238309538396342912523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124950604317538113828866789 23428238309538396342912523)
        ·
          refine ⟨35142357464307594514368785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23428238309538396342912523 35142357464307594514368785)
          ·
            refine ⟨26356768098230695885776589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35142357464307594514368785 26356768098230695885776589)
            ·
              refine ⟨9883788036836510957166221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26356768098230695885776589 9883788036836510957166221)
              ·
                refine ⟨3706420513813691608937333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9883788036836510957166221 3706420513813691608937333)
                ·
                  refine ⟨347476923170033588337875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3706420513813691608937333 347476923170033588337875)
                  ·
                    rfl

theorem cell21_1522595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 5].length) (baseStart_1522595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1522595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1522595 prefixEnd_1522595 := by exact prefixLift 1522595
  have htrace : WordTrace (prefixWord ++ tailWord_1522595) baseStart_1522595 baseEnd_1522595 := by
    simpa [prefixWord, tailWord_1522595, baseEnd_1522595] using wordTrace_append hprefix tailTrace_1522595
  have hstable : (prefixWord ++ tailWord_1522595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522595).length < 2 ^ (prefixWord ++ tailWord_1522595).sum := by decide
  have hdescent : baseEnd_1522595 < baseStart_1522595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522646 : List Nat := [5, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_1522646 : Nat := 118140960795 + 1522646 * 2 ^ 59
def prefixEnd_1522646 : Nat := 4983230072969 + 3 ^ 40 * 1522646 * 2
def baseEnd_1522646 : Nat := 347488562064868832987771

theorem tailTrace_1522646 : CollatzResearch.WordTrace tailWord_1522646 prefixEnd_1522646 347488562064868832987771 := by
  unfold tailWord_1522646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3470966377607566504905737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37023641361147376052327861 3470966377607566504905737)
  ·
    refine ⟨2603224783205674878679303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3470966377607566504905737 2603224783205674878679303)
    ·
      refine ⟨3904837174808512318018955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2603224783205674878679303 3904837174808512318018955)
      ·
        refine ⟨5857255762212768477028433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3904837174808512318018955 5857255762212768477028433)
        ·
          refine ⟨4392941821659576357771325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5857255762212768477028433 4392941821659576357771325)
          ·
            refine ⟨1647353183122341134164247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4392941821659576357771325 1647353183122341134164247)
            ·
              refine ⟨2471029774683511701246371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1647353183122341134164247 2471029774683511701246371)
              ·
                refine ⟨3706544662025267551869557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2471029774683511701246371 3706544662025267551869557)
                ·
                  refine ⟨347488562064868832987771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3706544662025267551869557 347488562064868832987771)
                  ·
                    rfl

theorem cell21_1522646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_1522646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1522646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1522646 prefixEnd_1522646 := by exact prefixLift 1522646
  have htrace : WordTrace (prefixWord ++ tailWord_1522646) baseStart_1522646 baseEnd_1522646 := by
    simpa [prefixWord, tailWord_1522646, baseEnd_1522646] using wordTrace_append hprefix tailTrace_1522646
  have hstable : (prefixWord ++ tailWord_1522646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522646).length < 2 ^ (prefixWord ++ tailWord_1522646).sum := by decide
  have hdescent : baseEnd_1522646 < baseStart_1522646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522753 : List Nat := [1, 2, 5, 1, 4, 1, 1, 2, 4]
def baseStart_1522753 : Nat := 118140960795 + 1522753 * 2 ^ 59
def prefixEnd_1522753 : Nat := 4983230072969 + 3 ^ 40 * 1522753 * 2
def baseEnd_1522753 : Nat := 347512980922660424704219

theorem tailTrace_1522753 : CollatzResearch.WordTrace tailWord_1522753 prefixEnd_1522753 347512980922660424704219 := by
  unfold tailWord_1522753
  simp only [CollatzResearch.WordTrace]
  refine ⟨55539364652333421352636913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37026243101555614235091275 55539364652333421352636913)
  ·
    refine ⟨41654523489250066014477685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55539364652333421352636913 41654523489250066014477685)
    ·
      refine ⟨3905111577117193688857283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41654523489250066014477685 3905111577117193688857283)
      ·
        refine ⟨5857667365675790533285925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3905111577117193688857283 5857667365675790533285925)
        ·
          refine ⟨1098312631064210724991111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5857667365675790533285925 1098312631064210724991111)
          ·
            refine ⟨1647468946596316087486667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1098312631064210724991111 1647468946596316087486667)
            ·
              refine ⟨2471203419894474131230001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1647468946596316087486667 2471203419894474131230001)
              ·
                refine ⟨1853402564920855598422501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2471203419894474131230001 1853402564920855598422501)
                ·
                  refine ⟨347512980922660424704219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1853402564920855598422501 347512980922660424704219)
                  ·
                    rfl

theorem cell21_1522753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 4].length) (baseStart_1522753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1522753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1522753 prefixEnd_1522753 := by exact prefixLift 1522753
  have htrace : WordTrace (prefixWord ++ tailWord_1522753) baseStart_1522753 baseEnd_1522753 := by
    simpa [prefixWord, tailWord_1522753, baseEnd_1522753] using wordTrace_append hprefix tailTrace_1522753
  have hstable : (prefixWord ++ tailWord_1522753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522753).length < 2 ^ (prefixWord ++ tailWord_1522753).sum := by decide
  have hdescent : baseEnd_1522753 < baseStart_1522753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522798 : List Nat := [4, 1, 2, 2, 1, 4, 1, 3, 3]
def baseStart_1522798 : Nat := 118140960795 + 1522798 * 2 ^ 59
def prefixEnd_1522798 : Nat := 4983230072969 + 3 ^ 40 * 1522798 * 2
def baseEnd_1522798 : Nat := 347523250535750346454127

theorem tailTrace_1522798 : CollatzResearch.WordTrace tailWord_1522798 prefixEnd_1522798 347523250535750346454127 := by
  unfold tailWord_1522798
  simp only [CollatzResearch.WordTrace]
  refine ⟨6942625742146299254753131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37027337291446929358683365 6942625742146299254753131)
  ·
    refine ⟨10413938613219448882129697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6942625742146299254753131 10413938613219448882129697)
    ·
      refine ⟨7810453959914586661597273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10413938613219448882129697 7810453959914586661597273)
      ·
        refine ⟨5857840469935939996197955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7810453959914586661597273 5857840469935939996197955)
        ·
          refine ⟨8786760704903909994296933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5857840469935939996197955 8786760704903909994296933)
          ·
            refine ⟨1647517632169483123930675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8786760704903909994296933 1647517632169483123930675)
            ·
              refine ⟨2471276448254224685896013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1647517632169483123930675 2471276448254224685896013)
              ·
                refine ⟨926728668095334257211005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2471276448254224685896013 926728668095334257211005)
                ·
                  refine ⟨347523250535750346454127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 926728668095334257211005 347523250535750346454127)
                  ·
                    rfl

theorem cell21_1522798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_1522798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1522798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1522798 prefixEnd_1522798 := by exact prefixLift 1522798
  have htrace : WordTrace (prefixWord ++ tailWord_1522798) baseStart_1522798 baseEnd_1522798 := by
    simpa [prefixWord, tailWord_1522798, baseEnd_1522798] using wordTrace_append hprefix tailTrace_1522798
  have hstable : (prefixWord ++ tailWord_1522798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522798).length < 2 ^ (prefixWord ++ tailWord_1522798).sum := by decide
  have hdescent : baseEnd_1522798 < baseStart_1522798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522809 : List Nat := [1, 2, 1, 3, 5, 2, 7]
def baseStart_1522809 : Nat := 118140960795 + 1522809 * 2 ^ 59
def prefixEnd_1522809 : Nat := 4983230072969 + 3 ^ 40 * 1522809 * 2
def baseEnd_1522809 : Nat := 38613973431735196863419

theorem tailTrace_1522809 : CollatzResearch.WordTrace tailWord_1522809 prefixEnd_1522809 38613973431735196863419 := by
  unfold tailWord_1522809
  simp only [CollatzResearch.WordTrace]
  refine ⟨55541407140130542916675481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37027604760087028611116987 55541407140130542916675481)
  ·
    refine ⟨41656055355097907187506611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55541407140130542916675481 41656055355097907187506611)
    ·
      refine ⟨62484083032646860781259917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41656055355097907187506611 62484083032646860781259917)
      ·
        refine ⟨23431531137242572792972469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62484083032646860781259917 23431531137242572792972469)
        ·
          refine ⟨2196706044116491199341169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23431531137242572792972469 2196706044116491199341169)
          ·
            refine ⟨1647529533087368399505877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2196706044116491199341169 1647529533087368399505877)
            ·
              refine ⟨38613973431735196863419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1647529533087368399505877 38613973431735196863419)
              ·
                rfl

theorem cell21_1522809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 7].length) (baseStart_1522809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1522809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1522809 prefixEnd_1522809 := by exact prefixLift 1522809
  have htrace : WordTrace (prefixWord ++ tailWord_1522809) baseStart_1522809 baseEnd_1522809 := by
    simpa [prefixWord, tailWord_1522809, baseEnd_1522809] using wordTrace_append hprefix tailTrace_1522809
  have hstable : (prefixWord ++ tailWord_1522809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522809).length < 2 ^ (prefixWord ++ tailWord_1522809).sum := by decide
  have hdescent : baseEnd_1522809 < baseStart_1522809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522837 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 8]
def baseStart_1522837 : Nat := 118140960795 + 1522837 * 2 ^ 59
def prefixEnd_1522837 : Nat := 4983230072969 + 3 ^ 40 * 1522837 * 2
def baseEnd_1522837 : Nat := 347532150867094945304047

theorem tailTrace_1522837 : CollatzResearch.WordTrace tailWord_1522837 prefixEnd_1522837 347532150867094945304047 := by
  unfold tailWord_1522837
  simp only [CollatzResearch.WordTrace]
  refine ⟨55542428384029103698694765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37028285589352735799129843 55542428384029103698694765)
  ·
    refine ⟨20828410644010913887010537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55542428384029103698694765 20828410644010913887010537)
    ·
      refine ⟨15621307983008185415257903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20828410644010913887010537 15621307983008185415257903)
      ·
        refine ⟨23431961974512278122886855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15621307983008185415257903 23431961974512278122886855)
        ·
          refine ⟨35147942961768417184330283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23431961974512278122886855 35147942961768417184330283)
          ·
            refine ⟨52721914442652625776495425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35147942961768417184330283 52721914442652625776495425)
            ·
              refine ⟨39541435831989469332371569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52721914442652625776495425 39541435831989469332371569)
              ·
                refine ⟨29656076873992101999278677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39541435831989469332371569 29656076873992101999278677)
                ·
                  refine ⟨347532150867094945304047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29656076873992101999278677 347532150867094945304047)
                  ·
                    rfl

theorem cell21_1522837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_1522837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1522837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1522837 prefixEnd_1522837 := by exact prefixLift 1522837
  have htrace : WordTrace (prefixWord ++ tailWord_1522837) baseStart_1522837 baseEnd_1522837 := by
    simpa [prefixWord, tailWord_1522837, baseEnd_1522837] using wordTrace_append hprefix tailTrace_1522837
  have hstable : (prefixWord ++ tailWord_1522837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522837).length < 2 ^ (prefixWord ++ tailWord_1522837).sum := by decide
  have hdescent : baseEnd_1522837 < baseStart_1522837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522916 : List Nat := [2, 3, 1, 1, 1, 2, 3, 5, 3]
def baseStart_1522916 : Nat := 118140960795 + 1522916 * 2 ^ 59
def prefixEnd_1522916 : Nat := 4983230072969 + 3 ^ 40 * 1522916 * 2
def baseEnd_1522916 : Nat := 347550179743408363487219

theorem tailTrace_1522916 : CollatzResearch.WordTrace tailWord_1522916 prefixEnd_1522916 347550179743408363487219 := by
  unfold tailWord_1522916
  simp only [CollatzResearch.WordTrace]
  refine ⟨27772654875371450095410301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37030206500495266793880401 27772654875371450095410301)
  ·
    refine ⟨10414745578264293785778863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27772654875371450095410301 10414745578264293785778863)
    ·
      refine ⟨15622118367396440678668295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10414745578264293785778863 15622118367396440678668295)
      ·
        refine ⟨23433177551094661018002443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15622118367396440678668295 23433177551094661018002443)
        ·
          refine ⟨35149766326641991527003665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23433177551094661018002443 35149766326641991527003665)
          ·
            refine ⟨26362324744981493645252749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35149766326641991527003665 26362324744981493645252749)
            ·
              refine ⟨9885871779368060116969781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26362324744981493645252749 9885871779368060116969781)
              ·
                refine ⟨926800479315755635965917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9885871779368060116969781 926800479315755635965917)
                ·
                  refine ⟨347550179743408363487219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 926800479315755635965917 347550179743408363487219)
                  ·
                    rfl

theorem cell21_1522916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_1522916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1522916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1522916 prefixEnd_1522916 := by exact prefixLift 1522916
  have htrace : WordTrace (prefixWord ++ tailWord_1522916) baseStart_1522916 baseEnd_1522916 := by
    simpa [prefixWord, tailWord_1522916, baseEnd_1522916] using wordTrace_append hprefix tailTrace_1522916
  have hstable : (prefixWord ++ tailWord_1522916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522916).length < 2 ^ (prefixWord ++ tailWord_1522916).sum := by decide
  have hdescent : baseEnd_1522916 < baseStart_1522916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522947 : List Nat := [1, 1, 1, 3, 2, 5, 3, 1, 4]
def baseStart_1522947 : Nat := 118140960795 + 1522947 * 2 ^ 59
def prefixEnd_1522947 : Nat := 4983230072969 + 3 ^ 40 * 1522947 * 2
def baseEnd_1522947 : Nat := 347557254365759198470489

theorem tailTrace_1522947 : CollatzResearch.WordTrace tailWord_1522947 prefixEnd_1522947 347557254365759198470489 := by
  unfold tailWord_1522947
  simp only [CollatzResearch.WordTrace]
  refine ⟨55546440413630592485199095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37030960275753728323466063 55546440413630592485199095)
  ·
    refine ⟨83319660620445888727798643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55546440413630592485199095 83319660620445888727798643)
    ·
      refine ⟨124979490930668833091697965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83319660620445888727798643 124979490930668833091697965)
      ·
        refine ⟨46867309099000812409386737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124979490930668833091697965 46867309099000812409386737)
        ·
          refine ⟨35150481824250609307040053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46867309099000812409386737 35150481824250609307040053)
          ·
            refine ⟨3295357671023494622535005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35150481824250609307040053 3295357671023494622535005)
            ·
              refine ⟨1235759126633810483450627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3295357671023494622535005 1235759126633810483450627)
              ·
                refine ⟨1853638689950715725175941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1235759126633810483450627 1853638689950715725175941)
                ·
                  refine ⟨347557254365759198470489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1853638689950715725175941 347557254365759198470489)
                  ·
                    rfl

theorem cell21_1522947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 4].length) (baseStart_1522947 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1522947 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1522947 prefixEnd_1522947 := by exact prefixLift 1522947
  have htrace : WordTrace (prefixWord ++ tailWord_1522947) baseStart_1522947 baseEnd_1522947 := by
    simpa [prefixWord, tailWord_1522947, baseEnd_1522947] using wordTrace_append hprefix tailTrace_1522947
  have hstable : (prefixWord ++ tailWord_1522947).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522947).length < 2 ^ (prefixWord ++ tailWord_1522947).sum := by decide
  have hdescent : baseEnd_1522947 < baseStart_1522947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522978 : List Nat := [3, 3, 1, 1, 5, 1, 7]
def baseStart_1522978 : Nat := 118140960795 + 1522978 * 2 ^ 59
def prefixEnd_1522978 : Nat := 4983230072969 + 3 ^ 40 * 1522978 * 2
def baseEnd_1522978 : Nat := 38618258776456670383751

theorem tailTrace_1522978 : CollatzResearch.WordTrace tailWord_1522978 prefixEnd_1522978 38618258776456670383751 := by
  unfold tailWord_1522978
  simp only [CollatzResearch.WordTrace]
  refine ⟨13886892769129571194894397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37031714051012189853051725 13886892769129571194894397)
  ·
    refine ⟨5207584788423589198085399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13886892769129571194894397 5207584788423589198085399)
    ·
      refine ⟨7811377182635383797128099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5207584788423589198085399 7811377182635383797128099)
      ·
        refine ⟨11717065773953075695692149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7811377182635383797128099 11717065773953075695692149)
        ·
          refine ⟨1098474916308100846471139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11717065773953075695692149 1098474916308100846471139)
          ·
            refine ⟨1647712374462151269706709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1098474916308100846471139 1647712374462151269706709)
            ·
              refine ⟨38618258776456670383751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1647712374462151269706709 38618258776456670383751)
              ·
                rfl

theorem cell21_1522978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 7].length) (baseStart_1522978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1522978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1522978 prefixEnd_1522978 := by exact prefixLift 1522978
  have htrace : WordTrace (prefixWord ++ tailWord_1522978) baseStart_1522978 baseEnd_1522978 := by
    simpa [prefixWord, tailWord_1522978, baseEnd_1522978] using wordTrace_append hprefix tailTrace_1522978
  have hstable : (prefixWord ++ tailWord_1522978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522978).length < 2 ^ (prefixWord ++ tailWord_1522978).sum := by decide
  have hdescent : baseEnd_1522978 < baseStart_1522978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522998 : List Nat := [5, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_1522998 : Nat := 118140960795 + 1522998 * 2 ^ 59
def prefixEnd_1522998 : Nat := 4983230072969 + 3 ^ 40 * 1522998 * 2
def baseEnd_1522998 : Nat := 347568893260594443120385

theorem tailTrace_1522998 : CollatzResearch.WordTrace tailWord_1522998 prefixEnd_1522998 347568893260594443120385 := by
  unfold tailWord_1522998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3471768783527864262206603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37032200357630552130203765 3471768783527864262206603)
  ·
    refine ⟨5207653175291796393309905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3471768783527864262206603 5207653175291796393309905)
    ·
      refine ⟨3905739881468847294982429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5207653175291796393309905 3905739881468847294982429)
      ·
        refine ⟨1464652455550817735618411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3905739881468847294982429 1464652455550817735618411)
        ·
          refine ⟨2196978683326226603427617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1464652455550817735618411 2196978683326226603427617)
          ·
            refine ⟨1647734012494669952570713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2196978683326226603427617 1647734012494669952570713)
            ·
              refine ⟨1235800509371002464428035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1647734012494669952570713 1235800509371002464428035)
              ·
                refine ⟨1853700764056503696642053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1235800509371002464428035 1853700764056503696642053)
                ·
                  refine ⟨347568893260594443120385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1853700764056503696642053 347568893260594443120385)
                  ·
                    rfl

theorem cell21_1522998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_1522998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1522998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1522998 prefixEnd_1522998 := by exact prefixLift 1522998
  have htrace : WordTrace (prefixWord ++ tailWord_1522998) baseStart_1522998 baseEnd_1522998 := by
    simpa [prefixWord, tailWord_1522998, baseEnd_1522998] using wordTrace_append hprefix tailTrace_1522998
  have hstable : (prefixWord ++ tailWord_1522998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522998).length < 2 ^ (prefixWord ++ tailWord_1522998).sum := by decide
  have hdescent : baseEnd_1522998 < baseStart_1522998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523020 : List Nat := [2, 2, 1, 3, 2, 2, 2, 7]
def baseStart_1523020 : Nat := 118140960795 + 1523020 * 2 ^ 59
def prefixEnd_1523020 : Nat := 4983230072969 + 3 ^ 40 * 1523020 * 2
def baseEnd_1523020 : Nat := 115857971320109097917891

theorem tailTrace_1523020 : CollatzResearch.WordTrace tailWord_1523020 prefixEnd_1523020 115857971320109097917891 := by
  unfold tailWord_1523020
  simp only [CollatzResearch.WordTrace]
  refine ⟨27774551471183062976303257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37032735294910750635071009 27774551471183062976303257)
  ·
    refine ⟨20830913603387297232227443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27774551471183062976303257 20830913603387297232227443)
    ·
      refine ⟨31246370405080945848341165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20830913603387297232227443 31246370405080945848341165)
      ·
        refine ⟨11717388901905354693127937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31246370405080945848341165 11717388901905354693127937)
        ·
          refine ⟨8788041676429016019845953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11717388901905354693127937 8788041676429016019845953)
          ·
            refine ⟨6591031257321762014884465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8788041676429016019845953 6591031257321762014884465)
            ·
              refine ⟨4943273442991321511163349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6591031257321762014884465 4943273442991321511163349)
              ·
                refine ⟨115857971320109097917891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4943273442991321511163349 115857971320109097917891)
                ·
                  rfl

theorem cell21_1523020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 7].length) (baseStart_1523020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1523020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1523020 prefixEnd_1523020 := by exact prefixLift 1523020
  have htrace : WordTrace (prefixWord ++ tailWord_1523020) baseStart_1523020 baseEnd_1523020 := by
    simpa [prefixWord, tailWord_1523020, baseEnd_1523020] using wordTrace_append hprefix tailTrace_1523020
  have hstable : (prefixWord ++ tailWord_1523020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523020).length < 2 ^ (prefixWord ++ tailWord_1523020).sum := by decide
  have hdescent : baseEnd_1523020 < baseStart_1523020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523161 : List Nat := [1, 2, 1, 2, 4, 3, 3, 2, 3]
def baseStart_1523161 : Nat := 118140960795 + 1523161 * 2 ^ 59
def prefixEnd_1523161 : Nat := 4983230072969 + 3 ^ 40 * 1523161 * 2
def baseEnd_1523161 : Nat := 347606092081342381903385

theorem tailTrace_1523161 : CollatzResearch.WordTrace tailWord_1523161 prefixEnd_1523161 347606092081342381903385 := by
  unfold tailWord_1523161
  simp only [CollatzResearch.WordTrace]
  refine ⟨55554245634855307033489337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37036163756570204688992891 55554245634855307033489337)
  ·
    refine ⟨41665684226141480275117003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55554245634855307033489337 41665684226141480275117003)
    ·
      refine ⟨62498526339212220412675505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41665684226141480275117003 62498526339212220412675505)
      ·
        refine ⟨46873894754409165309506629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62498526339212220412675505 46873894754409165309506629)
        ·
          refine ⟨8788855266451718495532493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46873894754409165309506629 8788855266451718495532493)
          ·
            refine ⟨3295820724919394435824685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8788855266451718495532493 3295820724919394435824685)
            ·
              refine ⟨1235932771844772913434257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3295820724919394435824685 1235932771844772913434257)
              ·
                refine ⟨926949578883579685075693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1235932771844772913434257 926949578883579685075693)
                ·
                  refine ⟨347606092081342381903385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 926949578883579685075693 347606092081342381903385)
                  ·
                    rfl

theorem cell21_1523161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2, 3].length) (baseStart_1523161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1523161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1523161 prefixEnd_1523161 := by exact prefixLift 1523161
  have htrace : WordTrace (prefixWord ++ tailWord_1523161) baseStart_1523161 baseEnd_1523161 := by
    simpa [prefixWord, tailWord_1523161, baseEnd_1523161] using wordTrace_append hprefix tailTrace_1523161
  have hstable : (prefixWord ++ tailWord_1523161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523161).length < 2 ^ (prefixWord ++ tailWord_1523161).sum := by decide
  have hdescent : baseEnd_1523161 < baseStart_1523161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523175 : List Nat := [1, 1, 5, 2, 1, 2, 4, 1, 4]
def baseStart_1523175 : Nat := 118140960795 + 1523175 * 2 ^ 59
def prefixEnd_1523175 : Nat := 4983230072969 + 3 ^ 40 * 1523175 * 2
def baseEnd_1523175 : Nat := 347609287072081468670023

theorem tailTrace_1523175 : CollatzResearch.WordTrace tailWord_1523175 prefixEnd_1523175 347609287072081468670023 := by
  unfold tailWord_1523175
  simp only [CollatzResearch.WordTrace]
  refine ⟨55554756256804587424498979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37036504171203058282999319 55554756256804587424498979)
  ·
    refine ⟨83332134385206881136748469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55554756256804587424498979 83332134385206881136748469)
    ·
      refine ⟨7812387598613145106570169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83332134385206881136748469 7812387598613145106570169)
      ·
        refine ⟨5859290698959858829927627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7812387598613145106570169 5859290698959858829927627)
        ·
          refine ⟨8788936048439788244891441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5859290698959858829927627 8788936048439788244891441)
          ·
            refine ⟨6591702036329841183668581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8788936048439788244891441 6591702036329841183668581)
            ·
              refine ⟨1235944131811845221937859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6591702036329841183668581 1235944131811845221937859)
              ·
                refine ⟨1853916197717767832906789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1235944131811845221937859 1853916197717767832906789)
                ·
                  refine ⟨347609287072081468670023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1853916197717767832906789 347609287072081468670023)
                  ·
                    rfl

theorem cell21_1523175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 4].length) (baseStart_1523175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1523175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1523175 prefixEnd_1523175 := by exact prefixLift 1523175
  have htrace : WordTrace (prefixWord ++ tailWord_1523175) baseStart_1523175 baseEnd_1523175 := by
    simpa [prefixWord, tailWord_1523175, baseEnd_1523175] using wordTrace_append hprefix tailTrace_1523175
  have hstable : (prefixWord ++ tailWord_1523175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523175).length < 2 ^ (prefixWord ++ tailWord_1523175).sum := by decide
  have hdescent : baseEnd_1523175 < baseStart_1523175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523189 : List Nat := [1, 3, 5, 1, 1, 1, 2, 7]
def baseStart_1523189 : Nat := 118140960795 + 1523189 * 2 ^ 59
def prefixEnd_1523189 : Nat := 4983230072969 + 3 ^ 40 * 1523189 * 2
def baseEnd_1523189 : Nat := 115870827354273518478887

theorem tailTrace_1523189 : CollatzResearch.WordTrace tailWord_1523189 prefixEnd_1523189 115870827354273518478887 := by
  unfold tailWord_1523189
  simp only [CollatzResearch.WordTrace]
  refine ⟨55555266878753867815508621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37036844585835911877005747 55555266878753867815508621)
  ·
    refine ⟨20833225079532700430815733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55555266878753867815508621 20833225079532700430815733)
    ·
      refine ⟨1953114851206190665388975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20833225079532700430815733 1953114851206190665388975)
      ·
        refine ⟨2929672276809285998083463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1953114851206190665388975 2929672276809285998083463)
        ·
          refine ⟨4394508415213928997125195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2929672276809285998083463 4394508415213928997125195)
          ·
            refine ⟨6591762622820893495687793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4394508415213928997125195 6591762622820893495687793)
            ·
              refine ⟨4943821967115670121765845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6591762622820893495687793 4943821967115670121765845)
              ·
                refine ⟨115870827354273518478887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4943821967115670121765845 115870827354273518478887)
                ·
                  rfl

theorem cell21_1523189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 7].length) (baseStart_1523189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1523189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1523189 prefixEnd_1523189 := by exact prefixLift 1523189
  have htrace : WordTrace (prefixWord ++ tailWord_1523189) baseStart_1523189 baseEnd_1523189 := by
    simpa [prefixWord, tailWord_1523189, baseEnd_1523189] using wordTrace_append hprefix tailTrace_1523189
  have hstable : (prefixWord ++ tailWord_1523189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523189).length < 2 ^ (prefixWord ++ tailWord_1523189).sum := by decide
  have hdescent : baseEnd_1523189 < baseStart_1523189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523206 : List Nat := [6, 2, 1, 1, 11]
def baseStart_1523206 : Nat := 118140960795 + 1523206 * 2 ^ 59
def prefixEnd_1523206 : Nat := 4983230072969 + 3 ^ 40 * 1523206 * 2
def baseEnd_1523206 : Nat := 4291560020918917329053

theorem tailTrace_1523206 : CollatzResearch.WordTrace tailWord_1523206 prefixEnd_1523206 4291560020918917329053 := by
  unfold tailWord_1523206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1736121466240383741214921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37037257946461519812584981 1736121466240383741214921)
  ·
    refine ⟨1302091099680287805911191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1736121466240383741214921 1302091099680287805911191)
    ·
      refine ⟨1953136649520431708866787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1302091099680287805911191 1953136649520431708866787)
      ·
        refine ⟨2929704974280647563300181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1953136649520431708866787 2929704974280647563300181)
        ·
          refine ⟨4291560020918917329053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2929704974280647563300181 4291560020918917329053)
          ·
            rfl

theorem cell21_1523206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 11].length) (baseStart_1523206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1523206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1523206 prefixEnd_1523206 := by exact prefixLift 1523206
  have htrace : WordTrace (prefixWord ++ tailWord_1523206) baseStart_1523206 baseEnd_1523206 := by
    simpa [prefixWord, tailWord_1523206, baseEnd_1523206] using wordTrace_append hprefix tailTrace_1523206
  have hstable : (prefixWord ++ tailWord_1523206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523206).length < 2 ^ (prefixWord ++ tailWord_1523206).sum := by decide
  have hdescent : baseEnd_1523206 < baseStart_1523206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523234 : List Nat := [3, 3, 1, 1, 1, 1, 4, 3, 4]
def baseStart_1523234 : Nat := 118140960795 + 1523234 * 2 ^ 59
def prefixEnd_1523234 : Nat := 4983230072969 + 3 ^ 40 * 1523234 * 2
def baseEnd_1523234 : Nat := 347622751675910477186569

theorem tailTrace_1523234 : CollatzResearch.WordTrace tailWord_1523234 prefixEnd_1523234 347622751675910477186569 := by
  unfold tailWord_1523234
  simp only [CollatzResearch.WordTrace]
  refine ⟨13889227040897710125224189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37037938775727227000597837 13889227040897710125224189)
  ·
    refine ⟨5208460140336641296959071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13889227040897710125224189 5208460140336641296959071)
    ·
      refine ⟨7812690210504961945438607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5208460140336641296959071 7812690210504961945438607)
      ·
        refine ⟨11719035315757442918157911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7812690210504961945438607 11719035315757442918157911)
        ·
          refine ⟨17578552973636164377236867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11719035315757442918157911 17578552973636164377236867)
          ·
            refine ⟨26367829460454246565855301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17578552973636164377236867 26367829460454246565855301)
            ·
              refine ⟨4943968023835171231097869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26367829460454246565855301 4943968023835171231097869)
              ·
                refine ⟨1853988008938189211661701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4943968023835171231097869 1853988008938189211661701)
                ·
                  refine ⟨347622751675910477186569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1853988008938189211661701 347622751675910477186569)
                  ·
                    rfl

theorem cell21_1523234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_1523234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1523234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1523234 prefixEnd_1523234 := by exact prefixLift 1523234
  have htrace : WordTrace (prefixWord ++ tailWord_1523234) baseStart_1523234 baseEnd_1523234 := by
    simpa [prefixWord, tailWord_1523234, baseEnd_1523234] using wordTrace_append hprefix tailTrace_1523234
  have hstable : (prefixWord ++ tailWord_1523234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523234).length < 2 ^ (prefixWord ++ tailWord_1523234).sum := by decide
  have hdescent : baseEnd_1523234 < baseStart_1523234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523254 : List Nat := [5, 1, 2, 1, 3, 1, 2, 3, 3]
def baseStart_1523254 : Nat := 118140960795 + 1523254 * 2 ^ 59
def prefixEnd_1523254 : Nat := 4983230072969 + 3 ^ 40 * 1523254 * 2
def baseEnd_1523254 : Nat := 347627315948394886853195

theorem tailTrace_1523254 : CollatzResearch.WordTrace tailWord_1523254 prefixEnd_1523254 347627315948394886853195 := by
  unfold tailWord_1523254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3472352351469898994789051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37038425082345589277749877 3472352351469898994789051)
  ·
    refine ⟨5208528527204848492183577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3472352351469898994789051 5208528527204848492183577)
    ·
      refine ⟨3906396395403636369137683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5208528527204848492183577 3906396395403636369137683)
      ·
        refine ⟨5859594593105454553706525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3906396395403636369137683 5859594593105454553706525)
        ·
          refine ⟨2197347972414545457639947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5859594593105454553706525 2197347972414545457639947)
          ·
            refine ⟨3296021958621818186459921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2197347972414545457639947 3296021958621818186459921)
            ·
              refine ⟨2472016468966363639844941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3296021958621818186459921 2472016468966363639844941)
              ·
                refine ⟨927006175862386364941853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2472016468966363639844941 927006175862386364941853)
                ·
                  refine ⟨347627315948394886853195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 927006175862386364941853 347627315948394886853195)
                  ·
                    rfl

theorem cell21_1523254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_1523254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1523254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1523254 prefixEnd_1523254 := by exact prefixLift 1523254
  have htrace : WordTrace (prefixWord ++ tailWord_1523254) baseStart_1523254 baseEnd_1523254 := by
    simpa [prefixWord, tailWord_1523254, baseEnd_1523254] using wordTrace_append hprefix tailTrace_1523254
  have hstable : (prefixWord ++ tailWord_1523254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523254).length < 2 ^ (prefixWord ++ tailWord_1523254).sum := by decide
  have hdescent : baseEnd_1523254 < baseStart_1523254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523383 : List Nat := [1, 1, 3, 1, 5, 10]
def baseStart_1523383 : Nat := 118140960795 + 1523383 * 2 ^ 59
def prefixEnd_1523383 : Nat := 4983230072969 + 3 ^ 40 * 1523383 * 2
def baseEnd_1523383 : Nat := 12876176129848864044553

theorem tailTrace_1523383 : CollatzResearch.WordTrace tailWord_1523383 prefixEnd_1523383 12876176129848864044553 := by
  unfold tailWord_1523383
  simp only [CollatzResearch.WordTrace]
  refine ⟨55562342640051038948070803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37041561760034025965380535 55562342640051038948070803)
  ·
    refine ⟨83343513960076558422106205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55562342640051038948070803 83343513960076558422106205)
    ·
      refine ⟨31253817735028709408289827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83343513960076558422106205 31253817735028709408289827)
      ·
        refine ⟨46880726602543064112434741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31253817735028709408289827 46880726602543064112434741)
        ·
          refine ⟨4395068118988412260540757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46880726602543064112434741 4395068118988412260540757)
          ·
            refine ⟨12876176129848864044553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4395068118988412260540757 12876176129848864044553)
            ·
              rfl

theorem cell21_1523383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 10].length) (baseStart_1523383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1523383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1523383 prefixEnd_1523383 := by exact prefixLift 1523383
  have htrace : WordTrace (prefixWord ++ tailWord_1523383) baseStart_1523383 baseEnd_1523383 := by
    simpa [prefixWord, tailWord_1523383, baseEnd_1523383] using wordTrace_append hprefix tailTrace_1523383
  have hstable : (prefixWord ++ tailWord_1523383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523383).length < 2 ^ (prefixWord ++ tailWord_1523383).sum := by decide
  have hdescent : baseEnd_1523383 < baseStart_1523383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523386 : List Nat := [3, 1, 1, 1, 2, 5, 2, 2, 4]
def baseStart_1523386 : Nat := 118140960795 + 1523386 * 2 ^ 59
def prefixEnd_1523386 : Nat := 4983230072969 + 3 ^ 40 * 1523386 * 2
def baseEnd_1523386 : Nat := 347657440146791990652925

theorem tailTrace_1523386 : CollatzResearch.WordTrace tailWord_1523386 prefixEnd_1523386 347657440146791990652925 := by
  unfold tailWord_1523386
  simp only [CollatzResearch.WordTrace]
  refine ⟨13890613014760042615107503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37041634706026780306953341 13890613014760042615107503)
  ·
    refine ⟨20835919522140063922661255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13890613014760042615107503 20835919522140063922661255)
    ·
      refine ⟨31253879283210095883991883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20835919522140063922661255 31253879283210095883991883)
      ·
        refine ⟨46880818924815143825987825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31253879283210095883991883 46880818924815143825987825)
        ·
          refine ⟨35160614193611357869490869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46880818924815143825987825 35160614193611357869490869)
          ·
            refine ⟨3296307580651064800264769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35160614193611357869490869 3296307580651064800264769)
            ·
              refine ⟨2472230685488298600198577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3296307580651064800264769 2472230685488298600198577)
              ·
                refine ⟨1854173014116223950148933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2472230685488298600198577 1854173014116223950148933)
                ·
                  refine ⟨347657440146791990652925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1854173014116223950148933 347657440146791990652925)
                  ·
                    rfl

theorem cell21_1523386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_1523386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1523386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1523386 prefixEnd_1523386 := by exact prefixLift 1523386
  have htrace : WordTrace (prefixWord ++ tailWord_1523386) baseStart_1523386 baseEnd_1523386 := by
    simpa [prefixWord, tailWord_1523386, baseEnd_1523386] using wordTrace_append hprefix tailTrace_1523386
  have hstable : (prefixWord ++ tailWord_1523386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523386).length < 2 ^ (prefixWord ++ tailWord_1523386).sum := by decide
  have hdescent : baseEnd_1523386 < baseStart_1523386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523513 : List Nat := [1, 2, 1, 7, 2, 1, 2, 1, 4]
def baseStart_1523513 : Nat := 118140960795 + 1523513 * 2 ^ 59
def prefixEnd_1523513 : Nat := 4983230072969 + 3 ^ 40 * 1523513 * 2
def baseEnd_1523513 : Nat := 347686423277067992035999

theorem tailTrace_1523513 : CollatzResearch.WordTrace tailWord_1523513 prefixEnd_1523513 347686423277067992035999 := by
  unfold tailWord_1523513
  simp only [CollatzResearch.WordTrace]
  refine ⟨55567084129580071150303193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37044722753053380766868795 55567084129580071150303193)
  ·
    refine ⟨41675313097185053362727395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55567084129580071150303193 41675313097185053362727395)
    ·
      refine ⟨62512969645777580044091093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41675313097185053362727395 62512969645777580044091093)
      ·
        refine ⟨1465147726072912032283385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 62512969645777580044091093 1465147726072912032283385)
        ·
          refine ⟨1098860794554684024212539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1465147726072912032283385 1098860794554684024212539)
          ·
            refine ⟨1648291191832026036318809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1098860794554684024212539 1648291191832026036318809)
            ·
              refine ⟨1236218393874019527239107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1648291191832026036318809 1236218393874019527239107)
              ·
                refine ⟨1854327590811029290858661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1236218393874019527239107 1854327590811029290858661)
                ·
                  refine ⟨347686423277067992035999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1854327590811029290858661 347686423277067992035999)
                  ·
                    rfl

theorem cell21_1523513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 4].length) (baseStart_1523513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1523513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1523513 prefixEnd_1523513 := by exact prefixLift 1523513
  have htrace : WordTrace (prefixWord ++ tailWord_1523513) baseStart_1523513 baseEnd_1523513 := by
    simpa [prefixWord, tailWord_1523513, baseEnd_1523513] using wordTrace_append hprefix tailTrace_1523513
  have hstable : (prefixWord ++ tailWord_1523513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523513).length < 2 ^ (prefixWord ++ tailWord_1523513).sum := by decide
  have hdescent : baseEnd_1523513 < baseStart_1523513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523580 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 10]
def baseStart_1523580 : Nat := 118140960795 + 1523580 * 2 ^ 59
def prefixEnd_1523580 : Nat := 4983230072969 + 3 ^ 40 * 1523580 * 2
def baseEnd_1523580 : Nat := 347701713589890764419195

theorem tailTrace_1523580 : CollatzResearch.WordTrace tailWord_1523580 prefixEnd_1523580 347701713589890764419195 := by
  unfold tailWord_1523580
  simp only [CollatzResearch.WordTrace]
  refine ⟨27784763910168670796496097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37046351880224894395328129 27784763910168670796496097)
  ·
    refine ⟨20838572932626503097372073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27784763910168670796496097 20838572932626503097372073)
    ·
      refine ⟨15628929699469877323029055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20838572932626503097372073 15628929699469877323029055)
      ·
        refine ⟨23443394549204815984543583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15628929699469877323029055 23443394549204815984543583)
        ·
          refine ⟨35165091823807223976815375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23443394549204815984543583 35165091823807223976815375)
          ·
            refine ⟨52747637735710835965223063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35165091823807223976815375 52747637735710835965223063)
            ·
              refine ⟨79121456603566253947834595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52747637735710835965223063 79121456603566253947834595)
              ·
                refine ⟨118682184905349380921751893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79121456603566253947834595 118682184905349380921751893)
                ·
                  refine ⟨347701713589890764419195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 118682184905349380921751893 347701713589890764419195)
                  ·
                    rfl

theorem cell21_1523580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_1523580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1523580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1523580 prefixEnd_1523580 := by exact prefixLift 1523580
  have htrace : WordTrace (prefixWord ++ tailWord_1523580) baseStart_1523580 baseEnd_1523580 := by
    simpa [prefixWord, tailWord_1523580, baseEnd_1523580] using wordTrace_append hprefix tailTrace_1523580
  have hstable : (prefixWord ++ tailWord_1523580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523580).length < 2 ^ (prefixWord ++ tailWord_1523580).sum := by decide
  have hdescent : baseEnd_1523580 < baseStart_1523580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523606 : List Nat := [5, 3, 1, 1, 3, 1, 1, 2, 4]
def baseStart_1523606 : Nat := 118140960795 + 1523606 * 2 ^ 59
def prefixEnd_1523606 : Nat := 4983230072969 + 3 ^ 40 * 1523606 * 2
def baseEnd_1523606 : Nat := 347707647144120496985809

theorem tailTrace_1523606 : CollatzResearch.WordTrace tailWord_1523606 prefixEnd_1523606 347707647144120496985809 := by
  unfold tailWord_1523606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3473154757390196752089917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37046984078828765355625781 3473154757390196752089917)
  ·
    refine ⟨1302433034021323782033719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3473154757390196752089917 1302433034021323782033719)
    ·
      refine ⟨1953649551031985673050579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1302433034021323782033719 1953649551031985673050579)
      ·
        refine ⟨2930474326547978509575869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1953649551031985673050579 2930474326547978509575869)
        ·
          refine ⟨1098927872455491941090951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2930474326547978509575869 1098927872455491941090951)
          ·
            refine ⟨1648391808683237911636427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1098927872455491941090951 1648391808683237911636427)
            ·
              refine ⟨2472587713024856867454641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1648391808683237911636427 2472587713024856867454641)
              ·
                refine ⟨1854440784768642650590981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2472587713024856867454641 1854440784768642650590981)
                ·
                  refine ⟨347707647144120496985809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1854440784768642650590981 347707647144120496985809)
                  ·
                    rfl

theorem cell21_1523606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_1523606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1523606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1523606 prefixEnd_1523606 := by exact prefixLift 1523606
  have htrace : WordTrace (prefixWord ++ tailWord_1523606) baseStart_1523606 baseEnd_1523606 := by
    simpa [prefixWord, tailWord_1523606, baseEnd_1523606] using wordTrace_append hprefix tailTrace_1523606
  have hstable : (prefixWord ++ tailWord_1523606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523606).length < 2 ^ (prefixWord ++ tailWord_1523606).sum := by decide
  have hdescent : baseEnd_1523606 < baseStart_1523606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523645 : List Nat := [1, 4, 1, 2, 3, 3, 2, 5]
def baseStart_1523645 : Nat := 118140960795 + 1523645 * 2 ^ 59
def prefixEnd_1523645 : Nat := 4983230072969 + 3 ^ 40 * 1523645 * 2
def baseEnd_1523645 : Nat := 115905515825155031945243

theorem tailTrace_1523645 : CollatzResearch.WordTrace tailWord_1523645 prefixEnd_1523645 115905515825155031945243 := by
  unfold tailWord_1523645
  simp only [CollatzResearch.WordTrace]
  refine ⟨55571898565101857694108389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37047932376734571796072259 55571898565101857694108389)
  ·
    refine ⟨10419730980956598317645323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55571898565101857694108389 10419730980956598317645323)
    ·
      refine ⟨15629596471434897476467985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10419730980956598317645323 15629596471434897476467985)
      ·
        refine ⟨11722197353576173107350989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15629596471434897476467985 11722197353576173107350989)
        ·
          refine ⟨4395824007591064915256621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11722197353576173107350989 4395824007591064915256621)
          ·
            refine ⟨1648434002846649343221233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4395824007591064915256621 1648434002846649343221233)
            ·
              refine ⟨1236325502134987007415925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1648434002846649343221233 1236325502134987007415925)
              ·
                refine ⟨115905515825155031945243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1236325502134987007415925 115905515825155031945243)
                ·
                  rfl

theorem cell21_1523645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 5].length) (baseStart_1523645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1523645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1523645 prefixEnd_1523645 := by exact prefixLift 1523645
  have htrace : WordTrace (prefixWord ++ tailWord_1523645) baseStart_1523645 baseEnd_1523645 := by
    simpa [prefixWord, tailWord_1523645, baseEnd_1523645] using wordTrace_append hprefix tailTrace_1523645
  have hstable : (prefixWord ++ tailWord_1523645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523645).length < 2 ^ (prefixWord ++ tailWord_1523645).sum := by decide
  have hdescent : baseEnd_1523645 < baseStart_1523645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523749 : List Nat := [1, 3, 1, 2, 2, 3, 2, 3, 4]
def baseStart_1523749 : Nat := 118140960795 + 1523749 * 2 ^ 59
def prefixEnd_1523749 : Nat := 4983230072969 + 3 ^ 40 * 1523749 * 2
def baseEnd_1523749 : Nat := 347740281692384026102183

theorem tailTrace_1523749 : CollatzResearch.WordTrace tailWord_1523749 prefixEnd_1523749 347740281692384026102183 := by
  unfold tailWord_1523749
  simp only [CollatzResearch.WordTrace]
  refine ⟨55575691756725083455894301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37050461171150055637262867 55575691756725083455894301)
  ·
    refine ⟨20840884408771906295960363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55575691756725083455894301 20840884408771906295960363)
    ·
      refine ⟨31261326613157859443940545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20840884408771906295960363 31261326613157859443940545)
      ·
        refine ⟨23445994959868394582955409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31261326613157859443940545 23445994959868394582955409)
        ·
          refine ⟨17584496219901295937216557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23445994959868394582955409 17584496219901295937216557)
          ·
            refine ⟨6594186082462985976456209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17584496219901295937216557 6594186082462985976456209)
            ·
              refine ⟨4945639561847239482342157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6594186082462985976456209 4945639561847239482342157)
              ·
                refine ⟨1854614835692714805878309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4945639561847239482342157 1854614835692714805878309)
                ·
                  refine ⟨347740281692384026102183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1854614835692714805878309 347740281692384026102183)
                  ·
                    rfl

theorem cell21_1523749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_1523749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1523749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1523749 prefixEnd_1523749 := by exact prefixLift 1523749
  have htrace : WordTrace (prefixWord ++ tailWord_1523749) baseStart_1523749 baseEnd_1523749 := by
    simpa [prefixWord, tailWord_1523749, baseEnd_1523749] using wordTrace_append hprefix tailTrace_1523749
  have hstable : (prefixWord ++ tailWord_1523749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523749).length < 2 ^ (prefixWord ++ tailWord_1523749).sum := by decide
  have hdescent : baseEnd_1523749 < baseStart_1523749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523752 : List Nat := [2, 1, 5, 3, 1, 1, 1, 2, 5]
def baseStart_1523752 : Nat := 118140960795 + 1523752 * 2 ^ 59
def prefixEnd_1523752 : Nat := 4983230072969 + 3 ^ 40 * 1523752 * 2
def baseEnd_1523752 : Nat := 347740966333256687552177

theorem tailTrace_1523752 : CollatzResearch.WordTrace tailWord_1523752 prefixEnd_1523752 347740966333256687552177 := by
  unfold tailWord_1523752
  simp only [CollatzResearch.WordTrace]
  refine ⟨27787900587857107484126755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37050534117142809978835673 27787900587857107484126755)
  ·
    refine ⟨41681850881785661226190133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27787900587857107484126755 41681850881785661226190133)
    ·
      refine ⟨3907673520167405739955325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41681850881785661226190133 3907673520167405739955325)
      ·
        refine ⟨1465377570062777152483247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3907673520167405739955325 1465377570062777152483247)
        ·
          refine ⟨2198066355094165728724871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1465377570062777152483247 2198066355094165728724871)
          ·
            refine ⟨3297099532641248593087307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2198066355094165728724871 3297099532641248593087307)
            ·
              refine ⟨4945649298961872889630961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3297099532641248593087307 4945649298961872889630961)
              ·
                refine ⟨3709236974221404667223221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4945649298961872889630961 3709236974221404667223221)
                ·
                  refine ⟨347740966333256687552177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3709236974221404667223221 347740966333256687552177)
                  ·
                    rfl

theorem cell21_1523752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 5].length) (baseStart_1523752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1523752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1523752 prefixEnd_1523752 := by exact prefixLift 1523752
  have htrace : WordTrace (prefixWord ++ tailWord_1523752) baseStart_1523752 baseEnd_1523752 := by
    simpa [prefixWord, tailWord_1523752, baseEnd_1523752] using wordTrace_append hprefix tailTrace_1523752
  have hstable : (prefixWord ++ tailWord_1523752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523752).length < 2 ^ (prefixWord ++ tailWord_1523752).sum := by decide
  have hdescent : baseEnd_1523752 < baseStart_1523752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523904 : List Nat := [2, 1, 1, 2, 5, 1, 4, 2, 3]
def baseStart_1523904 : Nat := 118140960795 + 1523904 * 2 ^ 59
def prefixEnd_1523904 : Nat := 4983230072969 + 3 ^ 40 * 1523904 * 2
def baseEnd_1523904 : Nat := 347775654804138201018533

theorem tailTrace_1523904 : CollatzResearch.WordTrace tailWord_1523904 prefixEnd_1523904 347775654804138201018533 := by
  unfold tailWord_1523904
  simp only [CollatzResearch.WordTrace]
  refine ⟨27790672535581772463893383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37054230047442363285191177 27790672535581772463893383)
  ·
    refine ⟨41686008803372658695840075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27790672535581772463893383 41686008803372658695840075)
    ·
      refine ⟨62529013205058988043760113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41686008803372658695840075 62529013205058988043760113)
      ·
        refine ⟨46896759903794241032820085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62529013205058988043760113 46896759903794241032820085)
        ·
          refine ⟨4396571240980710096826883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46896759903794241032820085 4396571240980710096826883)
          ·
            refine ⟨6594856861471065145240325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4396571240980710096826883 6594856861471065145240325)
            ·
              refine ⟨1236535661525824714732561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6594856861471065145240325 1236535661525824714732561)
              ·
                refine ⟨927401746144368536049421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1236535661525824714732561 927401746144368536049421)
                ·
                  refine ⟨347775654804138201018533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 927401746144368536049421 347775654804138201018533)
                  ·
                    rfl

theorem cell21_1523904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2, 3].length) (baseStart_1523904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1523904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1523904 prefixEnd_1523904 := by exact prefixLift 1523904
  have htrace : WordTrace (prefixWord ++ tailWord_1523904) baseStart_1523904 baseEnd_1523904 := by
    simpa [prefixWord, tailWord_1523904, baseEnd_1523904] using wordTrace_append hprefix tailTrace_1523904
  have hstable : (prefixWord ++ tailWord_1523904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523904).length < 2 ^ (prefixWord ++ tailWord_1523904).sum := by decide
  have hdescent : baseEnd_1523904 < baseStart_1523904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523929 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 7]
def baseStart_1523929 : Nat := 118140960795 + 1523929 * 2 ^ 59
def prefixEnd_1523929 : Nat := 4983230072969 + 3 ^ 40 * 1523929 * 2
def baseEnd_1523929 : Nat := 347781360144743713101815

theorem tailTrace_1523929 : CollatzResearch.WordTrace tailWord_1523929 prefixEnd_1523929 347781360144743713101815 := by
  unfold tailWord_1523929
  simp only [CollatzResearch.WordTrace]
  refine ⟨55582256896072974197446841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37054837930715316131631227 55582256896072974197446841)
  ·
    refine ⟨41686692672054730648085131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55582256896072974197446841 41686692672054730648085131)
    ·
      refine ⟨62530039008082095972127697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41686692672054730648085131 62530039008082095972127697)
      ·
        refine ⟨46897529256061571979095773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62530039008082095972127697 46897529256061571979095773)
        ·
          refine ⟨17586573471023089492160915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46897529256061571979095773 17586573471023089492160915)
          ·
            refine ⟨26379860206534634238241373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17586573471023089492160915 26379860206534634238241373)
            ·
              refine ⟨9892447577450487839340515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26379860206534634238241373 9892447577450487839340515)
              ·
                refine ⟨14838671366175731759010773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9892447577450487839340515 14838671366175731759010773)
                ·
                  refine ⟨347781360144743713101815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14838671366175731759010773 347781360144743713101815)
                  ·
                    rfl

theorem cell21_1523929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 7].length) (baseStart_1523929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1523929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1523929 prefixEnd_1523929 := by exact prefixLift 1523929
  have htrace : WordTrace (prefixWord ++ tailWord_1523929) baseStart_1523929 baseEnd_1523929 := by
    simpa [prefixWord, tailWord_1523929, baseEnd_1523929] using wordTrace_append hprefix tailTrace_1523929
  have hstable : (prefixWord ++ tailWord_1523929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523929).length < 2 ^ (prefixWord ++ tailWord_1523929).sum := by decide
  have hdescent : baseEnd_1523929 < baseStart_1523929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523991 : List Nat := [1, 1, 3, 4, 1, 3, 1, 7]
def baseStart_1523991 : Nat := 118140960795 + 1523991 * 2 ^ 59
def prefixEnd_1523991 : Nat := 4983230072969 + 3 ^ 40 * 1523991 * 2
def baseEnd_1523991 : Nat := 115931836463148461022785

theorem tailTrace_1523991 : CollatzResearch.WordTrace tailWord_1523991 prefixEnd_1523991 115931836463148461022785 := by
  unfold tailWord_1523991
  simp only [CollatzResearch.WordTrace]
  refine ⟨55584518221848358786203827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37056345481232239190802551 55584518221848358786203827)
  ·
    refine ⟨83376777332772538179305741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55584518221848358786203827 83376777332772538179305741)
    ·
      refine ⟨31266291499789701817239653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83376777332772538179305741 31266291499789701817239653)
      ·
        refine ⟨5862429656210569090732435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31266291499789701817239653 5862429656210569090732435)
        ·
          refine ⟨8793644484315853636098653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5862429656210569090732435 8793644484315853636098653)
          ·
            refine ⟨3297616681618445113536995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8793644484315853636098653 3297616681618445113536995)
            ·
              refine ⟨4946425022427667670305493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3297616681618445113536995 4946425022427667670305493)
              ·
                refine ⟨115931836463148461022785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4946425022427667670305493 115931836463148461022785)
                ·
                  rfl

theorem cell21_1523991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 7].length) (baseStart_1523991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1523991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1523991 prefixEnd_1523991 := by exact prefixLift 1523991
  have htrace : WordTrace (prefixWord ++ tailWord_1523991) baseStart_1523991 baseEnd_1523991 := by
    simpa [prefixWord, tailWord_1523991, baseEnd_1523991] using wordTrace_append hprefix tailTrace_1523991
  have hstable : (prefixWord ++ tailWord_1523991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523991).length < 2 ^ (prefixWord ++ tailWord_1523991).sum := by decide
  have hdescent : baseEnd_1523991 < baseStart_1523991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523997 : List Nat := [1, 4, 2, 3, 2, 2, 1, 3, 3]
def baseStart_1523997 : Nat := 118140960795 + 1523997 * 2 ^ 59
def prefixEnd_1523997 : Nat := 4983230072969 + 3 ^ 40 * 1523997 * 2
def baseEnd_1523997 : Nat := 347796878671190705968343

theorem tailTrace_1523997 : CollatzResearch.WordTrace tailWord_1523997 prefixEnd_1523997 347796878671190705968343 := by
  unfold tailWord_1523997
  simp only [CollatzResearch.WordTrace]
  refine ⟨55584737059826621810922245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37056491373217747873948163 55584737059826621810922245)
  ·
    refine ⟨10422138198717491589547921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55584737059826621810922245 10422138198717491589547921)
    ·
      refine ⟨7816603649038118692160941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10422138198717491589547921 7816603649038118692160941)
      ·
        refine ⟨2931226368389294509560353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7816603649038118692160941 2931226368389294509560353)
        ·
          refine ⟨2198419776291970882170265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2931226368389294509560353 2198419776291970882170265)
          ·
            refine ⟨1648814832218978161627699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2198419776291970882170265 1648814832218978161627699)
            ·
              refine ⟨2473222248328467242441549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1648814832218978161627699 2473222248328467242441549)
              ·
                refine ⟨927458343123175215915581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2473222248328467242441549 927458343123175215915581)
                ·
                  refine ⟨347796878671190705968343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 927458343123175215915581 347796878671190705968343)
                  ·
                    rfl

theorem cell21_1523997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_1523997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1523997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1523997 prefixEnd_1523997 := by exact prefixLift 1523997
  have htrace : WordTrace (prefixWord ++ tailWord_1523997) baseStart_1523997 baseEnd_1523997 := by
    simpa [prefixWord, tailWord_1523997, baseEnd_1523997] using wordTrace_append hprefix tailTrace_1523997
  have hstable : (prefixWord ++ tailWord_1523997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523997).length < 2 ^ (prefixWord ++ tailWord_1523997).sum := by decide
  have hdescent : baseEnd_1523997 < baseStart_1523997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524008 : List Nat := [2, 1, 5, 1, 3, 2, 7]
def baseStart_1524008 : Nat := 118140960795 + 1524008 * 2 ^ 59
def prefixEnd_1524008 : Nat := 4983230072969 + 3 ^ 40 * 1524008 * 2
def baseEnd_1524008 : Nat := 38644376557895236809443

theorem tailTrace_1524008 : CollatzResearch.WordTrace tailWord_1524008 prefixEnd_1524008 38644376557895236809443 := by
  unfold tailWord_1524008
  simp only [CollatzResearch.WordTrace]
  refine ⟨27792569131393385344786339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37056758841857847126381785 27792569131393385344786339)
  ·
    refine ⟨41688853697090078017179509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27792569131393385344786339 41688853697090078017179509)
    ·
      refine ⟨3908330034102194814110579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41688853697090078017179509 3908330034102194814110579)
      ·
        refine ⟨5862495051153292221165869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3908330034102194814110579 5862495051153292221165869)
        ·
          refine ⟨2198435644182484582937201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5862495051153292221165869 2198435644182484582937201)
          ·
            refine ⟨1648826733136863437202901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2198435644182484582937201 1648826733136863437202901)
            ·
              refine ⟨38644376557895236809443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1648826733136863437202901 38644376557895236809443)
              ·
                rfl

theorem cell21_1524008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 7].length) (baseStart_1524008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1524008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1524008 prefixEnd_1524008 := by exact prefixLift 1524008
  have htrace : WordTrace (prefixWord ++ tailWord_1524008) baseStart_1524008 baseEnd_1524008 := by
    simpa [prefixWord, tailWord_1524008, baseEnd_1524008] using wordTrace_append hprefix tailTrace_1524008
  have hstable : (prefixWord ++ tailWord_1524008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524008).length < 2 ^ (prefixWord ++ tailWord_1524008).sum := by decide
  have hdescent : baseEnd_1524008 < baseStart_1524008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524014 : List Nat := [4, 1, 3, 3, 1, 1, 3, 2, 3]
def baseStart_1524014 : Nat := 118140960795 + 1524014 * 2 ^ 59
def prefixEnd_1524014 : Nat := 4983230072969 + 3 ^ 40 * 1524014 * 2
def baseEnd_1524014 : Nat := 347800758302802454184975

theorem tailTrace_1524014 : CollatzResearch.WordTrace tailWord_1524014 prefixEnd_1524014 347800758302802454184975 := by
  unfold tailWord_1524014
  simp only [CollatzResearch.WordTrace]
  refine ⟨6948169637595629214286387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37056904733843355809527397 6948169637595629214286387)
  ·
    refine ⟨10422254456393443821429581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6948169637595629214286387 10422254456393443821429581)
    ·
      refine ⟨3908345421147541433036093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10422254456393443821429581 3908345421147541433036093)
      ·
        refine ⟨1465629532930328037388535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3908345421147541433036093 1465629532930328037388535)
        ·
          refine ⟨2198444299395492056082803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1465629532930328037388535 2198444299395492056082803)
          ·
            refine ⟨3297666449093238084124205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2198444299395492056082803 3297666449093238084124205)
            ·
              refine ⟨1236624918409964281546577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3297666449093238084124205 1236624918409964281546577)
              ·
                refine ⟨927468688807473211159933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1236624918409964281546577 927468688807473211159933)
                ·
                  refine ⟨347800758302802454184975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 927468688807473211159933 347800758302802454184975)
                  ·
                    rfl

theorem cell21_1524014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_1524014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1524014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1524014 prefixEnd_1524014 := by exact prefixLift 1524014
  have htrace : WordTrace (prefixWord ++ tailWord_1524014) baseStart_1524014 baseEnd_1524014 := by
    simpa [prefixWord, tailWord_1524014, baseEnd_1524014] using wordTrace_append hprefix tailTrace_1524014
  have hstable : (prefixWord ++ tailWord_1524014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524014).length < 2 ^ (prefixWord ++ tailWord_1524014).sum := by decide
  have hdescent : baseEnd_1524014 < baseStart_1524014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524081 : List Nat := [1, 2, 2, 2, 1, 2, 1, 5, 5]
def baseStart_1524081 : Nat := 118140960795 + 1524081 * 2 ^ 59
def prefixEnd_1524081 : Nat := 4983230072969 + 3 ^ 40 * 1524081 * 2
def baseEnd_1524081 : Nat := 347816048615625226568171

theorem tailTrace_1524081 : CollatzResearch.WordTrace tailWord_1524081 prefixEnd_1524081 347816048615625226568171 := by
  unfold tailWord_1524081
  simp only [CollatzResearch.WordTrace]
  refine ⟨55587800791522304156980097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37058533861014869437986731 55587800791522304156980097)
  ·
    refine ⟨41690850593641728117735073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55587800791522304156980097 41690850593641728117735073)
    ·
      refine ⟨31268137945231296088301305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41690850593641728117735073 31268137945231296088301305)
      ·
        refine ⟨23451103458923472066225979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31268137945231296088301305 23451103458923472066225979)
        ·
          refine ⟨35176655188385208099338969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23451103458923472066225979 35176655188385208099338969)
          ·
            refine ⟨26382491391288906074504227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35176655188385208099338969 26382491391288906074504227)
            ·
              refine ⟨39573737086933359111756341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26382491391288906074504227 39573737086933359111756341)
              ·
                refine ⟨3710037851900002416727157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39573737086933359111756341 3710037851900002416727157)
                ·
                  refine ⟨347816048615625226568171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3710037851900002416727157 347816048615625226568171)
                  ·
                    rfl

theorem cell21_1524081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 5].length) (baseStart_1524081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1524081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1524081 prefixEnd_1524081 := by exact prefixLift 1524081
  have htrace : WordTrace (prefixWord ++ tailWord_1524081) baseStart_1524081 baseEnd_1524081 := by
    simpa [prefixWord, tailWord_1524081, baseEnd_1524081] using wordTrace_append hprefix tailTrace_1524081
  have hstable : (prefixWord ++ tailWord_1524081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524081).length < 2 ^ (prefixWord ++ tailWord_1524081).sum := by decide
  have hdescent : baseEnd_1524081 < baseStart_1524081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524118 : List Nat := [5, 3, 1, 2, 1, 1, 8]
def baseStart_1524118 : Nat := 118140960795 + 1524118 * 2 ^ 59
def prefixEnd_1524118 : Nat := 4983230072969 + 3 ^ 40 * 1524118 * 2
def baseEnd_1524118 : Nat := 38647165835524598272381

theorem tailTrace_1524118 : CollatzResearch.WordTrace tailWord_1524118 prefixEnd_1524118 38647165835524598272381 := by
  unfold tailWord_1524118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3474321893274266217254813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37059433528258839650718005 3474321893274266217254813)
  ·
    refine ⟨1302870709977849831470555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3474321893274266217254813 1302870709977849831470555)
    ·
      refine ⟨1954306064966774747205833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1302870709977849831470555 1954306064966774747205833)
      ·
        refine ⟨1465729548725081060404375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1954306064966774747205833 1465729548725081060404375)
        ·
          refine ⟨2198594323087621590606563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1465729548725081060404375 2198594323087621590606563)
          ·
            refine ⟨3297891484631432385909845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2198594323087621590606563 3297891484631432385909845)
            ·
              refine ⟨38647165835524598272381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3297891484631432385909845 38647165835524598272381)
              ·
                rfl

theorem cell21_1524118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 8].length) (baseStart_1524118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1524118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1524118 prefixEnd_1524118 := by exact prefixLift 1524118
  have htrace : WordTrace (prefixWord ++ tailWord_1524118) baseStart_1524118 baseEnd_1524118 := by
    simpa [prefixWord, tailWord_1524118, baseEnd_1524118] using wordTrace_append hprefix tailTrace_1524118
  have hstable : (prefixWord ++ tailWord_1524118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524118).length < 2 ^ (prefixWord ++ tailWord_1524118).sum := by decide
  have hdescent : baseEnd_1524118 < baseStart_1524118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524309 : List Nat := [1, 3, 2, 2, 1, 1, 3, 3, 5]
def baseStart_1524309 : Nat := 118140960795 + 1524309 * 2 ^ 59
def prefixEnd_1524309 : Nat := 4983230072969 + 3 ^ 40 * 1524309 * 2
def baseEnd_1524309 : Nat := 347868081321947496767705

theorem tailTrace_1524309 : CollatzResearch.WordTrace tailWord_1524309 prefixEnd_1524309 347868081321947496767705 := by
  unfold tailWord_1524309
  simp only [CollatzResearch.WordTrace]
  refine ⟨55596116634696299096279981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37064077756464199397519987 55596116634696299096279981)
  ·
    refine ⟨20848543738011112161104993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55596116634696299096279981 20848543738011112161104993)
    ·
      refine ⟨15636407803508334120828745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20848543738011112161104993 15636407803508334120828745)
      ·
        refine ⟨11727305852631250590621559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15636407803508334120828745 11727305852631250590621559)
        ·
          refine ⟨17590958778946875885932339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11727305852631250590621559 17590958778946875885932339)
          ·
            refine ⟨26386438168420313828898509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17590958778946875885932339 26386438168420313828898509)
            ·
              refine ⟨9894914313157617685836941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26386438168420313828898509 9894914313157617685836941)
              ·
                refine ⟨3710592867434106632188853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9894914313157617685836941 3710592867434106632188853)
                ·
                  refine ⟨347868081321947496767705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3710592867434106632188853 347868081321947496767705)
                  ·
                    rfl

theorem cell21_1524309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_1524309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1524309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1524309 prefixEnd_1524309 := by exact prefixLift 1524309
  have htrace : WordTrace (prefixWord ++ tailWord_1524309) baseStart_1524309 baseEnd_1524309 := by
    simpa [prefixWord, tailWord_1524309, baseEnd_1524309] using wordTrace_append hprefix tailTrace_1524309
  have hstable : (prefixWord ++ tailWord_1524309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524309).length < 2 ^ (prefixWord ++ tailWord_1524309).sum := by decide
  have hdescent : baseEnd_1524309 < baseStart_1524309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524402 : List Nat := [3, 2, 1, 1, 1, 2, 1, 7, 3]
def baseStart_1524402 : Nat := 118140960795 + 1524402 * 2 ^ 59
def prefixEnd_1524402 : Nat := 4983230072969 + 3 ^ 40 * 1524402 * 2
def baseEnd_1524402 : Nat := 347889305189000001717515

theorem tailTrace_1524402 : CollatzResearch.WordTrace tailWord_1524402 prefixEnd_1524402 347889305189000001717515 := by
  unfold tailWord_1524402
  simp only [CollatzResearch.WordTrace]
  refine ⟨13899877155839843994853865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37066339082239583986276973 13899877155839843994853865)
  ·
    refine ⟨10424907866879882996140399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13899877155839843994853865 10424907866879882996140399)
    ·
      refine ⟨15637361800319824494210599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10424907866879882996140399 15637361800319824494210599)
      ·
        refine ⟨23456042700479736741315899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15637361800319824494210599 23456042700479736741315899)
        ·
          refine ⟨35184064050719605111973849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23456042700479736741315899 35184064050719605111973849)
          ·
            refine ⟨26388048038039703833980387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35184064050719605111973849 26388048038039703833980387)
            ·
              refine ⟨39582072057059555750970581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26388048038039703833980387 39582072057059555750970581)
              ·
                refine ⟨927704813837333337913373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 39582072057059555750970581 927704813837333337913373)
                ·
                  refine ⟨347889305189000001717515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 927704813837333337913373 347889305189000001717515)
                  ·
                    rfl

theorem cell21_1524402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_1524402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1524402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1524402 prefixEnd_1524402 := by exact prefixLift 1524402
  have htrace : WordTrace (prefixWord ++ tailWord_1524402) baseStart_1524402 baseEnd_1524402 := by
    simpa [prefixWord, tailWord_1524402, baseEnd_1524402] using wordTrace_append hprefix tailTrace_1524402
  have hstable : (prefixWord ++ tailWord_1524402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524402).length < 2 ^ (prefixWord ++ tailWord_1524402).sum := by decide
  have hdescent : baseEnd_1524402 < baseStart_1524402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524416 : List Nat := [2, 1, 1, 2, 4, 2, 1, 4, 4]
def baseStart_1524416 : Nat := 118140960795 + 1524416 * 2 ^ 59
def prefixEnd_1524416 : Nat := 4983230072969 + 3 ^ 40 * 1524416 * 2
def baseEnd_1524416 : Nat := 347892500179739088484153

theorem tailTrace_1524416 : CollatzResearch.WordTrace tailWord_1524416 prefixEnd_1524416 347892500179739088484153 := by
  unfold tailWord_1524416
  simp only [CollatzResearch.WordTrace]
  refine ⟨27800009622654328185212551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37066679496872437580283401 27800009622654328185212551)
  ·
    refine ⟨41700014433981492277818827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27800009622654328185212551 41700014433981492277818827)
    ·
      refine ⟨62550021650972238416728241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41700014433981492277818827 62550021650972238416728241)
      ·
        refine ⟨46912516238229178812546181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62550021650972238416728241 46912516238229178812546181)
        ·
          refine ⟨8796096794667971027352409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46912516238229178812546181 8796096794667971027352409)
          ·
            refine ⟨6597072596000978270514307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8796096794667971027352409 6597072596000978270514307)
            ·
              refine ⟨9895608894001467405771461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6597072596000978270514307 9895608894001467405771461)
              ·
                refine ⟨1855426667625275138582149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9895608894001467405771461 1855426667625275138582149)
                ·
                  refine ⟨347892500179739088484153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1855426667625275138582149 347892500179739088484153)
                  ·
                    rfl

theorem cell21_1524416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 4].length) (baseStart_1524416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1524416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1524416 prefixEnd_1524416 := by exact prefixLift 1524416
  have htrace : WordTrace (prefixWord ++ tailWord_1524416) baseStart_1524416 baseEnd_1524416 := by
    simpa [prefixWord, tailWord_1524416, baseEnd_1524416] using wordTrace_append hprefix tailTrace_1524416
  have hstable : (prefixWord ++ tailWord_1524416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524416).length < 2 ^ (prefixWord ++ tailWord_1524416).sum := by decide
  have hdescent : baseEnd_1524416 < baseStart_1524416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524422 : List Nat := [6, 1, 2, 1, 2, 2, 1, 6]
def baseStart_1524422 : Nat := 118140960795 + 1524422 * 2 ^ 59
def prefixEnd_1524422 : Nat := 4983230072969 + 3 ^ 40 * 1524422 * 2
def baseEnd_1524422 : Nat := 115964623153828137128047

theorem tailTrace_1524422 : CollatzResearch.WordTrace tailWord_1524422 prefixEnd_1524422 115964623153828137128047 := by
  unfold tailWord_1524422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1737507440102716231098235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37066825388857946263429013 1737507440102716231098235)
  ·
    refine ⟨2606261160154074346647353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1737507440102716231098235 2606261160154074346647353)
    ·
      refine ⟨1954695870115555759985515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2606261160154074346647353 1954695870115555759985515)
      ·
        refine ⟨2932043805173333639978273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1954695870115555759985515 2932043805173333639978273)
        ·
          refine ⟨2199032853880000229983705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2932043805173333639978273 2199032853880000229983705)
          ·
            refine ⟨1649274640410000172487779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2199032853880000229983705 1649274640410000172487779)
            ·
              refine ⟨2473911960615000258731669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1649274640410000172487779 2473911960615000258731669)
              ·
                refine ⟨115964623153828137128047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2473911960615000258731669 115964623153828137128047)
                ·
                  rfl

theorem cell21_1524422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_1524422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1524422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1524422 prefixEnd_1524422 := by exact prefixLift 1524422
  have htrace : WordTrace (prefixWord ++ tailWord_1524422) baseStart_1524422 baseEnd_1524422 := by
    simpa [prefixWord, tailWord_1524422, baseEnd_1524422] using wordTrace_append hprefix tailTrace_1524422
  have hstable : (prefixWord ++ tailWord_1524422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524422).length < 2 ^ (prefixWord ++ tailWord_1524422).sum := by decide
  have hdescent : baseEnd_1524422 < baseStart_1524422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524447 : List Nat := [1, 1, 2, 3, 2, 4, 3, 5]
def baseStart_1524447 : Nat := 118140960795 + 1524447 * 2 ^ 59
def prefixEnd_1524447 : Nat := 4983230072969 + 3 ^ 40 * 1524447 * 2
def baseEnd_1524447 : Nat := 115966524934029974489141

theorem tailTrace_1524447 : CollatzResearch.WordTrace tailWord_1524447 prefixEnd_1524447 115966524934029974489141 := by
  unfold tailWord_1524447
  simp only [CollatzResearch.WordTrace]
  refine ⟨55601149908196348664803595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37067433272130899109869063 55601149908196348664803595)
  ·
    refine ⟨83401724862294522997205393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55601149908196348664803595 83401724862294522997205393)
    ·
      refine ⟨62551293646720892247904045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83401724862294522997205393 62551293646720892247904045)
      ·
        refine ⟨23456735117520334592964017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62551293646720892247904045 23456735117520334592964017)
        ·
          refine ⟨17592551338140250944723013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23456735117520334592964017 17592551338140250944723013)
          ·
            refine ⟨3298603375901297052135565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17592551338140250944723013 3298603375901297052135565)
            ·
              refine ⟨1236976265962986394550837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3298603375901297052135565 1236976265962986394550837)
              ·
                refine ⟨115966524934029974489141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1236976265962986394550837 115966524934029974489141)
                ·
                  rfl

theorem cell21_1524447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 5].length) (baseStart_1524447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1524447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1524447 prefixEnd_1524447 := by exact prefixLift 1524447
  have htrace : WordTrace (prefixWord ++ tailWord_1524447) baseStart_1524447 baseEnd_1524447 := by
    simpa [prefixWord, tailWord_1524447, baseEnd_1524447] using wordTrace_append hprefix tailTrace_1524447
  have hstable : (prefixWord ++ tailWord_1524447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524447).length < 2 ^ (prefixWord ++ tailWord_1524447).sum := by decide
  have hdescent : baseEnd_1524447 < baseStart_1524447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524461 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 7]
def baseStart_1524461 : Nat := 118140960795 + 1524461 * 2 ^ 59
def prefixEnd_1524461 : Nat := 4983230072969 + 3 ^ 40 * 1524461 * 2
def baseEnd_1524461 : Nat := 347902769792829010234061

theorem tailTrace_1524461 : CollatzResearch.WordTrace tailWord_1524461 prefixEnd_1524461 347902769792829010234061 := by
  unfold tailWord_1524461
  simp only [CollatzResearch.WordTrace]
  refine ⟨55601660530145629055813237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37067773686763752703875491 55601660530145629055813237)
  ·
    refine ⟨5212655674701152723982491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55601660530145629055813237 5212655674701152723982491)
    ·
      refine ⟨7818983512051729085973737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5212655674701152723982491 7818983512051729085973737)
      ·
        refine ⟨5864237634038796814480303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7818983512051729085973737 5864237634038796814480303)
        ·
          refine ⟨8796356451058195221720455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5864237634038796814480303 8796356451058195221720455)
          ·
            refine ⟨13194534676587292832580683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8796356451058195221720455 13194534676587292832580683)
            ·
              refine ⟨19791802014880939248871025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13194534676587292832580683 19791802014880939248871025)
              ·
                refine ⟨14843851511160704436653269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19791802014880939248871025 14843851511160704436653269)
                ·
                  refine ⟨347902769792829010234061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14843851511160704436653269 347902769792829010234061)
                  ·
                    rfl

theorem cell21_1524461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_1524461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1524461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1524461 prefixEnd_1524461 := by exact prefixLift 1524461
  have htrace : WordTrace (prefixWord ++ tailWord_1524461) baseStart_1524461 baseEnd_1524461 := by
    simpa [prefixWord, tailWord_1524461, baseEnd_1524461] using wordTrace_append hprefix tailTrace_1524461
  have hstable : (prefixWord ++ tailWord_1524461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524461).length < 2 ^ (prefixWord ++ tailWord_1524461).sum := by decide
  have hdescent : baseEnd_1524461 < baseStart_1524461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524478 : List Nat := [4, 2, 2, 1, 2, 1, 1, 3, 5]
def baseStart_1524478 : Nat := 118140960795 + 1524478 * 2 ^ 59
def prefixEnd_1524478 : Nat := 4983230072969 + 3 ^ 40 * 1524478 * 2
def baseEnd_1524478 : Nat := 347906649424440758450693

theorem tailTrace_1524478 : CollatzResearch.WordTrace tailWord_1524478 prefixEnd_1524478 347906649424440758450693 := by
  unfold tailWord_1524478
  simp only [CollatzResearch.WordTrace]
  refine ⟨6950285071385505119897761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37068187047389360639454725 6950285071385505119897761)
  ·
    refine ⟨5212713803539128839923321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6950285071385505119897761 5212713803539128839923321)
    ·
      refine ⟨3909535352654346629942491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5212713803539128839923321 3909535352654346629942491)
      ·
        refine ⟨5864303028981519944913737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3909535352654346629942491 5864303028981519944913737)
        ·
          refine ⟨4398227271736139958685303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5864303028981519944913737 4398227271736139958685303)
          ·
            refine ⟨6597340907604209938027955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4398227271736139958685303 6597340907604209938027955)
            ·
              refine ⟨9896011361406314907041933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6597340907604209938027955 9896011361406314907041933)
              ·
                refine ⟨3711004260527368090140725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9896011361406314907041933 3711004260527368090140725)
                ·
                  refine ⟨347906649424440758450693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3711004260527368090140725 347906649424440758450693)
                  ·
                    rfl

theorem cell21_1524478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_1524478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1524478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1524478 prefixEnd_1524478 := by exact prefixLift 1524478
  have htrace : WordTrace (prefixWord ++ tailWord_1524478) baseStart_1524478 baseEnd_1524478 := by
    simpa [prefixWord, tailWord_1524478, baseEnd_1524478] using wordTrace_append hprefix tailTrace_1524478
  have hstable : (prefixWord ++ tailWord_1524478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524478).length < 2 ^ (prefixWord ++ tailWord_1524478).sum := by decide
  have hdescent : baseEnd_1524478 < baseStart_1524478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524498 : List Nat := [3, 2, 4, 1, 3, 1, 2, 5]
def baseStart_1524498 : Nat := 118140960795 + 1524498 * 2 ^ 59
def prefixEnd_1524498 : Nat := 4983230072969 + 3 ^ 40 * 1524498 * 2
def baseEnd_1524498 : Nat := 115970404565641722705773

theorem tailTrace_1524498 : CollatzResearch.WordTrace tailWord_1524498 prefixEnd_1524498 115970404565641722705773 := by
  unfold tailWord_1524498
  simp only [CollatzResearch.WordTrace]
  refine ⟨13900752507752896093727537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37068673354007722916606765 13900752507752896093727537)
  ·
    refine ⟨10425564380814672070295653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13900752507752896093727537 10425564380814672070295653)
    ·
      refine ⟨1954793321402751013180435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10425564380814672070295653 1954793321402751013180435)
      ·
        refine ⟨2932189982104126519770653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1954793321402751013180435 2932189982104126519770653)
        ·
          refine ⟨1099571243289047444913995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2932189982104126519770653 1099571243289047444913995)
          ·
            refine ⟨1649356864933571167370993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1099571243289047444913995 1649356864933571167370993)
            ·
              refine ⟨1237017648700178375528245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1649356864933571167370993 1237017648700178375528245)
              ·
                refine ⟨115970404565641722705773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1237017648700178375528245 115970404565641722705773)
                ·
                  rfl

theorem cell21_1524498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 5].length) (baseStart_1524498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1524498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1524498 prefixEnd_1524498 := by exact prefixLift 1524498
  have htrace : WordTrace (prefixWord ++ tailWord_1524498) baseStart_1524498 baseEnd_1524498 := by
    simpa [prefixWord, tailWord_1524498, baseEnd_1524498] using wordTrace_append hprefix tailTrace_1524498
  have hstable : (prefixWord ++ tailWord_1524498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524498).length < 2 ^ (prefixWord ++ tailWord_1524498).sum := by decide
  have hdescent : baseEnd_1524498 < baseStart_1524498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524506 : List Nat := [3, 1, 1, 3, 2, 1, 3, 7]
def baseStart_1524506 : Nat := 118140960795 + 1524506 * 2 ^ 59
def prefixEnd_1524506 : Nat := 4983230072969 + 3 ^ 40 * 1524506 * 2
def baseEnd_1524506 : Nat := 115971013135306310661323

theorem tailTrace_1524506 : CollatzResearch.WordTrace tailWord_1524506 prefixEnd_1524506 115971013135306310661323 := by
  unfold tailWord_1524506
  simp only [CollatzResearch.WordTrace]
  refine ⟨13900825453745650435300343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37068867876655067827467581 13900825453745650435300343)
  ·
    refine ⟨20851238180618475652950515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13900825453745650435300343 20851238180618475652950515)
    ·
      refine ⟨31276857270927713479425773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20851238180618475652950515 31276857270927713479425773)
      ·
        refine ⟨11728821476597892554784665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31276857270927713479425773 11728821476597892554784665)
        ·
          refine ⟨8796616107448419416088499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11728821476597892554784665 8796616107448419416088499)
          ·
            refine ⟨13194924161172629124132749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8796616107448419416088499 13194924161172629124132749)
            ·
              refine ⟨4948096560439735921549781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13194924161172629124132749 4948096560439735921549781)
              ·
                refine ⟨115971013135306310661323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4948096560439735921549781 115971013135306310661323)
                ·
                  rfl

theorem cell21_1524506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_1524506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1524506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1524506 prefixEnd_1524506 := by exact prefixLift 1524506
  have htrace : WordTrace (prefixWord ++ tailWord_1524506) baseStart_1524506 baseEnd_1524506 := by
    simpa [prefixWord, tailWord_1524506, baseEnd_1524506] using wordTrace_append hprefix tailTrace_1524506
  have hstable : (prefixWord ++ tailWord_1524506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524506).length < 2 ^ (prefixWord ++ tailWord_1524506).sum := by decide
  have hdescent : baseEnd_1524506 < baseStart_1524506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524613 : List Nat := [1, 3, 1, 1, 3, 4, 1, 2, 5]
def baseStart_1524613 : Nat := 118140960795 + 1524613 * 2 ^ 59
def prefixEnd_1524613 : Nat := 4983230072969 + 3 ^ 40 * 1524613 * 2
def baseEnd_1524613 : Nat := 347937458263710523700417

theorem tailTrace_1524613 : CollatzResearch.WordTrace tailWord_1524613 prefixEnd_1524613 347937458263710523700417 := by
  unfold tailWord_1524613
  simp only [CollatzResearch.WordTrace]
  refine ⟨55607204425594959015346493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37071469617063306010230995 55607204425594959015346493)
  ·
    refine ⟨20852701659598109630754935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55607204425594959015346493 20852701659598109630754935)
    ·
      refine ⟨31279052489397164446132403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20852701659598109630754935 31279052489397164446132403)
      ·
        refine ⟨46918578734095746669198605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31279052489397164446132403 46918578734095746669198605)
        ·
          refine ⟨17594467025285905000949477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46918578734095746669198605 17594467025285905000949477)
          ·
            refine ⟨3298962567241107187678027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17594467025285905000949477 3298962567241107187678027)
            ·
              refine ⟨4948443850861660781517041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3298962567241107187678027 4948443850861660781517041)
              ·
                refine ⟨3711332888146245586137781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4948443850861660781517041 3711332888146245586137781)
                ·
                  refine ⟨347937458263710523700417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3711332888146245586137781 347937458263710523700417)
                  ·
                    rfl

theorem cell21_1524613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_1524613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1524613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1524613 prefixEnd_1524613 := by exact prefixLift 1524613
  have htrace : WordTrace (prefixWord ++ tailWord_1524613) baseStart_1524613 baseEnd_1524613 := by
    simpa [prefixWord, tailWord_1524613, baseEnd_1524613] using wordTrace_append hprefix tailTrace_1524613
  have hstable : (prefixWord ++ tailWord_1524613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524613).length < 2 ^ (prefixWord ++ tailWord_1524613).sum := by decide
  have hdescent : baseEnd_1524613 < baseStart_1524613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524661 : List Nat := [1, 3, 3, 2, 1, 1, 5, 1, 4]
def baseStart_1524661 : Nat := 118140960795 + 1524661 * 2 ^ 59
def prefixEnd_1524661 : Nat := 4983230072969 + 3 ^ 40 * 1524661 * 2
def baseEnd_1524661 : Nat := 347948412517673106900319

theorem tailTrace_1524661 : CollatzResearch.WordTrace tailWord_1524661 prefixEnd_1524661 347948412517673106900319 := by
  unfold tailWord_1524661
  simp only [CollatzResearch.WordTrace]
  refine ⟨55608955129421063213093837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37072636752947375475395891 55608955129421063213093837)
  ·
    refine ⟨20853358173532898704910189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55608955129421063213093837 20853358173532898704910189)
    ·
      refine ⟨7820009315074837014341321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20853358173532898704910189 7820009315074837014341321)
      ·
        refine ⟨5865006986306127760755991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7820009315074837014341321 5865006986306127760755991)
        ·
          refine ⟨8797510479459191641133987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5865006986306127760755991 8797510479459191641133987)
          ·
            refine ⟨13196265719188787461700981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8797510479459191641133987 13196265719188787461700981)
            ·
              refine ⟨1237149911173948824534467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13196265719188787461700981 1237149911173948824534467)
              ·
                refine ⟨1855724866760923236801701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1237149911173948824534467 1855724866760923236801701)
                ·
                  refine ⟨347948412517673106900319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1855724866760923236801701 347948412517673106900319)
                  ·
                    rfl

theorem cell21_1524661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_1524661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1524661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1524661 prefixEnd_1524661 := by exact prefixLift 1524661
  have htrace : WordTrace (prefixWord ++ tailWord_1524661) baseStart_1524661 baseEnd_1524661 := by
    simpa [prefixWord, tailWord_1524661, baseEnd_1524661] using wordTrace_append hprefix tailTrace_1524661
  have hstable : (prefixWord ++ tailWord_1524661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524661).length < 2 ^ (prefixWord ++ tailWord_1524661).sum := by decide
  have hdescent : baseEnd_1524661 < baseStart_1524661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524768 : List Nat := [2, 1, 1, 7, 1, 2, 1, 6]
def baseStart_1524768 : Nat := 118140960795 + 1524768 * 2 ^ 59
def prefixEnd_1524768 : Nat := 4983230072969 + 3 ^ 40 * 1524768 * 2
def baseEnd_1524768 : Nat := 115990943791821566205589

theorem tailTrace_1524768 : CollatzResearch.WordTrace tailWord_1524768 prefixEnd_1524768 115990943791821566205589 := by
  unfold tailWord_1524768
  simp only [CollatzResearch.WordTrace]
  refine ⟨27806428870016710243619479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37075238493355613658159305 27806428870016710243619479)
  ·
    refine ⟨41709643305025065365429219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27806428870016710243619479 41709643305025065365429219)
    ·
      refine ⟨62564464957537598048143829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41709643305025065365429219 62564464957537598048143829)
      ·
        refine ⟨1466354647442287454253371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 62564464957537598048143829 1466354647442287454253371)
        ·
          refine ⟨2199531971163431181380057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1466354647442287454253371 2199531971163431181380057)
          ·
            refine ⟨1649648978372573386035043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2199531971163431181380057 1649648978372573386035043)
            ·
              refine ⟨2474473467558860079052565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1649648978372573386035043 2474473467558860079052565)
              ·
                refine ⟨115990943791821566205589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2474473467558860079052565 115990943791821566205589)
                ·
                  rfl

theorem cell21_1524768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 6].length) (baseStart_1524768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1524768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1524768 prefixEnd_1524768 := by exact prefixLift 1524768
  have htrace : WordTrace (prefixWord ++ tailWord_1524768) baseStart_1524768 baseEnd_1524768 := by
    simpa [prefixWord, tailWord_1524768, baseEnd_1524768] using wordTrace_append hprefix tailTrace_1524768
  have hstable : (prefixWord ++ tailWord_1524768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524768).length < 2 ^ (prefixWord ++ tailWord_1524768).sum := by decide
  have hdescent : baseEnd_1524768 < baseStart_1524768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524779 : List Nat := [1, 1, 1, 1, 2, 1, 5, 5, 4]
def baseStart_1524779 : Nat := 118140960795 + 1524779 * 2 ^ 59
def prefixEnd_1524779 : Nat := 4983230072969 + 3 ^ 40 * 1524779 * 2
def baseEnd_1524779 : Nat := 347975341725331123933411

theorem tailTrace_1524779 : CollatzResearch.WordTrace tailWord_1524779 prefixEnd_1524779 347975341725331123933411 := by
  unfold tailWord_1524779
  simp only [CollatzResearch.WordTrace]
  refine ⟨55613258942993569365889391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37075505961995712910592927 55613258942993569365889391)
  ·
    refine ⟨83419888414490354048834087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55613258942993569365889391 83419888414490354048834087)
    ·
      refine ⟨125129832621735531073251131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83419888414490354048834087 125129832621735531073251131)
      ·
        refine ⟨187694748932603296609876697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125129832621735531073251131 187694748932603296609876697)
        ·
          refine ⟨140771061699452472457407523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187694748932603296609876697 140771061699452472457407523)
          ·
            refine ⟨211156592549178708686111285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140771061699452472457407523 211156592549178708686111285)
            ·
              refine ⟨19795930551485503939322933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 211156592549178708686111285 19795930551485503939322933)
              ·
                refine ⟨1855868489201765994311525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19795930551485503939322933 1855868489201765994311525)
                ·
                  refine ⟨347975341725331123933411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1855868489201765994311525 347975341725331123933411)
                  ·
                    rfl

theorem cell21_1524779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 4].length) (baseStart_1524779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1524779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1524779 prefixEnd_1524779 := by exact prefixLift 1524779
  have htrace : WordTrace (prefixWord ++ tailWord_1524779) baseStart_1524779 baseEnd_1524779 := by
    simpa [prefixWord, tailWord_1524779, baseEnd_1524779] using wordTrace_append hprefix tailTrace_1524779
  have hstable : (prefixWord ++ tailWord_1524779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524779).length < 2 ^ (prefixWord ++ tailWord_1524779).sum := by decide
  have hdescent : baseEnd_1524779 < baseStart_1524779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524813 : List Nat := [1, 6, 1, 1, 1, 2, 3, 2, 4]
def baseStart_1524813 : Nat := 118140960795 + 1524813 * 2 ^ 59
def prefixEnd_1524813 : Nat := 4983230072969 + 3 ^ 40 * 1524813 * 2
def baseEnd_1524813 : Nat := 347983100988554620366675

theorem tailTrace_1524813 : CollatzResearch.WordTrace tailWord_1524813 prefixEnd_1524813 347983100988554620366675 := by
  unfold tailWord_1524813
  simp only [CollatzResearch.WordTrace]
  refine ⟨55614499024870393172627093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37076332683246928781751395 55614499024870393172627093)
  ·
    refine ⟨2606929641790799679966895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55614499024870393172627093 2606929641790799679966895)
    ·
      refine ⟨3910394462686199519950343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2606929641790799679966895 3910394462686199519950343)
      ·
        refine ⟨5865591694029299279925515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3910394462686199519950343 5865591694029299279925515)
        ·
          refine ⟨8798387541043948919888273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5865591694029299279925515 8798387541043948919888273)
          ·
            refine ⟨6598790655782961689916205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8798387541043948919888273 6598790655782961689916205)
            ·
              refine ⟨2474546495918610633718577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6598790655782961689916205 2474546495918610633718577)
              ·
                refine ⟨1855909871938957975288933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2474546495918610633718577 1855909871938957975288933)
                ·
                  refine ⟨347983100988554620366675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1855909871938957975288933 347983100988554620366675)
                  ·
                    rfl

theorem cell21_1524813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_1524813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1524813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1524813 prefixEnd_1524813 := by exact prefixLift 1524813
  have htrace : WordTrace (prefixWord ++ tailWord_1524813) baseStart_1524813 baseEnd_1524813 := by
    simpa [prefixWord, tailWord_1524813, baseEnd_1524813] using wordTrace_append hprefix tailTrace_1524813
  have hstable : (prefixWord ++ tailWord_1524813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524813).length < 2 ^ (prefixWord ++ tailWord_1524813).sum := by decide
  have hdescent : baseEnd_1524813 < baseStart_1524813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524993 : List Nat := [1, 2, 4, 1, 1, 4, 2, 1, 5]
def baseStart_1524993 : Nat := 118140960795 + 1524993 * 2 ^ 59
def prefixEnd_1524993 : Nat := 4983230072969 + 3 ^ 40 * 1524993 * 2
def baseEnd_1524993 : Nat := 348024179440914307366307

theorem tailTrace_1524993 : CollatzResearch.WordTrace tailWord_1524993 prefixEnd_1524993 348024179440914307366307 := by
  unfold tailWord_1524993
  simp only [CollatzResearch.WordTrace]
  refine ⟨55621064164218283914179633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37080709442812189276119755 55621064164218283914179633)
  ·
    refine ⟨41715798123163712935634725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55621064164218283914179633 41715798123163712935634725)
    ·
      refine ⟨7821712148093196175431511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41715798123163712935634725 7821712148093196175431511)
      ·
        refine ⟨11732568222139794263147267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7821712148093196175431511 11732568222139794263147267)
        ·
          refine ⟨17598852333209691394720901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11732568222139794263147267 17598852333209691394720901)
          ·
            refine ⟨3299784812476817136510169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17598852333209691394720901 3299784812476817136510169)
            ·
              refine ⟨2474838609357612852382627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3299784812476817136510169 2474838609357612852382627)
              ·
                refine ⟨3712257914036419278573941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2474838609357612852382627 3712257914036419278573941)
                ·
                  refine ⟨348024179440914307366307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3712257914036419278573941 348024179440914307366307)
                  ·
                    rfl

theorem cell21_1524993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 5].length) (baseStart_1524993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1524993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1524993 prefixEnd_1524993 := by exact prefixLift 1524993
  have htrace : WordTrace (prefixWord ++ tailWord_1524993) baseStart_1524993 baseEnd_1524993 := by
    simpa [prefixWord, tailWord_1524993, baseEnd_1524993] using wordTrace_append hprefix tailTrace_1524993
  have hstable : (prefixWord ++ tailWord_1524993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524993).length < 2 ^ (prefixWord ++ tailWord_1524993).sum := by decide
  have hdescent : baseEnd_1524993 < baseStart_1524993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525100 : List Nat := [2, 2, 1, 1, 5, 2, 2, 2, 4]
def baseStart_1525100 : Nat := 118140960795 + 1525100 * 2 ^ 59
def prefixEnd_1525100 : Nat := 4983230072969 + 3 ^ 40 * 1525100 * 2
def baseEnd_1525100 : Nat := 348048598298705899082755

theorem tailTrace_1525100 : CollatzResearch.WordTrace tailWord_1525100 prefixEnd_1525100 348048598298705899082755 := by
  unfold tailWord_1525100
  simp only [CollatzResearch.WordTrace]
  refine ⟨27812483387415320594162377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37083311183220427458883169 27812483387415320594162377)
  ·
    refine ⟨20859362540561490445621783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27812483387415320594162377 20859362540561490445621783)
    ·
      refine ⟨31289043810842235668432675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20859362540561490445621783 31289043810842235668432675)
      ·
        refine ⟨46933565716263353502649013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31289043810842235668432675 46933565716263353502649013)
        ·
          refine ⟨4400021785899689390873345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46933565716263353502649013 4400021785899689390873345)
          ·
            refine ⟨3300016339424767043155009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4400021785899689390873345 3300016339424767043155009)
            ·
              refine ⟨2475012254568575282366257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3300016339424767043155009 2475012254568575282366257)
              ·
                refine ⟨1856259190926431461774693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2475012254568575282366257 1856259190926431461774693)
                ·
                  refine ⟨348048598298705899082755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1856259190926431461774693 348048598298705899082755)
                  ·
                    rfl

theorem cell21_1525100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_1525100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1525100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1525100 prefixEnd_1525100 := by exact prefixLift 1525100
  have htrace : WordTrace (prefixWord ++ tailWord_1525100) baseStart_1525100 baseEnd_1525100 := by
    simpa [prefixWord, tailWord_1525100, baseEnd_1525100] using wordTrace_append hprefix tailTrace_1525100
  have hstable : (prefixWord ++ tailWord_1525100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525100).length < 2 ^ (prefixWord ++ tailWord_1525100).sum := by decide
  have hdescent : baseEnd_1525100 < baseStart_1525100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525128 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 7]
def baseStart_1525128 : Nat := 118140960795 + 1525128 * 2 ^ 59
def prefixEnd_1525128 : Nat := 4983230072969 + 3 ^ 40 * 1525128 * 2
def baseEnd_1525128 : Nat := 348054988280184072616031

theorem tailTrace_1525128 : CollatzResearch.WordTrace tailWord_1525128 prefixEnd_1525128 348054988280184072616031 := by
  unfold tailWord_1525128
  simp only [CollatzResearch.WordTrace]
  refine ⟨27812994009364600985172019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37083992012486134646896025 27812994009364600985172019)
  ·
    refine ⟨41719491014046901477758029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27812994009364600985172019 41719491014046901477758029)
    ·
      refine ⟨15644809130267588054159261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41719491014046901477758029 15644809130267588054159261)
      ·
        refine ⟨5866803423850345520309723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15644809130267588054159261 5866803423850345520309723)
        ·
          refine ⟨8800205135775518280464585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5866803423850345520309723 8800205135775518280464585)
          ·
            refine ⟨6600153851831638710348439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8800205135775518280464585 6600153851831638710348439)
            ·
              refine ⟨9900230777747458065522659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6600153851831638710348439 9900230777747458065522659)
              ·
                refine ⟨14850346166621187098283989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9900230777747458065522659 14850346166621187098283989)
                ·
                  refine ⟨348054988280184072616031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14850346166621187098283989 348054988280184072616031)
                  ·
                    rfl

theorem cell21_1525128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 7].length) (baseStart_1525128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1525128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1525128 prefixEnd_1525128 := by exact prefixLift 1525128
  have htrace : WordTrace (prefixWord ++ tailWord_1525128) baseStart_1525128 baseEnd_1525128 := by
    simpa [prefixWord, tailWord_1525128, baseEnd_1525128] using wordTrace_append hprefix tailTrace_1525128
  have hstable : (prefixWord ++ tailWord_1525128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525128).length < 2 ^ (prefixWord ++ tailWord_1525128).sum := by decide
  have hdescent : baseEnd_1525128 < baseStart_1525128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525145 : List Nat := [1, 2, 1, 2, 1, 5, 1, 5, 3]
def baseStart_1525145 : Nat := 118140960795 + 1525145 * 2 ^ 59
def prefixEnd_1525145 : Nat := 4983230072969 + 3 ^ 40 * 1525145 * 2
def baseEnd_1525145 : Nat := 348058867911795820832663

theorem tailTrace_1525145 : CollatzResearch.WordTrace tailWord_1525145 prefixEnd_1525145 348058867911795820832663 := by
  unfold tailWord_1525145
  simp only [CollatzResearch.WordTrace]
  refine ⟨55626608059667613873712889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37084405373111742582475259 55626608059667613873712889)
  ·
    refine ⟨41719956044750710405284667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55626608059667613873712889 41719956044750710405284667)
    ·
      refine ⟨62579934067126065607927001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41719956044750710405284667 62579934067126065607927001)
      ·
        refine ⟨46934950550344549205945251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62579934067126065607927001 46934950550344549205945251)
        ·
          refine ⟨70402425825516823808917877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46934950550344549205945251 70402425825516823808917877)
          ·
            refine ⟨6600227421142202232086051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70402425825516823808917877 6600227421142202232086051)
            ·
              refine ⟨9900341131713303348129077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6600227421142202232086051 9900341131713303348129077)
              ·
                refine ⟨928156981098122188887101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9900341131713303348129077 928156981098122188887101)
                ·
                  refine ⟨348058867911795820832663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 928156981098122188887101 348058867911795820832663)
                  ·
                    rfl

theorem cell21_1525145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5, 3].length) (baseStart_1525145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1525145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1525145 prefixEnd_1525145 := by exact prefixLift 1525145
  have htrace : WordTrace (prefixWord ++ tailWord_1525145) baseStart_1525145 baseEnd_1525145 := by
    simpa [prefixWord, tailWord_1525145, baseEnd_1525145] using wordTrace_append hprefix tailTrace_1525145
  have hstable : (prefixWord ++ tailWord_1525145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525145).length < 2 ^ (prefixWord ++ tailWord_1525145).sum := by decide
  have hdescent : baseEnd_1525145 < baseStart_1525145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525159 : List Nat := [1, 1, 6, 1, 1, 1, 3, 1, 6]
def baseStart_1525159 : Nat := 118140960795 + 1525159 * 2 ^ 59
def prefixEnd_1525159 : Nat := 4983230072969 + 3 ^ 40 * 1525159 * 2
def baseEnd_1525159 : Nat := 348062062902534907599301

theorem tailTrace_1525159 : CollatzResearch.WordTrace tailWord_1525159 prefixEnd_1525159 348062062902534907599301 := by
  unfold tailWord_1525159
  simp only [CollatzResearch.WordTrace]
  refine ⟨55627118681616894264722531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37084745787744596176481687 55627118681616894264722531)
  ·
    refine ⟨83440678022425341397083797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55627118681616894264722531 83440678022425341397083797)
    ·
      refine ⟨3911281782301187877988303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83440678022425341397083797 3911281782301187877988303)
      ·
        refine ⟨5866922673451781816982455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3911281782301187877988303 5866922673451781816982455)
        ·
          refine ⟨8800384010177672725473683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5866922673451781816982455 8800384010177672725473683)
          ·
            refine ⟨13200576015266509088210525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8800384010177672725473683 13200576015266509088210525)
            ·
              refine ⟨4950216005724940908078947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13200576015266509088210525 4950216005724940908078947)
              ·
                refine ⟨7425324008587411362118421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4950216005724940908078947 7425324008587411362118421)
                ·
                  refine ⟨348062062902534907599301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7425324008587411362118421 348062062902534907599301)
                  ·
                    rfl

theorem cell21_1525159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 6].length) (baseStart_1525159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1525159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1525159 prefixEnd_1525159 := by exact prefixLift 1525159
  have htrace : WordTrace (prefixWord ++ tailWord_1525159) baseStart_1525159 baseEnd_1525159 := by
    simpa [prefixWord, tailWord_1525159, baseEnd_1525159] using wordTrace_append hprefix tailTrace_1525159
  have hstable : (prefixWord ++ tailWord_1525159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525159).length < 2 ^ (prefixWord ++ tailWord_1525159).sum := by decide
  have hdescent : baseEnd_1525159 < baseStart_1525159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525221 : List Nat := [1, 3, 1, 5, 1, 1, 3, 1, 5]
def baseStart_1525221 : Nat := 118140960795 + 1525221 * 2 ^ 59
def prefixEnd_1525221 : Nat := 4983230072969 + 3 ^ 40 * 1525221 * 2
def baseEnd_1525221 : Nat := 348076212147236577565841

theorem tailTrace_1525221 : CollatzResearch.WordTrace tailWord_1525221 prefixEnd_1525221 348076212147236577565841 := by
  unfold tailWord_1525221
  simp only [CollatzResearch.WordTrace]
  refine ⟨55629380007392278853479517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37086253338261519235653011 55629380007392278853479517)
  ·
    refine ⟨20861017502772104570054819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55629380007392278853479517 20861017502772104570054819)
    ·
      refine ⟨31291526254158156855082229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20861017502772104570054819 31291526254158156855082229)
      ·
        refine ⟨2933580586327327205163959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31291526254158156855082229 2933580586327327205163959)
        ·
          refine ⟨4400370879490990807745939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2933580586327327205163959 4400370879490990807745939)
          ·
            refine ⟨6600556319236486211618909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4400370879490990807745939 6600556319236486211618909)
            ·
              refine ⟨2475208619713682329357091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6600556319236486211618909 2475208619713682329357091)
              ·
                refine ⟨3712812929570523494035637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2475208619713682329357091 3712812929570523494035637)
                ·
                  refine ⟨348076212147236577565841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3712812929570523494035637 348076212147236577565841)
                  ·
                    rfl

theorem cell21_1525221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_1525221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1525221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1525221 prefixEnd_1525221 := by exact prefixLift 1525221
  have htrace : WordTrace (prefixWord ++ tailWord_1525221) baseStart_1525221 baseEnd_1525221 := by
    simpa [prefixWord, tailWord_1525221, baseEnd_1525221] using wordTrace_append hprefix tailTrace_1525221
  have hstable : (prefixWord ++ tailWord_1525221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525221).length < 2 ^ (prefixWord ++ tailWord_1525221).sum := by decide
  have hdescent : baseEnd_1525221 < baseStart_1525221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525272 : List Nat := [2, 1, 2, 3, 5, 1, 2, 2, 3]
def baseStart_1525272 : Nat := 118140960795 + 1525272 * 2 ^ 59
def prefixEnd_1525272 : Nat := 4983230072969 + 3 ^ 40 * 1525272 * 2
def baseEnd_1525272 : Nat := 348087851042071822215737

theorem tailTrace_1525272 : CollatzResearch.WordTrace tailWord_1525272 prefixEnd_1525272 348087851042071822215737 := by
  unfold tailWord_1525272
  simp only [CollatzResearch.WordTrace]
  refine ⟨27815620065103757281793035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37087493420138343042390713 27815620065103757281793035)
  ·
    refine ⟨41723430097655635922689553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27815620065103757281793035 41723430097655635922689553)
    ·
      refine ⟨31292572573241726942017165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41723430097655635922689553 31292572573241726942017165)
      ·
        refine ⟨11734714714965647603256437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31292572573241726942017165 11734714714965647603256437)
        ·
          refine ⟨1100129504528029462805291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11734714714965647603256437 1100129504528029462805291)
          ·
            refine ⟨1650194256792044194207937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1100129504528029462805291 1650194256792044194207937)
            ·
              refine ⟨1237645692594033145655953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1650194256792044194207937 1237645692594033145655953)
              ·
                refine ⟨928234269445524859241965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1237645692594033145655953 928234269445524859241965)
                ·
                  refine ⟨348087851042071822215737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 928234269445524859241965 348087851042071822215737)
                  ·
                    rfl

theorem cell21_1525272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2, 3].length) (baseStart_1525272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1525272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1525272 prefixEnd_1525272 := by exact prefixLift 1525272
  have htrace : WordTrace (prefixWord ++ tailWord_1525272) baseStart_1525272 baseEnd_1525272 := by
    simpa [prefixWord, tailWord_1525272, baseEnd_1525272] using wordTrace_append hprefix tailTrace_1525272
  have hstable : (prefixWord ++ tailWord_1525272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525272).length < 2 ^ (prefixWord ++ tailWord_1525272).sum := by decide
  have hdescent : baseEnd_1525272 < baseStart_1525272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525283 : List Nat := [1, 1, 1, 4, 6, 1, 1, 6]
def baseStart_1525283 : Nat := 118140960795 + 1525283 * 2 ^ 59
def prefixEnd_1525283 : Nat := 4983230072969 + 3 ^ 40 * 1525283 * 2
def baseEnd_1525283 : Nat := 116030120463979415844127

theorem tailTrace_1525283 : CollatzResearch.WordTrace tailWord_1525283 prefixEnd_1525283 116030120463979415844127 := by
  unfold tailWord_1525283
  simp only [CollatzResearch.WordTrace]
  refine ⟨55631641333167663442236503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37087760888778442294824335 55631641333167663442236503)
  ·
    refine ⟨83447461999751495163354755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55631641333167663442236503 83447461999751495163354755)
    ·
      refine ⟨125171192999627242745032133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83447461999751495163354755 125171192999627242745032133)
      ·
        refine ⟨23469598687430108014693525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125171192999627242745032133 23469598687430108014693525)
        ·
          refine ⟨1100137438473286313188759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23469598687430108014693525 1100137438473286313188759)
          ·
            refine ⟨1650206157709929469783139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1100137438473286313188759 1650206157709929469783139)
            ·
              refine ⟨2475309236564894204674709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1650206157709929469783139 2475309236564894204674709)
              ·
                refine ⟨116030120463979415844127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2475309236564894204674709 116030120463979415844127)
                ·
                  rfl

theorem cell21_1525283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 6].length) (baseStart_1525283 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1525283 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1525283 prefixEnd_1525283 := by exact prefixLift 1525283
  have htrace : WordTrace (prefixWord ++ tailWord_1525283) baseStart_1525283 baseEnd_1525283 := by
    simpa [prefixWord, tailWord_1525283, baseEnd_1525283] using wordTrace_append hprefix tailTrace_1525283
  have hstable : (prefixWord ++ tailWord_1525283).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525283).length < 2 ^ (prefixWord ++ tailWord_1525283).sum := by decide
  have hdescent : baseEnd_1525283 < baseStart_1525283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525404 : List Nat := [2, 2, 3, 2, 3, 1, 1, 3, 4]
def baseStart_1525404 : Nat := 118140960795 + 1525404 * 2 ^ 59
def prefixEnd_1525404 : Nat := 4983230072969 + 3 ^ 40 * 1525404 * 2
def baseEnd_1525404 : Nat := 348117975240468926015467

theorem tailTrace_1525404 : CollatzResearch.WordTrace tailWord_1525404 prefixEnd_1525404 348117975240468926015467 := by
  unfold tailWord_1525404
  simp only [CollatzResearch.WordTrace]
  refine ⟨27818027282864650553695633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37090703043819534071594177 27818027282864650553695633)
  ·
    refine ⟨20863520462148487915271725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27818027282864650553695633 20863520462148487915271725)
    ·
      refine ⟨7823820173305682968226897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20863520462148487915271725 7823820173305682968226897)
      ·
        refine ⟨5867865129979262226170173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7823820173305682968226897 5867865129979262226170173)
        ·
          refine ⟨2200449423742223334813815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5867865129979262226170173 2200449423742223334813815)
          ·
            refine ⟨3300674135613335002220723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2200449423742223334813815 3300674135613335002220723)
            ·
              refine ⟨4951011203420002503331085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3300674135613335002220723 4951011203420002503331085)
              ·
                refine ⟨1856629201282500938749157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4951011203420002503331085 1856629201282500938749157)
                ·
                  refine ⟨348117975240468926015467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1856629201282500938749157 348117975240468926015467)
                  ·
                    rfl

theorem cell21_1525404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_1525404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1525404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1525404 prefixEnd_1525404 := by exact prefixLift 1525404
  have htrace : WordTrace (prefixWord ++ tailWord_1525404) baseStart_1525404 baseEnd_1525404 := by
    simpa [prefixWord, tailWord_1525404, baseEnd_1525404] using wordTrace_append hprefix tailTrace_1525404
  have hstable : (prefixWord ++ tailWord_1525404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525404).length < 2 ^ (prefixWord ++ tailWord_1525404).sum := by decide
  have hdescent : baseEnd_1525404 < baseStart_1525404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525508 : List Nat := [2, 3, 2, 2, 1, 2, 1, 3, 5]
def baseStart_1525508 : Nat := 118140960795 + 1525508 * 2 ^ 59
def prefixEnd_1525508 : Nat := 4983230072969 + 3 ^ 40 * 1525508 * 2
def baseEnd_1525508 : Nat := 348141709457387856281921

theorem tailTrace_1525508 : CollatzResearch.WordTrace tailWord_1525508 prefixEnd_1525508 348141709457387856281921 := by
  unfold tailWord_1525508
  simp only [CollatzResearch.WordTrace]
  refine ⟨27819923878676263434588589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37093231838235017912784785 27819923878676263434588589)
  ·
    refine ⟨10432471454503598787970721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27819923878676263434588589 10432471454503598787970721)
    ·
      refine ⟨7824353590877699090978041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10432471454503598787970721 7824353590877699090978041)
      ·
        refine ⟨5868265193158274318233531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7824353590877699090978041 5868265193158274318233531)
        ·
          refine ⟨8802397789737411477350297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5868265193158274318233531 8802397789737411477350297)
          ·
            refine ⟨6601798342303058608012723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8802397789737411477350297 6601798342303058608012723)
            ·
              refine ⟨9902697513454587912019085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6601798342303058608012723 9902697513454587912019085)
              ·
                refine ⟨3713511567545470467007157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9902697513454587912019085 3713511567545470467007157)
                ·
                  refine ⟨348141709457387856281921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3713511567545470467007157 348141709457387856281921)
                  ·
                    rfl

theorem cell21_1525508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_1525508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1525508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1525508 prefixEnd_1525508 := by exact prefixLift 1525508
  have htrace : WordTrace (prefixWord ++ tailWord_1525508) baseStart_1525508 baseEnd_1525508 := by
    simpa [prefixWord, tailWord_1525508, baseEnd_1525508] using wordTrace_append hprefix tailTrace_1525508
  have hstable : (prefixWord ++ tailWord_1525508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525508).length < 2 ^ (prefixWord ++ tailWord_1525508).sum := by decide
  have hdescent : baseEnd_1525508 < baseStart_1525508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525553 : List Nat := [1, 2, 2, 3, 2, 4, 7]
def baseStart_1525553 : Nat := 118140960795 + 1525553 * 2 ^ 59
def prefixEnd_1525553 : Nat := 4983230072969 + 3 ^ 40 * 1525553 * 2
def baseEnd_1525553 : Nat := 38683553230053086447981

theorem tailTrace_1525553 : CollatzResearch.WordTrace tailWord_1525553 prefixEnd_1525553 38683553230053086447981 := by
  unfold tailWord_1525553
  simp only [CollatzResearch.WordTrace]
  refine ⟨55641489042189499554565313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37094326028126333036376875 55641489042189499554565313)
  ·
    refine ⟨41731116781642124665923985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55641489042189499554565313 41731116781642124665923985)
    ·
      refine ⟨31298337586231593499442989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41731116781642124665923985 31298337586231593499442989)
      ·
        refine ⟨11736876594836847562291121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31298337586231593499442989 11736876594836847562291121)
        ·
          refine ⟨8802657446127635671718341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11736876594836847562291121 8802657446127635671718341)
          ·
            refine ⟨1650498271148931688447189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8802657446127635671718341 1650498271148931688447189)
            ·
              refine ⟨38683553230053086447981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1650498271148931688447189 38683553230053086447981)
              ·
                rfl

theorem cell21_1525553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 7].length) (baseStart_1525553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1525553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1525553 prefixEnd_1525553 := by exact prefixLift 1525553
  have htrace : WordTrace (prefixWord ++ tailWord_1525553) baseStart_1525553 baseEnd_1525553 := by
    simpa [prefixWord, tailWord_1525553, baseEnd_1525553] using wordTrace_append hprefix tailTrace_1525553
  have hstable : (prefixWord ++ tailWord_1525553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525553).length < 2 ^ (prefixWord ++ tailWord_1525553).sum := by decide
  have hdescent : baseEnd_1525553 < baseStart_1525553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525612 : List Nat := [2, 2, 1, 1, 4, 11]
def baseStart_1525612 : Nat := 118140960795 + 1525612 * 2 ^ 59
def prefixEnd_1525612 : Nat := 4983230072969 + 3 ^ 40 * 1525612 * 2
def baseEnd_1525612 : Nat := 12895016432381732835125

theorem tailTrace_1525612 : CollatzResearch.WordTrace tailWord_1525612 prefixEnd_1525612 12895016432381732835125 := by
  unfold tailWord_1525612
  simp only [CollatzResearch.WordTrace]
  refine ⟨27821820474487876315481545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37095760632650501753975393 27821820474487876315481545)
  ·
    refine ⟨20866365355865907236611159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27821820474487876315481545 20866365355865907236611159)
    ·
      refine ⟨31299548033798860854916739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20866365355865907236611159 31299548033798860854916739)
      ·
        refine ⟨46949322050698291282375109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31299548033798860854916739 46949322050698291282375109)
        ·
          refine ⟨8802997884505929615445333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46949322050698291282375109 8802997884505929615445333)
          ·
            refine ⟨12895016432381732835125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8802997884505929615445333 12895016432381732835125)
            ·
              rfl

theorem cell21_1525612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 11].length) (baseStart_1525612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1525612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1525612 prefixEnd_1525612 := by exact prefixLift 1525612
  have htrace : WordTrace (prefixWord ++ tailWord_1525612) baseStart_1525612 baseEnd_1525612 := by
    simpa [prefixWord, tailWord_1525612, baseEnd_1525612] using wordTrace_append hprefix tailTrace_1525612
  have hstable : (prefixWord ++ tailWord_1525612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525612).length < 2 ^ (prefixWord ++ tailWord_1525612).sum := by decide
  have hdescent : baseEnd_1525612 < baseStart_1525612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525688 : List Nat := [2, 1, 2, 1, 2, 3, 2, 8]
def baseStart_1525688 : Nat := 118140960795 + 1525688 * 2 ^ 59
def prefixEnd_1525688 : Nat := 4983230072969 + 3 ^ 40 * 1525688 * 2
def baseEnd_1525688 : Nat := 116060929303249181093851

theorem tailTrace_1525688 : CollatzResearch.WordTrace tailWord_1525688 prefixEnd_1525688 116060929303249181093851 := by
  unfold tailWord_1525688
  simp only [CollatzResearch.WordTrace]
  refine ⟨27823206448350208805364859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37097608597800278407153145 27823206448350208805364859)
  ·
    refine ⟨41734809672525313208047289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27823206448350208805364859 41734809672525313208047289)
    ·
      refine ⟨31301107254393984906035467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41734809672525313208047289 31301107254393984906035467)
      ·
        refine ⟨46951660881590977359053201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31301107254393984906035467 46951660881590977359053201)
        ·
          refine ⟨35213745661193233019289901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46951660881590977359053201 35213745661193233019289901)
          ·
            refine ⟨13205154622947462382233713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35213745661193233019289901 13205154622947462382233713)
            ·
              refine ⟨9903865967210596786675285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13205154622947462382233713 9903865967210596786675285)
              ·
                refine ⟨116060929303249181093851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9903865967210596786675285 116060929303249181093851)
                ·
                  rfl

theorem cell21_1525688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 8].length) (baseStart_1525688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1525688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1525688 prefixEnd_1525688 := by exact prefixLift 1525688
  have htrace : WordTrace (prefixWord ++ tailWord_1525688) baseStart_1525688 baseEnd_1525688 := by
    simpa [prefixWord, tailWord_1525688, baseEnd_1525688] using wordTrace_append hprefix tailTrace_1525688
  have hstable : (prefixWord ++ tailWord_1525688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525688).length < 2 ^ (prefixWord ++ tailWord_1525688).sum := by decide
  have hdescent : baseEnd_1525688 < baseStart_1525688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525722 : List Nat := [3, 1, 1, 2, 6, 1, 7]
def baseStart_1525722 : Nat := 118140960795 + 1525722 * 2 ^ 59
def prefixEnd_1525722 : Nat := 4983230072969 + 3 ^ 40 * 1525722 * 2
def baseEnd_1525722 : Nat := 38687838574774559968313

theorem tailTrace_1525722 : CollatzResearch.WordTrace tailWord_1525722 prefixEnd_1525722 38687838574774559968313 := by
  unfold tailWord_1525722
  simp only [CollatzResearch.WordTrace]
  refine ⟨13911913244644310354366855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37098435319051494278311613 13911913244644310354366855)
  ·
    refine ⟨20867869866966465531550283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13911913244644310354366855 20867869866966465531550283)
    ·
      refine ⟨31301804800449698297325425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20867869866966465531550283 31301804800449698297325425)
      ·
        refine ⟨23476353600337273722994069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31301804800449698297325425 23476353600337273722994069)
        ·
          refine ⟨1100454075015809705765347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23476353600337273722994069 1100454075015809705765347)
          ·
            refine ⟨1650681112523714558648021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1100454075015809705765347 1650681112523714558648021)
            ·
              refine ⟨38687838574774559968313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1650681112523714558648021 38687838574774559968313)
              ·
                rfl

theorem cell21_1525722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 7].length) (baseStart_1525722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1525722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1525722 prefixEnd_1525722 := by exact prefixLift 1525722
  have htrace : WordTrace (prefixWord ++ tailWord_1525722) baseStart_1525722 baseEnd_1525722 := by
    simpa [prefixWord, tailWord_1525722, baseEnd_1525722] using wordTrace_append hprefix tailTrace_1525722
  have hstable : (prefixWord ++ tailWord_1525722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525722).length < 2 ^ (prefixWord ++ tailWord_1525722).sum := by decide
  have hdescent : baseEnd_1525722 < baseStart_1525722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525781 : List Nat := [1, 3, 2, 1, 6, 8]
def baseStart_1525781 : Nat := 118140960795 + 1525781 * 2 ^ 59
def prefixEnd_1525781 : Nat := 4983230072969 + 3 ^ 40 * 1525781 * 2
def baseEnd_1525781 : Nat := 12896444880622224008569

theorem tailTrace_1525781 : CollatzResearch.WordTrace tailWord_1525781 prefixEnd_1525781 12896444880622224008569 := by
  unfold tailWord_1525781
  simp only [CollatzResearch.WordTrace]
  refine ⟨55649804885363494493865197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37099869923575662995910131 55649804885363494493865197)
  ·
    refine ⟨20868676832011310435199449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55649804885363494493865197 20868676832011310435199449)
    ·
      refine ⟨15651507624008482826399587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20868676832011310435199449 15651507624008482826399587)
      ·
        refine ⟨23477261436012724239599381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15651507624008482826399587 23477261436012724239599381)
        ·
          refine ⟨1100496629813096448731221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23477261436012724239599381 1100496629813096448731221)
          ·
            refine ⟨12896444880622224008569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1100496629813096448731221 12896444880622224008569)
            ·
              rfl

theorem cell21_1525781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 8].length) (baseStart_1525781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1525781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1525781 prefixEnd_1525781 := by exact prefixLift 1525781
  have htrace : WordTrace (prefixWord ++ tailWord_1525781) baseStart_1525781 baseEnd_1525781 := by
    simpa [prefixWord, tailWord_1525781, baseEnd_1525781] using wordTrace_append hprefix tailTrace_1525781
  have hstable : (prefixWord ++ tailWord_1525781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525781).length < 2 ^ (prefixWord ++ tailWord_1525781).sum := by decide
  have hdescent : baseEnd_1525781 < baseStart_1525781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525795 : List Nat := [1, 1, 1, 4, 3, 1, 2, 3, 5]
def baseStart_1525795 : Nat := 118140960795 + 1525795 * 2 ^ 59
def prefixEnd_1525795 : Nat := 4983230072969 + 3 ^ 40 * 1525795 * 2
def baseEnd_1525795 : Nat := 348207206767539134998001

theorem tailTrace_1525795 : CollatzResearch.WordTrace tailWord_1525795 prefixEnd_1525795 348207206767539134998001 := by
  unfold tailWord_1525795
  simp only [CollatzResearch.WordTrace]
  refine ⟨55650315507312774884874839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37100210338208516589916559 55650315507312774884874839)
  ·
    refine ⟨83475473260969162327312259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55650315507312774884874839 83475473260969162327312259)
    ·
      refine ⟨125213209891453743490968389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83475473260969162327312259 125213209891453743490968389)
      ·
        refine ⟨23477476854647576904556573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125213209891453743490968389 23477476854647576904556573)
        ·
          refine ⟨8804053820492841339208715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23477476854647576904556573 8804053820492841339208715)
          ·
            refine ⟨13206080730739262008813073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8804053820492841339208715 13206080730739262008813073)
            ·
              refine ⟨9904560548054446506609805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13206080730739262008813073 9904560548054446506609805)
              ·
                refine ⟨3714210205520417439978677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9904560548054446506609805 3714210205520417439978677)
                ·
                  refine ⟨348207206767539134998001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3714210205520417439978677 348207206767539134998001)
                  ·
                    rfl

theorem cell21_1525795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 5].length) (baseStart_1525795 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1525795 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1525795 prefixEnd_1525795 := by exact prefixLift 1525795
  have htrace : WordTrace (prefixWord ++ tailWord_1525795) baseStart_1525795 baseEnd_1525795 := by
    simpa [prefixWord, tailWord_1525795, baseEnd_1525795] using wordTrace_append hprefix tailTrace_1525795
  have hstable : (prefixWord ++ tailWord_1525795).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525795).length < 2 ^ (prefixWord ++ tailWord_1525795).sum := by decide
  have hdescent : baseEnd_1525795 < baseStart_1525795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525846 : List Nat := [5, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_1525846 : Nat := 118140960795 + 1525846 * 2 ^ 59
def prefixEnd_1525846 : Nat := 4983230072969 + 3 ^ 40 * 1525846 * 2
def baseEnd_1525846 : Nat := 348218845662374379647897

theorem tailTrace_1525846 : CollatzResearch.WordTrace tailWord_1525846 prefixEnd_1525846 348218845662374379647897 := by
  unfold tailWord_1525846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3478260976883000662186337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37101450420085340396654261 3478260976883000662186337)
  ·
    refine ⟨2608695732662250496639753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3478260976883000662186337 2608695732662250496639753)
    ·
      refine ⟨1956521799496687872479815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2608695732662250496639753 1956521799496687872479815)
      ·
        refine ⟨2934782699245031808719723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1956521799496687872479815 2934782699245031808719723)
        ·
          refine ⟨4402174048867547713079585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2934782699245031808719723 4402174048867547713079585)
          ·
            refine ⟨3301630536650660784809689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4402174048867547713079585 3301630536650660784809689)
            ·
              refine ⟨2476222902487995588607267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3301630536650660784809689 2476222902487995588607267)
              ·
                refine ⟨3714334353731993382910901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2476222902487995588607267 3714334353731993382910901)
                ·
                  refine ⟨348218845662374379647897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3714334353731993382910901 348218845662374379647897)
                  ·
                    rfl

theorem cell21_1525846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_1525846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1525846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1525846 prefixEnd_1525846 := by exact prefixLift 1525846
  have htrace : WordTrace (prefixWord ++ tailWord_1525846) baseStart_1525846 baseEnd_1525846 := by
    simpa [prefixWord, tailWord_1525846, baseEnd_1525846] using wordTrace_append hprefix tailTrace_1525846
  have hstable : (prefixWord ++ tailWord_1525846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525846).length < 2 ^ (prefixWord ++ tailWord_1525846).sum := by decide
  have hdescent : baseEnd_1525846 < baseStart_1525846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525871 : List Nat := [1, 1, 2, 1, 3, 4, 2, 2, 5]
def baseStart_1525871 : Nat := 118140960795 + 1525871 * 2 ^ 59
def prefixEnd_1525871 : Nat := 4983230072969 + 3 ^ 40 * 1525871 * 2
def baseEnd_1525871 : Nat := 348224551002979891731179

theorem tailTrace_1525871 : CollatzResearch.WordTrace tailWord_1525871 prefixEnd_1525871 348224551002979891731179 := by
  unfold tailWord_1525871
  simp only [CollatzResearch.WordTrace]
  refine ⟨55653087455037439864641467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37102058303358293243094311 55653087455037439864641467)
  ·
    refine ⟨83479631182556159796962201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55653087455037439864641467 83479631182556159796962201)
    ·
      refine ⟨62609723386917119847721651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83479631182556159796962201 62609723386917119847721651)
      ·
        refine ⟨93914585080375679771582477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62609723386917119847721651 93914585080375679771582477)
        ·
          refine ⟨35217969405140879914343429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93914585080375679771582477 35217969405140879914343429)
          ·
            refine ⟨6603369263463914983939393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35217969405140879914343429 6603369263463914983939393)
            ·
              refine ⟨4952526947597936237954545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6603369263463914983939393 4952526947597936237954545)
              ·
                refine ⟨3714395210698452178465909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4952526947597936237954545 3714395210698452178465909)
                ·
                  refine ⟨348224551002979891731179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3714395210698452178465909 348224551002979891731179)
                  ·
                    rfl

theorem cell21_1525871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 5].length) (baseStart_1525871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1525871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1525871 prefixEnd_1525871 := by exact prefixLift 1525871
  have htrace : WordTrace (prefixWord ++ tailWord_1525871) baseStart_1525871 baseEnd_1525871 := by
    simpa [prefixWord, tailWord_1525871, baseEnd_1525871] using wordTrace_append hprefix tailTrace_1525871
  have hstable : (prefixWord ++ tailWord_1525871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525871).length < 2 ^ (prefixWord ++ tailWord_1525871).sum := by decide
  have hdescent : baseEnd_1525871 < baseStart_1525871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525874 : List Nat := [3, 2, 1, 2, 2, 4, 2, 5]
def baseStart_1525874 : Nat := 118140960795 + 1525874 * 2 ^ 59
def prefixEnd_1525874 : Nat := 4983230072969 + 3 ^ 40 * 1525874 * 2
def baseEnd_1525874 : Nat := 116075078547950851060391

theorem tailTrace_1525874 : CollatzResearch.WordTrace tailWord_1525874 prefixEnd_1525874 116075078547950851060391 := by
  unfold tailWord_1525874
  simp only [CollatzResearch.WordTrace]
  refine ⟨13913299218506642844250169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37102131249351047584667117 13913299218506642844250169)
  ·
    refine ⟨10434974413879982133187627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13913299218506642844250169 10434974413879982133187627)
    ·
      refine ⟨15652461620819973199781441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10434974413879982133187627 15652461620819973199781441)
      ·
        refine ⟨11739346215614979899836081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15652461620819973199781441 11739346215614979899836081)
        ·
          refine ⟨8804509661711234924877061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11739346215614979899836081 8804509661711234924877061)
          ·
            refine ⟨1650845561570856548414449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8804509661711234924877061 1650845561570856548414449)
            ·
              refine ⟨1238134171178142411310837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1650845561570856548414449 1238134171178142411310837)
              ·
                refine ⟨116075078547950851060391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1238134171178142411310837 116075078547950851060391)
                ·
                  rfl

theorem cell21_1525874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 5].length) (baseStart_1525874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1525874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1525874 prefixEnd_1525874 := by exact prefixLift 1525874
  have htrace : WordTrace (prefixWord ++ tailWord_1525874) baseStart_1525874 baseEnd_1525874 := by
    simpa [prefixWord, tailWord_1525874, baseEnd_1525874] using wordTrace_append hprefix tailTrace_1525874
  have hstable : (prefixWord ++ tailWord_1525874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525874).length < 2 ^ (prefixWord ++ tailWord_1525874).sum := by decide
  have hdescent : baseEnd_1525874 < baseStart_1525874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525919 : List Nat := [1, 1, 2, 6, 1, 2, 1, 3, 4]
def baseStart_1525919 : Nat := 118140960795 + 1525919 * 2 ^ 59
def prefixEnd_1525919 : Nat := 4983230072969 + 3 ^ 40 * 1525919 * 2
def baseEnd_1525919 : Nat := 348235505256942474931081

theorem tailTrace_1525919 : CollatzResearch.WordTrace tailWord_1525919 prefixEnd_1525919 348235505256942474931081 := by
  unfold tailWord_1525919
  simp only [CollatzResearch.WordTrace]
  refine ⟨55654838158863544062388811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37103225439242362708259207 55654838158863544062388811)
  ·
    refine ⟨83482257238295316093583217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55654838158863544062388811 83482257238295316093583217)
    ·
      refine ⟨62611692928721487070187413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83482257238295316093583217 62611692928721487070187413)
      ·
        refine ⟨2934923106033819706415035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 62611692928721487070187413 2934923106033819706415035)
        ·
          refine ⟨4402384659050729559622553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2934923106033819706415035 4402384659050729559622553)
          ·
            refine ⟨3301788494288047169716915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4402384659050729559622553 3301788494288047169716915)
            ·
              refine ⟨4952682741432070754575373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3301788494288047169716915 4952682741432070754575373)
              ·
                refine ⟨1857256028037026532965765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4952682741432070754575373 1857256028037026532965765)
                ·
                  refine ⟨348235505256942474931081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1857256028037026532965765 348235505256942474931081)
                  ·
                    rfl

theorem cell21_1525919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 4].length) (baseStart_1525919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1525919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1525919 prefixEnd_1525919 := by exact prefixLift 1525919
  have htrace : WordTrace (prefixWord ++ tailWord_1525919) baseStart_1525919 baseEnd_1525919 := by
    simpa [prefixWord, tailWord_1525919, baseEnd_1525919] using wordTrace_append hprefix tailTrace_1525919
  have hstable : (prefixWord ++ tailWord_1525919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525919).length < 2 ^ (prefixWord ++ tailWord_1525919).sum := by decide
  have hdescent : baseEnd_1525919 < baseStart_1525919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525933 : List Nat := [1, 5, 2, 1, 2, 1, 2, 7]
def baseStart_1525933 : Nat := 118140960795 + 1525933 * 2 ^ 59
def prefixEnd_1525933 : Nat := 4983230072969 + 3 ^ 40 * 1525933 * 2
def baseEnd_1525933 : Nat := 116079566749227187232573

theorem tailTrace_1525933 : CollatzResearch.WordTrace tailWord_1525933 prefixEnd_1525933 116079566749227187232573 := by
  unfold tailWord_1525933
  simp only [CollatzResearch.WordTrace]
  refine ⟨55655348780812824453398453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37103565853875216302265635 55655348780812824453398453)
  ·
    refine ⟨5217688948201202292506105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55655348780812824453398453 5217688948201202292506105)
    ·
      refine ⟨3913266711150901719379579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5217688948201202292506105 3913266711150901719379579)
      ·
        refine ⟨5869900066726352579069369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3913266711150901719379579 5869900066726352579069369)
        ·
          refine ⟨4402425050044764434302027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5869900066726352579069369 4402425050044764434302027)
          ·
            refine ⟨6603637575067146651453041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4402425050044764434302027 6603637575067146651453041)
            ·
              refine ⟨4952728181300359988589781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6603637575067146651453041 4952728181300359988589781)
              ·
                refine ⟨116079566749227187232573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4952728181300359988589781 116079566749227187232573)
                ·
                  rfl

theorem cell21_1525933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 7].length) (baseStart_1525933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1525933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1525933 prefixEnd_1525933 := by exact prefixLift 1525933
  have htrace : WordTrace (prefixWord ++ tailWord_1525933) baseStart_1525933 baseEnd_1525933 := by
    simpa [prefixWord, tailWord_1525933, baseEnd_1525933] using wordTrace_append hprefix tailTrace_1525933
  have hstable : (prefixWord ++ tailWord_1525933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525933).length < 2 ^ (prefixWord ++ tailWord_1525933).sum := by decide
  have hdescent : baseEnd_1525933 < baseStart_1525933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525978 : List Nat := [3, 1, 1, 2, 2, 1, 4, 3, 4]
def baseStart_1525978 : Nat := 118140960795 + 1525978 * 2 ^ 59
def prefixEnd_1525978 : Nat := 4983230072969 + 3 ^ 40 * 1525978 * 2
def baseEnd_1525978 : Nat := 348248969860771483447627

theorem tailTrace_1525978 : CollatzResearch.WordTrace tailWord_1525978 prefixEnd_1525978 348248969860771483447627 := by
  unfold tailWord_1525978
  simp only [CollatzResearch.WordTrace]
  refine ⟨13914247516412449284696647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37104660043766531425857725 13914247516412449284696647)
  ·
    refine ⟨20871371274618673927044971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13914247516412449284696647 20871371274618673927044971)
    ·
      refine ⟨31307056911928010890567457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20871371274618673927044971 31307056911928010890567457)
      ·
        refine ⟨23480292683946008167925593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31307056911928010890567457 23480292683946008167925593)
        ·
          refine ⟨17610219512959506125944195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23480292683946008167925593 17610219512959506125944195)
          ·
            refine ⟨26415329269439259188916293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17610219512959506125944195 26415329269439259188916293)
            ·
              refine ⟨4952874238019861097921805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26415329269439259188916293 4952874238019861097921805)
              ·
                refine ⟨1857327839257447911720677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4952874238019861097921805 1857327839257447911720677)
                ·
                  refine ⟨348248969860771483447627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1857327839257447911720677 348248969860771483447627)
                  ·
                    rfl

theorem cell21_1525978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_1525978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1525978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1525978 prefixEnd_1525978 := by exact prefixLift 1525978
  have htrace : WordTrace (prefixWord ++ tailWord_1525978) baseStart_1525978 baseEnd_1525978 := by
    simpa [prefixWord, tailWord_1525978, baseEnd_1525978] using wordTrace_append hprefix tailTrace_1525978
  have hstable : (prefixWord ++ tailWord_1525978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525978).length < 2 ^ (prefixWord ++ tailWord_1525978).sum := by decide
  have hdescent : baseEnd_1525978 < baseStart_1525978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526116 : List Nat := [2, 3, 1, 1, 3, 1, 2, 5, 3]
def baseStart_1526116 : Nat := 118140960795 + 1526116 * 2 ^ 59
def prefixEnd_1526116 : Nat := 4983230072969 + 3 ^ 40 * 1526116 * 2
def baseEnd_1526116 : Nat := 348280463340913910147345

theorem tailTrace_1526116 : CollatzResearch.WordTrace tailWord_1526116 prefixEnd_1526116 348280463340913910147345 := by
  unfold tailWord_1526116
  simp only [CollatzResearch.WordTrace]
  refine ⟨27831011669574923353655101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37108015559433231138206801 27831011669574923353655101)
  ·
    refine ⟨10436629376090596257620663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27831011669574923353655101 10436629376090596257620663)
    ·
      refine ⟨15654944064135894386430995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10436629376090596257620663 15654944064135894386430995)
      ·
        refine ⟨23482416096203841579646493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15654944064135894386430995 23482416096203841579646493)
        ·
          refine ⟨8805906036076440592367435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23482416096203841579646493 8805906036076440592367435)
          ·
            refine ⟨13208859054114660888551153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8805906036076440592367435 13208859054114660888551153)
            ·
              refine ⟨9906644290585995666413365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13208859054114660888551153 9906644290585995666413365)
              ·
                refine ⟨928747902242437093726253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9906644290585995666413365 928747902242437093726253)
                ·
                  refine ⟨348280463340913910147345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 928747902242437093726253 348280463340913910147345)
                  ·
                    rfl

theorem cell21_1526116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_1526116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1526116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1526116 prefixEnd_1526116 := by exact prefixLift 1526116
  have htrace : WordTrace (prefixWord ++ tailWord_1526116) baseStart_1526116 baseEnd_1526116 := by
    simpa [prefixWord, tailWord_1526116, baseEnd_1526116] using wordTrace_append hprefix tailTrace_1526116
  have hstable : (prefixWord ++ tailWord_1526116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526116).length < 2 ^ (prefixWord ++ tailWord_1526116).sum := by decide
  have hdescent : baseEnd_1526116 < baseStart_1526116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526130 : List Nat := [3, 2, 1, 2, 1, 3, 1, 4, 4]
def baseStart_1526130 : Nat := 118140960795 + 1526130 * 2 ^ 59
def prefixEnd_1526130 : Nat := 4983230072969 + 3 ^ 40 * 1526130 * 2
def baseEnd_1526130 : Nat := 348283658331652996913983

theorem tailTrace_1526130 : CollatzResearch.WordTrace tailWord_1526130 prefixEnd_1526130 348283658331652996913983 := by
  unfold tailWord_1526130
  simp only [CollatzResearch.WordTrace]
  refine ⟨13915633490274781774579961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37108355974066084732213229 13915633490274781774579961)
  ·
    refine ⟨10436725117706086330934971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13915633490274781774579961 10436725117706086330934971)
    ·
      refine ⟨15655087676559129496402457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10436725117706086330934971 15655087676559129496402457)
      ·
        refine ⟨11741315757419347122301843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15655087676559129496402457 11741315757419347122301843)
        ·
          refine ⟨17611973636129020683452765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11741315757419347122301843 17611973636129020683452765)
          ·
            refine ⟨6604490113548382756294787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17611973636129020683452765 6604490113548382756294787)
            ·
              refine ⟨9906735170322574134442181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6604490113548382756294787 9906735170322574134442181)
              ·
                refine ⟨1857512844435482650207909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9906735170322574134442181 1857512844435482650207909)
                ·
                  refine ⟨348283658331652996913983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1857512844435482650207909 348283658331652996913983)
                  ·
                    rfl

theorem cell21_1526130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_1526130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1526130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1526130 prefixEnd_1526130 := by exact prefixLift 1526130
  have htrace : WordTrace (prefixWord ++ tailWord_1526130) baseStart_1526130 baseEnd_1526130 := by
    simpa [prefixWord, tailWord_1526130, baseEnd_1526130] using wordTrace_append hprefix tailTrace_1526130
  have hstable : (prefixWord ++ tailWord_1526130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526130).length < 2 ^ (prefixWord ++ tailWord_1526130).sum := by decide
  have hdescent : baseEnd_1526130 < baseStart_1526130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526133 : List Nat := [1, 3, 4, 1, 2, 2, 1, 4, 3]
def baseStart_1526133 : Nat := 118140960795 + 1526133 * 2 ^ 59
def prefixEnd_1526133 : Nat := 4983230072969 + 3 ^ 40 * 1526133 * 2
def baseEnd_1526133 : Nat := 348284342972525658363977

theorem tailTrace_1526133 : CollatzResearch.WordTrace tailWord_1526133 prefixEnd_1526133 348284342972525658363977 := by
  unfold tailWord_1526133
  simp only [CollatzResearch.WordTrace]
  refine ⟨55662643380088258610679053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37108428920058839073786035 55662643380088258610679053)
  ·
    refine ⟨20873491267533096979004645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55662643380088258610679053 20873491267533096979004645)
    ·
      refine ⟨3913779612662455683563371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20873491267533096979004645 3913779612662455683563371)
      ·
        refine ⟨5870669418993683525345057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3913779612662455683563371 5870669418993683525345057)
        ·
          refine ⟨4403002064245262644008793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5870669418993683525345057 4403002064245262644008793)
          ·
            refine ⟨3302251548183946983006595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4403002064245262644008793 3302251548183946983006595)
            ·
              refine ⟨4953377322275920474509893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3302251548183946983006595 4953377322275920474509893)
              ·
                refine ⟨928758247926735088970605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4953377322275920474509893 928758247926735088970605)
                ·
                  refine ⟨348284342972525658363977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 928758247926735088970605 348284342972525658363977)
                  ·
                    rfl

theorem cell21_1526133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4, 3].length) (baseStart_1526133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1526133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1526133 prefixEnd_1526133 := by exact prefixLift 1526133
  have htrace : WordTrace (prefixWord ++ tailWord_1526133) baseStart_1526133 baseEnd_1526133 := by
    simpa [prefixWord, tailWord_1526133, baseEnd_1526133] using wordTrace_append hprefix tailTrace_1526133
  have hstable : (prefixWord ++ tailWord_1526133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526133).length < 2 ^ (prefixWord ++ tailWord_1526133).sum := by decide
  have hdescent : baseEnd_1526133 < baseStart_1526133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526206 : List Nat := [4, 2, 1, 1, 1, 1, 2, 5, 4]
def baseStart_1526206 : Nat := 118140960795 + 1526206 * 2 ^ 59
def prefixEnd_1526206 : Nat := 4983230072969 + 3 ^ 40 * 1526206 * 2
def baseEnd_1526206 : Nat := 348301002567093753647161

theorem tailTrace_1526206 : CollatzResearch.WordTrace tailWord_1526206 prefixEnd_1526206 348301002567093753647161 := by
  unfold tailWord_1526206
  simp only [CollatzResearch.WordTrace]
  refine ⟨6958163238602974009760809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37110203939215861385390981 6958163238602974009760809)
  ·
    refine ⟨5218622428952230507320607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6958163238602974009760809 5218622428952230507320607)
    ·
      refine ⟨7827933643428345760980911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5218622428952230507320607 7827933643428345760980911)
      ·
        refine ⟨11741900465142518641471367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7827933643428345760980911 11741900465142518641471367)
        ·
          refine ⟨17612850697713777962207051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11741900465142518641471367 17612850697713777962207051)
          ·
            refine ⟨26419276046570666943310577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17612850697713777962207051 26419276046570666943310577)
            ·
              refine ⟨19814457034928000207482933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26419276046570666943310577 19814457034928000207482933)
              ·
                refine ⟨1857605347024500019451525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19814457034928000207482933 1857605347024500019451525)
                ·
                  refine ⟨348301002567093753647161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1857605347024500019451525 348301002567093753647161)
                  ·
                    rfl

theorem cell21_1526206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_1526206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1526206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1526206 prefixEnd_1526206 := by exact prefixLift 1526206
  have htrace : WordTrace (prefixWord ++ tailWord_1526206) baseStart_1526206 baseEnd_1526206 := by
    simpa [prefixWord, tailWord_1526206, baseEnd_1526206] using wordTrace_append hprefix tailTrace_1526206
  have hstable : (prefixWord ++ tailWord_1526206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526206).length < 2 ^ (prefixWord ++ tailWord_1526206).sum := by decide
  have hdescent : baseEnd_1526206 < baseStart_1526206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526389 : List Nat := [1, 3, 4, 2, 2, 1, 1, 7]
def baseStart_1526389 : Nat := 118140960795 + 1526389 * 2 ^ 59
def prefixEnd_1526389 : Nat := 4983230072969 + 3 ^ 40 * 1526389 * 2
def baseEnd_1526389 : Nat := 116114255220108700698929

theorem tailTrace_1526389 : CollatzResearch.WordTrace tailWord_1526389 prefixEnd_1526389 116114255220108700698929 := by
  unfold tailWord_1526389
  simp only [CollatzResearch.WordTrace]
  refine ⟨55671980467160814331998221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37114653644773876221332147 55671980467160814331998221)
  ·
    refine ⟨20876992675185305374499333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55671980467160814331998221 20876992675185305374499333)
    ·
      refine ⟨3914436126597244757718625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20876992675185305374499333 3914436126597244757718625)
      ·
        refine ⟨2935827094947933568288969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3914436126597244757718625 2935827094947933568288969)
        ·
          refine ⟨2201870321210950176216727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2935827094947933568288969 2201870321210950176216727)
          ·
            refine ⟨3302805481816425264325091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2201870321210950176216727 3302805481816425264325091)
            ·
              refine ⟨4954208222724637896487637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3302805481816425264325091 4954208222724637896487637)
              ·
                refine ⟨116114255220108700698929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4954208222724637896487637 116114255220108700698929)
                ·
                  rfl

theorem cell21_1526389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 7].length) (baseStart_1526389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1526389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1526389 prefixEnd_1526389 := by exact prefixLift 1526389
  have htrace : WordTrace (prefixWord ++ tailWord_1526389) baseStart_1526389 baseEnd_1526389 := by
    simpa [prefixWord, tailWord_1526389, baseEnd_1526389] using wordTrace_append hprefix tailTrace_1526389
  have hstable : (prefixWord ++ tailWord_1526389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526389).length < 2 ^ (prefixWord ++ tailWord_1526389).sum := by decide
  have hdescent : baseEnd_1526389 < baseStart_1526389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526420 : List Nat := [2, 4, 2, 2, 1, 1, 3, 1, 5]
def baseStart_1526420 : Nat := 118140960795 + 1526420 * 2 ^ 59
def prefixEnd_1526420 : Nat := 4983230072969 + 3 ^ 40 * 1526420 * 2
def baseEnd_1526420 : Nat := 348349840282676937080057

theorem tailTrace_1526420 : CollatzResearch.WordTrace tailWord_1526420 prefixEnd_1526420 348349840282676937080057 := by
  unfold tailWord_1526420
  simp only [CollatzResearch.WordTrace]
  refine ⟨27836555565024253313188357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37115407420032337750917809 27836555565024253313188357)
  ·
    refine ⟨5219354168442047496222817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27836555565024253313188357 5219354168442047496222817)
    ·
      refine ⟨3914515626331535622167113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5219354168442047496222817 3914515626331535622167113)
      ·
        refine ⟨2935886719748651716625335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3914515626331535622167113 2935886719748651716625335)
        ·
          refine ⟨4403830079622977574938003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2935886719748651716625335 4403830079622977574938003)
          ·
            refine ⟨6605745119434466362407005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4403830079622977574938003 6605745119434466362407005)
            ·
              refine ⟨2477154419787924885902627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6605745119434466362407005 2477154419787924885902627)
              ·
                refine ⟨3715731629681887328853941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2477154419787924885902627 3715731629681887328853941)
                ·
                  refine ⟨348349840282676937080057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3715731629681887328853941 348349840282676937080057)
                  ·
                    rfl

theorem cell21_1526420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_1526420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1526420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1526420 prefixEnd_1526420 := by exact prefixLift 1526420
  have htrace : WordTrace (prefixWord ++ tailWord_1526420) baseStart_1526420 baseEnd_1526420 := by
    simpa [prefixWord, tailWord_1526420, baseEnd_1526420] using wordTrace_append hprefix tailTrace_1526420
  have hstable : (prefixWord ++ tailWord_1526420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526420).length < 2 ^ (prefixWord ++ tailWord_1526420).sum := by decide
  have hdescent : baseEnd_1526420 < baseStart_1526420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526465 : List Nat := [1, 2, 6, 2, 1, 9]
def baseStart_1526465 : Nat := 118140960795 + 1526465 * 2 ^ 59
def prefixEnd_1526465 : Nat := 4983230072969 + 3 ^ 40 * 1526465 * 2
def baseEnd_1526465 : Nat := 12902226292435809586295

theorem tailTrace_1526465 : CollatzResearch.WordTrace tailWord_1526465 prefixEnd_1526465 12902226292435809586295 := by
  unfold tailWord_1526465
  simp only [CollatzResearch.WordTrace]
  refine ⟨55674752414885479311764849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37116501609923652874509899 55674752414885479311764849)
  ·
    refine ⟨41756064311164109483823637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55674752414885479311764849 41756064311164109483823637)
    ·
      refine ⟨1957315514585817632054233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41756064311164109483823637 1957315514585817632054233)
      ·
        refine ⟨1467986635939363224040675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1957315514585817632054233 1467986635939363224040675)
        ·
          refine ⟨2201979953909044836061013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1467986635939363224040675 2201979953909044836061013)
          ·
            refine ⟨12902226292435809586295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2201979953909044836061013 12902226292435809586295)
            ·
              rfl

theorem cell21_1526465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 9].length) (baseStart_1526465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1526465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1526465 prefixEnd_1526465 := by exact prefixLift 1526465
  have htrace : WordTrace (prefixWord ++ tailWord_1526465) baseStart_1526465 baseEnd_1526465 := by
    simpa [prefixWord, tailWord_1526465, baseEnd_1526465] using wordTrace_append hprefix tailTrace_1526465
  have hstable : (prefixWord ++ tailWord_1526465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526465).length < 2 ^ (prefixWord ++ tailWord_1526465).sum := by decide
  have hdescent : baseEnd_1526465 < baseStart_1526465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526482 : List Nat := [3, 2, 2, 2, 4, 1, 1, 6]
def baseStart_1526482 : Nat := 118140960795 + 1526482 * 2 ^ 59
def prefixEnd_1526482 : Nat := 4983230072969 + 3 ^ 40 * 1526482 * 2
def baseEnd_1526482 : Nat := 116121329842459535682199

theorem tailTrace_1526482 : CollatzResearch.WordTrace tailWord_1526482 prefixEnd_1526482 116121329842459535682199 := by
  unfold tailWord_1526482
  simp only [CollatzResearch.WordTrace]
  refine ⟨13918843113955972803783425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37116914970549260810089133 13918843113955972803783425)
  ·
    refine ⟨10439132335466979602837569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13918843113955972803783425 10439132335466979602837569)
    ·
      refine ⟨7829349251600234702128177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10439132335466979602837569 7829349251600234702128177)
      ·
        refine ⟨5872011938700176026596133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7829349251600234702128177 5872011938700176026596133)
        ·
          refine ⟨1101002238506283004986775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5872011938700176026596133 1101002238506283004986775)
          ·
            refine ⟨1651503357759424507480163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1101002238506283004986775 1651503357759424507480163)
            ·
              refine ⟨2477255036639136761220245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1651503357759424507480163 2477255036639136761220245)
              ·
                refine ⟨116121329842459535682199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2477255036639136761220245 116121329842459535682199)
                ·
                  rfl

theorem cell21_1526482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 6].length) (baseStart_1526482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1526482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1526482 prefixEnd_1526482 := by exact prefixLift 1526482
  have htrace : WordTrace (prefixWord ++ tailWord_1526482) baseStart_1526482 baseEnd_1526482 := by
    simpa [prefixWord, tailWord_1526482, baseEnd_1526482] using wordTrace_append hprefix tailTrace_1526482
  have hstable : (prefixWord ++ tailWord_1526482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526482).length < 2 ^ (prefixWord ++ tailWord_1526482).sum := by decide
  have hdescent : baseEnd_1526482 < baseStart_1526482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526589 : List Nat := [1, 4, 1, 4, 3, 1, 1, 1, 5]
def baseStart_1526589 : Nat := 118140960795 + 1526589 * 2 ^ 59
def prefixEnd_1526589 : Nat := 4983230072969 + 3 ^ 40 * 1526589 * 2
def baseEnd_1526589 : Nat := 348388408385170198763045

theorem tailTrace_1526589 : CollatzResearch.WordTrace tailWord_1526589 prefixEnd_1526589 348388408385170198763045 := by
  unfold tailWord_1526589
  simp only [CollatzResearch.WordTrace]
  refine ⟨55679275066436248489278821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37119516710957498992852547 55679275066436248489278821)
  ·
    refine ⟨10439864074956796591739779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55679275066436248489278821 10439864074956796591739779)
    ·
      refine ⟨15659796112435194887609669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10439864074956796591739779 15659796112435194887609669)
      ·
        refine ⟨2936211771081599041426813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15659796112435194887609669 2936211771081599041426813)
        ·
          refine ⟨1101079414155599640535055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2936211771081599041426813 1101079414155599640535055)
          ·
            refine ⟨1651619121233399460802583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1101079414155599640535055 1651619121233399460802583)
            ·
              refine ⟨2477428681850099191203875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1651619121233399460802583 2477428681850099191203875)
              ·
                refine ⟨3716143022775148786805813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2477428681850099191203875 3716143022775148786805813)
                ·
                  refine ⟨348388408385170198763045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3716143022775148786805813 348388408385170198763045)
                  ·
                    rfl

theorem cell21_1526589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_1526589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1526589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1526589 prefixEnd_1526589 := by exact prefixLift 1526589
  have htrace : WordTrace (prefixWord ++ tailWord_1526589) baseStart_1526589 baseEnd_1526589 := by
    simpa [prefixWord, tailWord_1526589, baseEnd_1526589] using wordTrace_append hprefix tailTrace_1526589
  have hstable : (prefixWord ++ tailWord_1526589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526589).length < 2 ^ (prefixWord ++ tailWord_1526589).sum := by decide
  have hdescent : baseEnd_1526589 < baseStart_1526589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526735 : List Nat := [1, 1, 2, 1, 1, 7, 1, 7]
def baseStart_1526735 : Nat := 118140960795 + 1526735 * 2 ^ 59
def prefixEnd_1526735 : Nat := 4983230072969 + 3 ^ 40 * 1526735 * 2
def baseEnd_1526735 : Nat := 116140575858102129776471

theorem tailTrace_1526735 : CollatzResearch.WordTrace tailWord_1526735 prefixEnd_1526735 116140575858102129776471 := by
  unfold tailWord_1526735
  simp only [CollatzResearch.WordTrace]
  refine ⟨55684600123907315424093659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37123066749271543616062439 55684600123907315424093659)
  ·
    refine ⟨83526900185860973136140489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55684600123907315424093659 83526900185860973136140489)
    ·
      refine ⟨62645175139395729852105367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83526900185860973136140489 62645175139395729852105367)
      ·
        refine ⟨93967762709093594778158051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62645175139395729852105367 93967762709093594778158051)
        ·
          refine ⟨140951644063640392167237077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93967762709093594778158051 140951644063640392167237077)
          ·
            refine ⟨3303554157741571691419619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 140951644063640392167237077 3303554157741571691419619)
            ·
              refine ⟨4955331236612357537129429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3303554157741571691419619 4955331236612357537129429)
              ·
                refine ⟨116140575858102129776471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4955331236612357537129429 116140575858102129776471)
                ·
                  rfl

theorem cell21_1526735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 7].length) (baseStart_1526735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1526735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1526735 prefixEnd_1526735 := by exact prefixLift 1526735
  have htrace : WordTrace (prefixWord ++ tailWord_1526735) baseStart_1526735 baseEnd_1526735 := by
    simpa [prefixWord, tailWord_1526735, baseEnd_1526735] using wordTrace_append hprefix tailTrace_1526735
  have hstable : (prefixWord ++ tailWord_1526735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526735).length < 2 ^ (prefixWord ++ tailWord_1526735).sum := by decide
  have hdescent : baseEnd_1526735 < baseStart_1526735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526741 : List Nat := [1, 3, 2, 3, 3, 2, 1, 3, 3]
def baseStart_1526741 : Nat := 118140960795 + 1526741 * 2 ^ 59
def prefixEnd_1526741 : Nat := 4983230072969 + 3 ^ 40 * 1526741 * 2
def baseEnd_1526741 : Nat := 348423096856051712229401

theorem tailTrace_1526741 : CollatzResearch.WordTrace tailWord_1526741 prefixEnd_1526741 348423096856051712229401 := by
  unfold tailWord_1526741
  simp only [CollatzResearch.WordTrace]
  refine ⟨55684818961885578448812077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37123212641257052299208051 55684818961885578448812077)
  ·
    refine ⟨20881807110707091918304529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55684818961885578448812077 20881807110707091918304529)
    ·
      refine ⟨15661355333030318938728397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20881807110707091918304529 15661355333030318938728397)
      ·
        refine ⟨5873008249886369602023149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15661355333030318938728397 5873008249886369602023149)
        ·
          refine ⟨2202378093707388600758681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5873008249886369602023149 2202378093707388600758681)
          ·
            refine ⟨1651783570280541450569011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2202378093707388600758681 1651783570280541450569011)
            ·
              refine ⟨2477675355420812175853517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1651783570280541450569011 2477675355420812175853517)
              ·
                refine ⟨929128258282804565945069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2477675355420812175853517 929128258282804565945069)
                ·
                  refine ⟨348423096856051712229401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 929128258282804565945069 348423096856051712229401)
                  ·
                    rfl

theorem cell21_1526741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3, 3].length) (baseStart_1526741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1526741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1526741 prefixEnd_1526741 := by exact prefixLift 1526741
  have htrace : WordTrace (prefixWord ++ tailWord_1526741) baseStart_1526741 baseEnd_1526741 := by
    simpa [prefixWord, tailWord_1526741, baseEnd_1526741] using wordTrace_append hprefix tailTrace_1526741
  have hstable : (prefixWord ++ tailWord_1526741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526741).length < 2 ^ (prefixWord ++ tailWord_1526741).sum := by decide
  have hdescent : baseEnd_1526741 < baseStart_1526741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526817 : List Nat := [1, 2, 3, 2, 3, 3, 2, 2, 3]
def baseStart_1526817 : Nat := 118140960795 + 1526817 * 2 ^ 59
def prefixEnd_1526817 : Nat := 4983230072969 + 3 ^ 40 * 1526817 * 2
def baseEnd_1526817 : Nat := 348440441091492468962579

theorem tailTrace_1526817 : CollatzResearch.WordTrace tailWord_1526817 prefixEnd_1526817 348440441091492468962579 := by
  unfold tailWord_1526817
  simp only [CollatzResearch.WordTrace]
  refine ⟨55687590909610243428578705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37125060606406828952385803 55687590909610243428578705)
  ·
    refine ⟨41765693182207682571434029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55687590909610243428578705 41765693182207682571434029)
    ·
      refine ⟨15662134943327880964287761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41765693182207682571434029 15662134943327880964287761)
      ·
        refine ⟨11746601207495910723215821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15662134943327880964287761 11746601207495910723215821)
        ·
          refine ⟨4404975452810966521205933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11746601207495910723215821 4404975452810966521205933)
          ·
            refine ⟨1651865794804112445452225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4404975452810966521205933 1651865794804112445452225)
            ·
              refine ⟨1238899346103084334089169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1651865794804112445452225 1238899346103084334089169)
              ·
                refine ⟨929174509577313250566877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1238899346103084334089169 929174509577313250566877)
                ·
                  refine ⟨348440441091492468962579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 929174509577313250566877 348440441091492468962579)
                  ·
                    rfl

theorem cell21_1526817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2, 3].length) (baseStart_1526817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1526817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1526817 prefixEnd_1526817 := by exact prefixLift 1526817
  have htrace : WordTrace (prefixWord ++ tailWord_1526817) baseStart_1526817 baseEnd_1526817 := by
    simpa [prefixWord, tailWord_1526817, baseEnd_1526817] using wordTrace_append hprefix tailTrace_1526817
  have hstable : (prefixWord ++ tailWord_1526817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526817).length < 2 ^ (prefixWord ++ tailWord_1526817).sum := by decide
  have hdescent : baseEnd_1526817 < baseStart_1526817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526856 : List Nat := [2, 1, 3, 1, 1, 1, 4, 2, 6]
def baseStart_1526856 : Nat := 118140960795 + 1526856 * 2 ^ 59
def prefixEnd_1526856 : Nat := 4983230072969 + 3 ^ 40 * 1526856 * 2
def baseEnd_1526856 : Nat := 348449341422837067812499

theorem tailTrace_1526856 : CollatzResearch.WordTrace tailWord_1526856 prefixEnd_1526856 348449341422837067812499 := by
  unfold tailWord_1526856
  simp only [CollatzResearch.WordTrace]
  refine ⟨27844506678234476544624211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37126008904312635392832281 27844506678234476544624211)
  ·
    refine ⟨41766760017351714816936317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27844506678234476544624211 41766760017351714816936317)
    ·
      refine ⟨15662535006506893056351119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41766760017351714816936317 15662535006506893056351119)
      ·
        refine ⟨23493802509760339584526679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15662535006506893056351119 23493802509760339584526679)
        ·
          refine ⟨35240703764640509376790019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23493802509760339584526679 35240703764640509376790019)
          ·
            refine ⟨52861055646960764065185029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35240703764640509376790019 52861055646960764065185029)
            ·
              refine ⟨9911447933805143262222193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52861055646960764065185029 9911447933805143262222193)
              ·
                refine ⟨7433585950353857446666645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9911447933805143262222193 7433585950353857446666645)
                ·
                  refine ⟨348449341422837067812499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7433585950353857446666645 348449341422837067812499)
                  ·
                    rfl

theorem cell21_1526856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 6].length) (baseStart_1526856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1526856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1526856 prefixEnd_1526856 := by exact prefixLift 1526856
  have htrace : WordTrace (prefixWord ++ tailWord_1526856) baseStart_1526856 baseEnd_1526856 := by
    simpa [prefixWord, tailWord_1526856, baseEnd_1526856] using wordTrace_append hprefix tailTrace_1526856
  have hstable : (prefixWord ++ tailWord_1526856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526856).length < 2 ^ (prefixWord ++ tailWord_1526856).sum := by decide
  have hdescent : baseEnd_1526856 < baseStart_1526856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526935 : List Nat := [1, 1, 3, 3, 3, 3, 1, 1, 5]
def baseStart_1526935 : Nat := 118140960795 + 1526935 * 2 ^ 59
def prefixEnd_1526935 : Nat := 4983230072969 + 3 ^ 40 * 1526935 * 2
def baseEnd_1526935 : Nat := 348467370299150485995671

theorem tailTrace_1526935 : CollatzResearch.WordTrace tailWord_1526935 prefixEnd_1526935 348467370299150485995671 := by
  unfold tailWord_1526935
  simp only [CollatzResearch.WordTrace]
  refine ⟨55691894723182749581374259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37127929815455166387582839 55691894723182749581374259)
  ·
    refine ⟨83537842084774124372061389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55691894723182749581374259 83537842084774124372061389)
    ·
      refine ⟨31326690781790296639523021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83537842084774124372061389 31326690781790296639523021)
      ·
        refine ⟨11747509043171361239821133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31326690781790296639523021 11747509043171361239821133)
        ·
          refine ⟨4405315891189260464932925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11747509043171361239821133 4405315891189260464932925)
          ·
            refine ⟨1651993459195972674349847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4405315891189260464932925 1651993459195972674349847)
            ·
              refine ⟨2477990188793959011524771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1651993459195972674349847 2477990188793959011524771)
              ·
                refine ⟨3716985283190938517287157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2477990188793959011524771 3716985283190938517287157)
                ·
                  refine ⟨348467370299150485995671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3716985283190938517287157 348467370299150485995671)
                  ·
                    rfl

theorem cell21_1526935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 5].length) (baseStart_1526935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1526935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1526935 prefixEnd_1526935 := by exact prefixLift 1526935
  have htrace : WordTrace (prefixWord ++ tailWord_1526935) baseStart_1526935 baseEnd_1526935 := by
    simpa [prefixWord, tailWord_1526935, baseEnd_1526935] using wordTrace_append hprefix tailTrace_1526935
  have hstable : (prefixWord ++ tailWord_1526935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526935).length < 2 ^ (prefixWord ++ tailWord_1526935).sum := by decide
  have hdescent : baseEnd_1526935 < baseStart_1526935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526949 : List Nat := [1, 3, 1, 2, 1, 5, 1, 3, 4]
def baseStart_1526949 : Nat := 118140960795 + 1526949 * 2 ^ 59
def prefixEnd_1526949 : Nat := 4983230072969 + 3 ^ 40 * 1526949 * 2
def baseEnd_1526949 : Nat := 348470565289889572762309

theorem tailTrace_1526949 : CollatzResearch.WordTrace tailWord_1526949 prefixEnd_1526949 348470565289889572762309 := by
  unfold tailWord_1526949
  simp only [CollatzResearch.WordTrace]
  refine ⟨55692405345132029972383901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37128270230088019981589267 55692405345132029972383901)
  ·
    refine ⟨20884652004424511239643963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55692405345132029972383901 20884652004424511239643963)
    ·
      refine ⟨31326978006636766859465945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20884652004424511239643963 31326978006636766859465945)
      ·
        refine ⟨23495233504977575144599459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31326978006636766859465945 23495233504977575144599459)
        ·
          refine ⟨35242850257466362716899189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23495233504977575144599459 35242850257466362716899189)
          ·
            refine ⟨3304017211637471504709299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35242850257466362716899189 3304017211637471504709299)
            ·
              refine ⟨4956025817456207257063949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3304017211637471504709299 4956025817456207257063949)
              ·
                refine ⟨1858509681546077721398981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4956025817456207257063949 1858509681546077721398981)
                ·
                  refine ⟨348470565289889572762309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1858509681546077721398981 348470565289889572762309)
                  ·
                    rfl

theorem cell21_1526949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_1526949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1526949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1526949 prefixEnd_1526949 := by exact prefixLift 1526949
  have htrace : WordTrace (prefixWord ++ tailWord_1526949) baseStart_1526949 baseEnd_1526949 := by
    simpa [prefixWord, tailWord_1526949, baseEnd_1526949] using wordTrace_append hprefix tailTrace_1526949
  have hstable : (prefixWord ++ tailWord_1526949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526949).length < 2 ^ (prefixWord ++ tailWord_1526949).sum := by decide
  have hdescent : baseEnd_1526949 < baseStart_1526949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526980 : List Nat := [2, 3, 3, 1, 4, 8]
def baseStart_1526980 : Nat := 118140960795 + 1526980 * 2 ^ 59
def prefixEnd_1526980 : Nat := 4983230072969 + 3 ^ 40 * 1526980 * 2
def baseEnd_1526980 : Nat := 12906579256008903990577

theorem tailTrace_1526980 : CollatzResearch.WordTrace tailWord_1526980 prefixEnd_1526980 12906579256008903990577 := by
  unfold tailWord_1526980
  simp only [CollatzResearch.WordTrace]
  refine ⟨27846768004009861133381197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37129024005346481511174929 27846768004009861133381197)
  ·
    refine ⟨10442538001503697925017949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27846768004009861133381197 10442538001503697925017949)
    ·
      refine ⟨3915951750563886721881731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10442538001503697925017949 3915951750563886721881731)
      ·
        refine ⟨5873927625845830082822597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3915951750563886721881731 5873927625845830082822597)
        ·
          refine ⟨1101361429846093140529237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5873927625845830082822597 1101361429846093140529237)
          ·
            refine ⟨12906579256008903990577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1101361429846093140529237 12906579256008903990577)
            ·
              rfl

theorem cell21_1526980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 8].length) (baseStart_1526980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1526980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1526980 prefixEnd_1526980 := by exact prefixLift 1526980
  have htrace : WordTrace (prefixWord ++ tailWord_1526980) baseStart_1526980 baseEnd_1526980 := by
    simpa [prefixWord, tailWord_1526980, baseEnd_1526980] using wordTrace_append hprefix tailTrace_1526980
  have hstable : (prefixWord ++ tailWord_1526980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526980).length < 2 ^ (prefixWord ++ tailWord_1526980).sum := by decide
  have hdescent : baseEnd_1526980 < baseStart_1526980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526994 : List Nat := [3, 2, 2, 2, 1, 1, 2, 3, 5]
def baseStart_1526994 : Nat := 118140960795 + 1526994 * 2 ^ 59
def prefixEnd_1526994 : Nat := 4983230072969 + 3 ^ 40 * 1526994 * 2
def baseEnd_1526994 : Nat := 348480834902979494512217

theorem tailTrace_1526994 : CollatzResearch.WordTrace tailWord_1526994 prefixEnd_1526994 348480834902979494512217 := by
  unfold tailWord_1526994
  simp only [CollatzResearch.WordTrace]
  refine ⟨13923511657492250664443009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37129364419979335105181357 13923511657492250664443009)
  ·
    refine ⟨10442633743119187998332257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13923511657492250664443009 10442633743119187998332257)
    ·
      refine ⟨7831975307339390998749193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10442633743119187998332257 7831975307339390998749193)
      ·
        refine ⟨5873981480504543249061895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7831975307339390998749193 5873981480504543249061895)
        ·
          refine ⟨8810972220756814873592843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5873981480504543249061895 8810972220756814873592843)
          ·
            refine ⟨13216458331135222310389265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8810972220756814873592843 13216458331135222310389265)
            ·
              refine ⟨9912343748351416732791949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13216458331135222310389265 9912343748351416732791949)
              ·
                refine ⟨3717128905631781274796981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9912343748351416732791949 3717128905631781274796981)
                ·
                  refine ⟨348480834902979494512217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3717128905631781274796981 348480834902979494512217)
                  ·
                    rfl

theorem cell21_1526994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_1526994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1526994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1526994 prefixEnd_1526994 := by exact prefixLift 1526994
  have htrace : WordTrace (prefixWord ++ tailWord_1526994) baseStart_1526994 baseEnd_1526994 := by
    simpa [prefixWord, tailWord_1526994, baseEnd_1526994] using wordTrace_append hprefix tailTrace_1526994
  have hstable : (prefixWord ++ tailWord_1526994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526994).length < 2 ^ (prefixWord ++ tailWord_1526994).sum := by decide
  have hdescent : baseEnd_1526994 < baseStart_1526994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527042 : List Nat := [3, 4, 1, 1, 3, 1, 1, 1, 6]
def baseStart_1527042 : Nat := 118140960795 + 1527042 * 2 ^ 59
def prefixEnd_1527042 : Nat := 4983230072969 + 3 ^ 40 * 1527042 * 2
def baseEnd_1527042 : Nat := 348491789156942077712119

theorem tailTrace_1527042 : CollatzResearch.WordTrace tailWord_1527042 prefixEnd_1527042 348491789156942077712119 := by
  unfold tailWord_1527042
  simp only [CollatzResearch.WordTrace]
  refine ⟨13923949333448776713879845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37130531555863404570346253 13923949333448776713879845)
  ·
    refine ⟨2610740500021645633852471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13923949333448776713879845 2610740500021645633852471)
    ·
      refine ⟨3916110750032468450778707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2610740500021645633852471 3916110750032468450778707)
      ·
        refine ⟨5874166125048702676168061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3916110750032468450778707 5874166125048702676168061)
        ·
          refine ⟨2202812296893263503563023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5874166125048702676168061 2202812296893263503563023)
          ·
            refine ⟨3304218445339895255344535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2202812296893263503563023 3304218445339895255344535)
            ·
              refine ⟨4956327668009842883016803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3304218445339895255344535 4956327668009842883016803)
              ·
                refine ⟨7434491502014764324525205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4956327668009842883016803 7434491502014764324525205)
                ·
                  refine ⟨348491789156942077712119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7434491502014764324525205 348491789156942077712119)
                  ·
                    rfl

theorem cell21_1527042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_1527042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1527042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1527042 prefixEnd_1527042 := by exact prefixLift 1527042
  have htrace : WordTrace (prefixWord ++ tailWord_1527042) baseStart_1527042 baseEnd_1527042 := by
    simpa [prefixWord, tailWord_1527042, baseEnd_1527042] using wordTrace_append hprefix tailTrace_1527042
  have hstable : (prefixWord ++ tailWord_1527042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527042).length < 2 ^ (prefixWord ++ tailWord_1527042).sum := by decide
  have hdescent : baseEnd_1527042 < baseStart_1527042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527110 : List Nat := [6, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_1527110 : Nat := 118140960795 + 1527110 * 2 ^ 59
def prefixEnd_1527110 : Nat := 4983230072969 + 3 ^ 40 * 1527110 * 2
def baseEnd_1527110 : Nat := 348507307683389070578647

theorem tailTrace_1527110 : CollatzResearch.WordTrace tailWord_1527110 prefixEnd_1527110 348507307683389070578647 := by
  unfold tailWord_1527110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1740571171798398577156087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37132184998365836312663189 1740571171798398577156087)
  ·
    refine ⟨2610856757697597865734131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1740571171798398577156087 2610856757697597865734131)
    ·
      refine ⟨3916285136546396798601197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2610856757697597865734131 3916285136546396798601197)
      ·
        refine ⟨1468606926204898799475449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3916285136546396798601197 1468606926204898799475449)
        ·
          refine ⟨1101455194653674099606587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1468606926204898799475449 1101455194653674099606587)
          ·
            refine ⟨1652182791980511149409881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1101455194653674099606587 1652182791980511149409881)
            ·
              refine ⟨1239137093985383362057411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1652182791980511149409881 1239137093985383362057411)
              ·
                refine ⟨1858705640978075043086117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1239137093985383362057411 1858705640978075043086117)
                ·
                  refine ⟨348507307683389070578647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1858705640978075043086117 348507307683389070578647)
                  ·
                    rfl

theorem cell21_1527110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_1527110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1527110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1527110 prefixEnd_1527110 := by exact prefixLift 1527110
  have htrace : WordTrace (prefixWord ++ tailWord_1527110) baseStart_1527110 baseEnd_1527110 := by
    simpa [prefixWord, tailWord_1527110, baseEnd_1527110] using wordTrace_append hprefix tailTrace_1527110
  have hstable : (prefixWord ++ tailWord_1527110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527110).length < 2 ^ (prefixWord ++ tailWord_1527110).sum := by decide
  have hdescent : baseEnd_1527110 < baseStart_1527110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527129 : List Nat := [1, 2, 1, 2, 2, 2, 2, 4, 5]
def baseStart_1527129 : Nat := 118140960795 + 1527129 * 2 ^ 59
def prefixEnd_1527129 : Nat := 4983230072969 + 3 ^ 40 * 1527129 * 2
def baseEnd_1527129 : Nat := 348511643742249259761941

theorem tailTrace_1527129 : CollatzResearch.WordTrace tailWord_1527129 prefixEnd_1527129 348511643742249259761941 := by
  unfold tailWord_1527129
  simp only [CollatzResearch.WordTrace]
  refine ⟨55698970484479920713936441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37132646989653280475957627 55698970484479920713936441)
  ·
    refine ⟨41774227863359940535452331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55698970484479920713936441 41774227863359940535452331)
    ·
      refine ⟨62661341795039910803178497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41774227863359940535452331 62661341795039910803178497)
      ·
        refine ⟨46996006346279933102383873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62661341795039910803178497 46996006346279933102383873)
        ·
          refine ⟨35247004759709949826787905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46996006346279933102383873 35247004759709949826787905)
          ·
            refine ⟨26435253569782462370090929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35247004759709949826787905 26435253569782462370090929)
            ·
              refine ⟨19826440177336846777568197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26435253569782462370090929 19826440177336846777568197)
              ·
                refine ⟨3717457533250658770794037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19826440177336846777568197 3717457533250658770794037)
                ·
                  refine ⟨348511643742249259761941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3717457533250658770794037 348511643742249259761941)
                  ·
                    rfl

theorem cell21_1527129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 5].length) (baseStart_1527129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1527129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1527129 prefixEnd_1527129 := by exact prefixLift 1527129
  have htrace : WordTrace (prefixWord ++ tailWord_1527129) baseStart_1527129 baseEnd_1527129 := by
    simpa [prefixWord, tailWord_1527129, baseEnd_1527129] using wordTrace_append hprefix tailTrace_1527129
  have hstable : (prefixWord ++ tailWord_1527129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527129).length < 2 ^ (prefixWord ++ tailWord_1527129).sum := by decide
  have hdescent : baseEnd_1527129 < baseStart_1527129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527166 : List Nat := [4, 2, 3, 2, 1, 2, 1, 6]
def baseStart_1527166 : Nat := 118140960795 + 1527166 * 2 ^ 59
def prefixEnd_1527166 : Nat := 4983230072969 + 3 ^ 40 * 1527166 * 2
def baseEnd_1527166 : Nat := 116173362548781805881733

theorem tailTrace_1527166 : CollatzResearch.WordTrace tailWord_1527166 prefixEnd_1527166 116173362548781805881733 := by
  unfold tailWord_1527166
  simp only [CollatzResearch.WordTrace]
  refine ⟨6962539998168234504129169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37133546656897250688688901 6962539998168234504129169)
  ·
    refine ⟨5221904998626175878096877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6962539998168234504129169 5221904998626175878096877)
    ·
      refine ⟨1958214374484815954286329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5221904998626175878096877 1958214374484815954286329)
      ·
        refine ⟨1468660780863611965714747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1958214374484815954286329 1468660780863611965714747)
        ·
          refine ⟨2202991171295417948572121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1468660780863611965714747 2202991171295417948572121)
          ·
            refine ⟨1652243378471563461429091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2202991171295417948572121 1652243378471563461429091)
            ·
              refine ⟨2478365067707345192143637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1652243378471563461429091 2478365067707345192143637)
              ·
                refine ⟨116173362548781805881733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2478365067707345192143637 116173362548781805881733)
                ·
                  rfl

theorem cell21_1527166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_1527166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1527166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1527166 prefixEnd_1527166 := by exact prefixLift 1527166
  have htrace : WordTrace (prefixWord ++ tailWord_1527166) baseStart_1527166 baseEnd_1527166 := by
    simpa [prefixWord, tailWord_1527166, baseEnd_1527166] using wordTrace_append hprefix tailTrace_1527166
  have hstable : (prefixWord ++ tailWord_1527166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527166).length < 2 ^ (prefixWord ++ tailWord_1527166).sum := by decide
  have hdescent : baseEnd_1527166 < baseStart_1527166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527208 : List Nat := [2, 1, 6, 1, 2, 1, 8]
def baseStart_1527208 : Nat := 118140960795 + 1527208 * 2 ^ 59
def prefixEnd_1527208 : Nat := 4983230072969 + 3 ^ 40 * 1527208 * 2
def baseEnd_1527208 : Nat := 38725519179840297549457

theorem tailTrace_1527208 : CollatzResearch.WordTrace tailWord_1527208 prefixEnd_1527208 38725519179840297549457 := by
  unfold tailWord_1527208
  simp only [CollatzResearch.WordTrace]
  refine ⟨27850925925596858603031139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37134567900795811470708185 27850925925596858603031139)
  ·
    refine ⟨41776388888395287904546709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27850925925596858603031139 41776388888395287904546709)
    ·
      refine ⟨1958268229143529120525627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41776388888395287904546709 1958268229143529120525627)
      ·
        refine ⟨2937402343715293680788441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1958268229143529120525627 2937402343715293680788441)
        ·
          refine ⟨2203051757786470260591331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2937402343715293680788441 2203051757786470260591331)
          ·
            refine ⟨3304577636679705390886997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2203051757786470260591331 3304577636679705390886997)
            ·
              refine ⟨38725519179840297549457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3304577636679705390886997 38725519179840297549457)
              ·
                rfl

theorem cell21_1527208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 8].length) (baseStart_1527208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1527208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1527208 prefixEnd_1527208 := by exact prefixLift 1527208
  have htrace : WordTrace (prefixWord ++ tailWord_1527208) baseStart_1527208 baseEnd_1527208 := by
    simpa [prefixWord, tailWord_1527208, baseEnd_1527208] using wordTrace_append hprefix tailTrace_1527208
  have hstable : (prefixWord ++ tailWord_1527208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527208).length < 2 ^ (prefixWord ++ tailWord_1527208).sum := by decide
  have hdescent : baseEnd_1527208 < baseStart_1527208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527267 : List Nat := [1, 1, 1, 6, 2, 3, 7]
def baseStart_1527267 : Nat := 118140960795 + 1527267 * 2 ^ 59
def prefixEnd_1527267 : Nat := 4983230072969 + 3 ^ 40 * 1527267 * 2
def baseEnd_1527267 : Nat := 38727015246932409606851

theorem tailTrace_1527267 : CollatzResearch.WordTrace tailWord_1527267 prefixEnd_1527267 38727015246932409606851 := by
  unfold tailWord_1527267
  simp only [CollatzResearch.WordTrace]
  refine ⟨55704003757979970282460055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37136002505319980188306703 55704003757979970282460055)
  ·
    refine ⟨83556005636969955423690083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55704003757979970282460055 83556005636969955423690083)
    ·
      refine ⟨125334008455454933135535125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83556005636969955423690083 125334008455454933135535125)
      ·
        refine ⟨5875031646349449990728209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 125334008455454933135535125 5875031646349449990728209)
        ·
          refine ⟨4406273734762087493046157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5875031646349449990728209 4406273734762087493046157)
          ·
            refine ⟨1652352650535782809892309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4406273734762087493046157 1652352650535782809892309)
            ·
              refine ⟨38727015246932409606851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1652352650535782809892309 38727015246932409606851)
              ·
                rfl

theorem cell21_1527267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 7].length) (baseStart_1527267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1527267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1527267 prefixEnd_1527267 := by exact prefixLift 1527267
  have htrace : WordTrace (prefixWord ++ tailWord_1527267) baseStart_1527267 baseEnd_1527267 := by
    simpa [prefixWord, tailWord_1527267, baseEnd_1527267] using wordTrace_append hprefix tailTrace_1527267
  have hstable : (prefixWord ++ tailWord_1527267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527267).length < 2 ^ (prefixWord ++ tailWord_1527267).sum := by decide
  have hdescent : baseEnd_1527267 < baseStart_1527267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527295 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 8]
def baseStart_1527295 : Nat := 118140960795 + 1527295 * 2 ^ 59
def prefixEnd_1527295 : Nat := 4983230072969 + 3 ^ 40 * 1527295 * 2
def baseEnd_1527295 : Nat := 348549527203869859994935

theorem tailTrace_1527295 : CollatzResearch.WordTrace tailWord_1527295 prefixEnd_1527295 348549527203869859994935 := by
  unfold tailWord_1527295
  simp only [CollatzResearch.WordTrace]
  refine ⟨55705025001878531064479339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37136683334585687376319559 55705025001878531064479339)
  ·
    refine ⟨83557537502817796596719009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55705025001878531064479339 83557537502817796596719009)
    ·
      refine ⟨62668153127113347447539257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83557537502817796596719009 62668153127113347447539257)
      ·
        refine ⟨47001114845335010585654443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62668153127113347447539257 47001114845335010585654443)
        ·
          refine ⟨70501672268002515878481665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47001114845335010585654443 70501672268002515878481665)
          ·
            refine ⟨52876254201001886908861249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70501672268002515878481665 52876254201001886908861249)
            ·
              refine ⟨39657190650751415181645937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52876254201001886908861249 39657190650751415181645937)
              ·
                refine ⟨29742892988063561386234453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39657190650751415181645937 29742892988063561386234453)
                ·
                  refine ⟨348549527203869859994935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29742892988063561386234453 348549527203869859994935)
                  ·
                    rfl

theorem cell21_1527295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 8].length) (baseStart_1527295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1527295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1527295 prefixEnd_1527295 := by exact prefixLift 1527295
  have htrace : WordTrace (prefixWord ++ tailWord_1527295) baseStart_1527295 baseEnd_1527295 := by
    simpa [prefixWord, tailWord_1527295, baseEnd_1527295] using wordTrace_append hprefix tailTrace_1527295
  have hstable : (prefixWord ++ tailWord_1527295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527295).length < 2 ^ (prefixWord ++ tailWord_1527295).sum := by decide
  have hdescent : baseEnd_1527295 < baseStart_1527295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527329 : List Nat := [1, 2, 3, 2, 2, 3, 2, 2, 4]
def baseStart_1527329 : Nat := 118140960795 + 1527329 * 2 ^ 59
def prefixEnd_1527329 : Nat := 4983230072969 + 3 ^ 40 * 1527329 * 2
def baseEnd_1527329 : Nat := 348557286467093356428199

theorem tailTrace_1527329 : CollatzResearch.WordTrace tailWord_1527329 prefixEnd_1527329 348557286467093356428199 := by
  unfold tailWord_1527329
  simp only [CollatzResearch.WordTrace]
  refine ⟨55706265083755354871217041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37137510055836903247478027 55706265083755354871217041)
  ·
    refine ⟨41779698812816516153412781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55706265083755354871217041 41779698812816516153412781)
    ·
      refine ⟨15667387054806193557529793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41779698812816516153412781 15667387054806193557529793)
      ·
        refine ⟨11750540291104645168147345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15667387054806193557529793 11750540291104645168147345)
        ·
          refine ⟨8812905218328483876110509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11750540291104645168147345 8812905218328483876110509)
          ·
            refine ⟨3304839456873181453541441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8812905218328483876110509 3304839456873181453541441)
            ·
              refine ⟨2478629592654886090156081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3304839456873181453541441 2478629592654886090156081)
              ·
                refine ⟨1858972194491164567617061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2478629592654886090156081 1858972194491164567617061)
                ·
                  refine ⟨348557286467093356428199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1858972194491164567617061 348557286467093356428199)
                  ·
                    rfl

theorem cell21_1527329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 4].length) (baseStart_1527329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1527329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1527329 prefixEnd_1527329 := by exact prefixLift 1527329
  have htrace : WordTrace (prefixWord ++ tailWord_1527329) baseStart_1527329 baseEnd_1527329 := by
    simpa [prefixWord, tailWord_1527329, baseEnd_1527329] using wordTrace_append hprefix tailTrace_1527329
  have hstable : (prefixWord ++ tailWord_1527329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527329).length < 2 ^ (prefixWord ++ tailWord_1527329).sum := by decide
  have hdescent : baseEnd_1527329 < baseStart_1527329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527371 : List Nat := [1, 1, 1, 1, 3, 1, 3, 4, 6]
def baseStart_1527371 : Nat := 118140960795 + 1527371 * 2 ^ 59
def prefixEnd_1527371 : Nat := 4983230072969 + 3 ^ 40 * 1527371 * 2
def baseEnd_1527371 : Nat := 348566871439310616728113

theorem tailTrace_1527371 : CollatzResearch.WordTrace tailWord_1527371 prefixEnd_1527371 348566871439310616728113 := by
  unfold tailWord_1527371
  simp only [CollatzResearch.WordTrace]
  refine ⟨55707796949603196044245967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37138531299735464029497311 55707796949603196044245967)
  ·
    refine ⟨83561695424404794066368951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55707796949603196044245967 83561695424404794066368951)
    ·
      refine ⟨125342543136607191099553427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83561695424404794066368951 125342543136607191099553427)
      ·
        refine ⟨188013814704910786649330141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125342543136607191099553427 188013814704910786649330141)
        ·
          refine ⟨70505180514341544993498803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188013814704910786649330141 70505180514341544993498803)
          ·
            refine ⟨105757770771512317490248205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70505180514341544993498803 105757770771512317490248205)
            ·
              refine ⟨39659164039317119058843077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105757770771512317490248205 39659164039317119058843077)
              ·
                refine ⟨7436093257371959823533077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39659164039317119058843077 7436093257371959823533077)
                ·
                  refine ⟨348566871439310616728113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7436093257371959823533077 348566871439310616728113)
                  ·
                    rfl

theorem cell21_1527371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 6].length) (baseStart_1527371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1527371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1527371 prefixEnd_1527371 := by exact prefixLift 1527371
  have htrace : WordTrace (prefixWord ++ tailWord_1527371) baseStart_1527371 baseEnd_1527371 := by
    simpa [prefixWord, tailWord_1527371, baseEnd_1527371] using wordTrace_append hprefix tailTrace_1527371
  have hstable : (prefixWord ++ tailWord_1527371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527371).length < 2 ^ (prefixWord ++ tailWord_1527371).sum := by decide
  have hdescent : baseEnd_1527371 < baseStart_1527371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527501 : List Nat := [1, 6, 2, 1, 1, 1, 4, 2, 3]
def baseStart_1527501 : Nat := 118140960795 + 1527501 * 2 ^ 59
def prefixEnd_1527501 : Nat := 4983230072969 + 3 ^ 40 * 1527501 * 2
def baseEnd_1527501 : Nat := 348596539210459279561181

theorem tailTrace_1527501 : CollatzResearch.WordTrace tailWord_1527501 prefixEnd_1527501 348596539210459279561181 := by
  unfold tailWord_1527501
  simp only [CollatzResearch.WordTrace]
  refine ⟨55712538439132228246478357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37141692292754818830985571 55712538439132228246478357)
  ·
    refine ⟨2611525239334323199053673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55712538439132228246478357 2611525239334323199053673)
    ·
      refine ⟨1958643929500742399290255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2611525239334323199053673 1958643929500742399290255)
      ·
        refine ⟨2937965894251113598935383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1958643929500742399290255 2937965894251113598935383)
        ·
          refine ⟨4406948841376670398403075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2937965894251113598935383 4406948841376670398403075)
          ·
            refine ⟨6610423262065005597604613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4406948841376670398403075 6610423262065005597604613)
            ·
              refine ⟨1239454361637188549550865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6610423262065005597604613 1239454361637188549550865)
              ·
                refine ⟨929590771227891412163149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1239454361637188549550865 929590771227891412163149)
                ·
                  refine ⟨348596539210459279561181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 929590771227891412163149 348596539210459279561181)
                  ·
                    rfl

theorem cell21_1527501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_1527501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1527501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1527501 prefixEnd_1527501 := by exact prefixLift 1527501
  have htrace : WordTrace (prefixWord ++ tailWord_1527501) baseStart_1527501 baseEnd_1527501 := by
    simpa [prefixWord, tailWord_1527501, baseEnd_1527501] using wordTrace_append hprefix tailTrace_1527501
  have hstable : (prefixWord ++ tailWord_1527501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527501).length < 2 ^ (prefixWord ++ tailWord_1527501).sum := by decide
  have hdescent : baseEnd_1527501 < baseStart_1527501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527585 : List Nat := [1, 2, 3, 2, 1, 3, 2, 2, 5]
def baseStart_1527585 : Nat := 118140960795 + 1527585 * 2 ^ 59
def prefixEnd_1527585 : Nat := 4983230072969 + 3 ^ 40 * 1527585 * 2
def baseEnd_1527585 : Nat := 348615709154893800161009

theorem tailTrace_1527585 : CollatzResearch.WordTrace tailWord_1527585 prefixEnd_1527585 348615709154893800161009 := by
  unfold tailWord_1527585
  simp only [CollatzResearch.WordTrace]
  refine ⟨55715602170827910592536209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37143734780551940395024139 55715602170827910592536209)
  ·
    refine ⟨41786701628120932944402157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55715602170827910592536209 41786701628120932944402157)
    ·
      refine ⟨15670013110545349854150809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41786701628120932944402157 15670013110545349854150809)
      ·
        refine ⟨11752509832909012390613107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15670013110545349854150809 11752509832909012390613107)
        ·
          refine ⟨17628764749363518585919661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11752509832909012390613107 17628764749363518585919661)
          ·
            refine ⟨6610786781011319469719873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17628764749363518585919661 6610786781011319469719873)
            ·
              refine ⟨4958090085758489602289905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6610786781011319469719873 4958090085758489602289905)
              ·
                refine ⟨3718567564318867201717429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4958090085758489602289905 3718567564318867201717429)
                ·
                  refine ⟨348615709154893800161009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3718567564318867201717429 348615709154893800161009)
                  ·
                    rfl

theorem cell21_1527585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 5].length) (baseStart_1527585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1527585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1527585 prefixEnd_1527585 := by exact prefixLift 1527585
  have htrace : WordTrace (prefixWord ++ tailWord_1527585) baseStart_1527585 baseEnd_1527585 := by
    simpa [prefixWord, tailWord_1527585, baseEnd_1527585] using wordTrace_append hprefix tailTrace_1527585
  have hstable : (prefixWord ++ tailWord_1527585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527585).length < 2 ^ (prefixWord ++ tailWord_1527585).sum := by decide
  have hdescent : baseEnd_1527585 < baseStart_1527585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527588 : List Nat := [2, 3, 1, 3, 2, 3, 2, 5]
def baseStart_1527588 : Nat := 118140960795 + 1527588 * 2 ^ 59
def prefixEnd_1527588 : Nat := 4983230072969 + 3 ^ 40 * 1527588 * 2
def baseEnd_1527588 : Nat := 116205464598588820537001

theorem tailTrace_1527588 : CollatzResearch.WordTrace tailWord_1527588 prefixEnd_1527588 116205464598588820537001 := by
  unfold tailWord_1527588
  simp only [CollatzResearch.WordTrace]
  refine ⟨27857855794908521052447709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37143807726544694736596945 27857855794908521052447709)
  ·
    refine ⟨10446695923090695394667891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27857855794908521052447709 10446695923090695394667891)
    ·
      refine ⟨15670043884636043092001837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10446695923090695394667891 15670043884636043092001837)
      ·
        refine ⟨5876266456738516159500689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15670043884636043092001837 5876266456738516159500689)
        ·
          refine ⟨4407199842553887119625517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5876266456738516159500689 4407199842553887119625517)
          ·
            refine ⟨1652699940957707669859569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4407199842553887119625517 1652699940957707669859569)
            ·
              refine ⟨1239524955718280752394677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1652699940957707669859569 1239524955718280752394677)
              ·
                refine ⟨116205464598588820537001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1239524955718280752394677 116205464598588820537001)
                ·
                  rfl

theorem cell21_1527588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 5].length) (baseStart_1527588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1527588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1527588 prefixEnd_1527588 := by exact prefixLift 1527588
  have htrace : WordTrace (prefixWord ++ tailWord_1527588) baseStart_1527588 baseEnd_1527588 := by
    simpa [prefixWord, tailWord_1527588, baseEnd_1527588] using wordTrace_append hprefix tailTrace_1527588
  have hstable : (prefixWord ++ tailWord_1527588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527588).length < 2 ^ (prefixWord ++ tailWord_1527588).sum := by decide
  have hdescent : baseEnd_1527588 < baseStart_1527588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527619 : List Nat := [1, 1, 1, 3, 1, 6, 3, 2, 3]
def baseStart_1527619 : Nat := 118140960795 + 1527619 * 2 ^ 59
def prefixEnd_1527619 : Nat := 4983230072969 + 3 ^ 40 * 1527619 * 2
def baseEnd_1527619 : Nat := 348623468418117296594273

theorem tailTrace_1527619 : CollatzResearch.WordTrace tailWord_1527619 prefixEnd_1527619 348623468418117296594273 := by
  unfold tailWord_1527619
  simp only [CollatzResearch.WordTrace]
  refine ⟨55716842252704734399273911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37144561501803156266182607 55716842252704734399273911)
  ·
    refine ⟨83575263379057101598910867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55716842252704734399273911 83575263379057101598910867)
    ·
      refine ⟨125362895068585652398366301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83575263379057101598910867 125362895068585652398366301)
      ·
        refine ⟨47011085650719619649387363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125362895068585652398366301 47011085650719619649387363)
        ·
          refine ⟨70516628476079429474081045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47011085650719619649387363 70516628476079429474081045)
          ·
            refine ⟨3305466959816223256597549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70516628476079429474081045 3305466959816223256597549)
            ·
              refine ⟨1239550109931083721224081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3305466959816223256597549 1239550109931083721224081)
              ·
                refine ⟨929662582448312790918061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1239550109931083721224081 929662582448312790918061)
                ·
                  refine ⟨348623468418117296594273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 929662582448312790918061 348623468418117296594273)
                  ·
                    rfl

theorem cell21_1527619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2, 3].length) (baseStart_1527619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1527619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1527619 prefixEnd_1527619 := by exact prefixLift 1527619
  have htrace : WordTrace (prefixWord ++ tailWord_1527619) baseStart_1527619 baseEnd_1527619 := by
    simpa [prefixWord, tailWord_1527619, baseEnd_1527619] using wordTrace_append hprefix tailTrace_1527619
  have hstable : (prefixWord ++ tailWord_1527619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527619).length < 2 ^ (prefixWord ++ tailWord_1527619).sum := by decide
  have hdescent : baseEnd_1527619 < baseStart_1527619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527633 : List Nat := [1, 2, 2, 1, 5, 1, 4, 1, 4]
def baseStart_1527633 : Nat := 118140960795 + 1527633 * 2 ^ 59
def prefixEnd_1527633 : Nat := 4983230072969 + 3 ^ 40 * 1527633 * 2
def baseEnd_1527633 : Nat := 348626663408856383360911

theorem tailTrace_1527633 : CollatzResearch.WordTrace tailWord_1527633 prefixEnd_1527633 348626663408856383360911 := by
  unfold tailWord_1527633
  simp only [CollatzResearch.WordTrace]
  refine ⟨55717352874654014790283553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37144901916436009860189035 55717352874654014790283553)
  ·
    refine ⟨41788014655990511092712665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55717352874654014790283553 41788014655990511092712665)
    ·
      refine ⟨31341010991992883319534499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41788014655990511092712665 31341010991992883319534499)
      ·
        refine ⟨47011516487989324979301749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31341010991992883319534499 47011516487989324979301749)
        ·
          refine ⟨4407329670748999216809539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47011516487989324979301749 4407329670748999216809539)
          ·
            refine ⟨6610994506123498825214309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4407329670748999216809539 6610994506123498825214309)
            ·
              refine ⟨1239561469898156029727683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6610994506123498825214309 1239561469898156029727683)
              ·
                refine ⟨1859342204847234044591525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1239561469898156029727683 1859342204847234044591525)
                ·
                  refine ⟨348626663408856383360911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1859342204847234044591525 348626663408856383360911)
                  ·
                    rfl

theorem cell21_1527633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 4].length) (baseStart_1527633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1527633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1527633 prefixEnd_1527633 := by exact prefixLift 1527633
  have htrace : WordTrace (prefixWord ++ tailWord_1527633) baseStart_1527633 baseEnd_1527633 := by
    simpa [prefixWord, tailWord_1527633, baseEnd_1527633] using wordTrace_append hprefix tailTrace_1527633
  have hstable : (prefixWord ++ tailWord_1527633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527633).length < 2 ^ (prefixWord ++ tailWord_1527633).sum := by decide
  have hdescent : baseEnd_1527633 < baseStart_1527633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527670 : List Nat := [5, 1, 1, 3, 3, 1, 2, 2, 3]
def baseStart_1527670 : Nat := 118140960795 + 1527670 * 2 ^ 59
def prefixEnd_1527670 : Nat := 4983230072969 + 3 ^ 40 * 1527670 * 2
def baseEnd_1527670 : Nat := 348635107312952541244169

theorem tailTrace_1527670 : CollatzResearch.WordTrace tailWord_1527670 prefixEnd_1527670 348635107312952541244169 := by
  unfold tailWord_1527670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3482418898469998131836279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37145801583679980072920309 3482418898469998131836279)
  ·
    refine ⟨5223628347704997197754419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3482418898469998131836279 5223628347704997197754419)
    ·
      refine ⟨7835442521557495796631629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5223628347704997197754419 7835442521557495796631629)
      ·
        refine ⟨2938290945584060923736861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7835442521557495796631629 2938290945584060923736861)
        ·
          refine ⟨1101859104594022846401323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2938290945584060923736861 1101859104594022846401323)
          ·
            refine ⟨1652788656891034269601985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1101859104594022846401323 1652788656891034269601985)
            ·
              refine ⟨1239591492668275702201489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1652788656891034269601985 1239591492668275702201489)
              ·
                refine ⟨929693619501206776651117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1239591492668275702201489 929693619501206776651117)
                ·
                  refine ⟨348635107312952541244169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 929693619501206776651117 348635107312952541244169)
                  ·
                    rfl

theorem cell21_1527670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_1527670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1527670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1527670 prefixEnd_1527670 := by exact prefixLift 1527670
  have htrace : WordTrace (prefixWord ++ tailWord_1527670) baseStart_1527670 baseEnd_1527670 := by
    simpa [prefixWord, tailWord_1527670, baseEnd_1527670] using wordTrace_append hprefix tailTrace_1527670
  have hstable : (prefixWord ++ tailWord_1527670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527670).length < 2 ^ (prefixWord ++ tailWord_1527670).sum := by decide
  have hdescent : baseEnd_1527670 < baseStart_1527670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527681 : List Nat := [1, 2, 4, 4, 2, 1, 1, 6]
def baseStart_1527681 : Nat := 118140960795 + 1527681 * 2 ^ 59
def prefixEnd_1527681 : Nat := 4983230072969 + 3 ^ 40 * 1527681 * 2
def baseEnd_1527681 : Nat := 116212539220939655520271

theorem tailTrace_1527681 : CollatzResearch.WordTrace tailWord_1527681 prefixEnd_1527681 116212539220939655520271 := by
  unfold tailWord_1527681
  simp only [CollatzResearch.WordTrace]
  refine ⟨55719103578480118988030897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37146069052320079325353931 55719103578480118988030897)
  ·
    refine ⟨41789327683860089241023173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55719103578480118988030897 41789327683860089241023173)
    ·
      refine ⟨7835498940723766732691845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41789327683860089241023173 7835498940723766732691845)
      ·
        refine ⟨1469156051385706262379721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7835498940723766732691845 1469156051385706262379721)
        ·
          refine ⟨1101867038539279696784791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1469156051385706262379721 1101867038539279696784791)
          ·
            refine ⟨1652800557808919545177187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1101867038539279696784791 1652800557808919545177187)
            ·
              refine ⟨2479200836713379317765781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1652800557808919545177187 2479200836713379317765781)
              ·
                refine ⟨116212539220939655520271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2479200836713379317765781 116212539220939655520271)
                ·
                  rfl

theorem cell21_1527681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 6].length) (baseStart_1527681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1527681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1527681 prefixEnd_1527681 := by exact prefixLift 1527681
  have htrace : WordTrace (prefixWord ++ tailWord_1527681) baseStart_1527681 baseEnd_1527681 := by
    simpa [prefixWord, tailWord_1527681, baseEnd_1527681] using wordTrace_append hprefix tailTrace_1527681
  have hstable : (prefixWord ++ tailWord_1527681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527681).length < 2 ^ (prefixWord ++ tailWord_1527681).sum := by decide
  have hdescent : baseEnd_1527681 < baseStart_1527681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527737 : List Nat := [1, 2, 1, 4, 2, 1, 4, 1, 5]
def baseStart_1527737 : Nat := 118140960795 + 1527737 * 2 ^ 59
def prefixEnd_1527737 : Nat := 4983230072969 + 3 ^ 40 * 1527737 * 2
def baseEnd_1527737 : Nat := 348650397625775313627365

theorem tailTrace_1527737 : CollatzResearch.WordTrace tailWord_1527737 prefixEnd_1527737 348650397625775313627365 := by
  unfold tailWord_1527737
  simp only [CollatzResearch.WordTrace]
  refine ⟨55721146066277240552069465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37147430710851493701379643 55721146066277240552069465)
  ·
    refine ⟨41790859549707930414052099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55721146066277240552069465 41790859549707930414052099)
    ·
      refine ⟨62686289324561895621078149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41790859549707930414052099 62686289324561895621078149)
      ·
        refine ⟨11753679248355355428952153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62686289324561895621078149 11753679248355355428952153)
        ·
          refine ⟨8815259436266516571714115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11753679248355355428952153 8815259436266516571714115)
          ·
            refine ⟨13222889154399774857571173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8815259436266516571714115 13222889154399774857571173)
            ·
              refine ⟨2479291716449957785794595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13222889154399774857571173 2479291716449957785794595)
              ·
                refine ⟨3718937574674936678691893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2479291716449957785794595 3718937574674936678691893)
                ·
                  refine ⟨348650397625775313627365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3718937574674936678691893 348650397625775313627365)
                  ·
                    rfl

theorem cell21_1527737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 5].length) (baseStart_1527737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1527737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1527737 prefixEnd_1527737 := by exact prefixLift 1527737
  have htrace : WordTrace (prefixWord ++ tailWord_1527737) baseStart_1527737 baseEnd_1527737 := by
    simpa [prefixWord, tailWord_1527737, baseEnd_1527737] using wordTrace_append hprefix tailTrace_1527737
  have hstable : (prefixWord ++ tailWord_1527737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527737).length < 2 ^ (prefixWord ++ tailWord_1527737).sum := by decide
  have hdescent : baseEnd_1527737 < baseStart_1527737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527841 : List Nat := [1, 2, 3, 2, 13]
def baseStart_1527841 : Nat := 118140960795 + 1527841 * 2 ^ 59
def prefixEnd_1527841 : Nat := 4983230072969 + 3 ^ 40 * 1527841 * 2
def baseEnd_1527841 : Nat := 4304618911638200541899

theorem tailTrace_1527841 : CollatzResearch.WordTrace tailWord_1527841 prefixEnd_1527841 4304618911638200541899 := by
  unfold tailWord_1527841
  simp only [CollatzResearch.WordTrace]
  refine ⟨55724939257900466313855377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37149959505266977542570251 55724939257900466313855377)
  ·
    refine ⟨41793704443425349735391533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55724939257900466313855377 41793704443425349735391533)
    ·
      refine ⟨15672639166284506150771825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41793704443425349735391533 15672639166284506150771825)
      ·
        refine ⟨11754479374713379613078869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15672639166284506150771825 11754479374713379613078869)
        ·
          refine ⟨4304618911638200541899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 11754479374713379613078869 4304618911638200541899)
          ·
            rfl

theorem cell21_1527841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 13].length) (baseStart_1527841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1527841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1527841 prefixEnd_1527841 := by exact prefixLift 1527841
  have htrace : WordTrace (prefixWord ++ tailWord_1527841) baseStart_1527841 baseEnd_1527841 := by
    simpa [prefixWord, tailWord_1527841, baseEnd_1527841] using wordTrace_append hprefix tailTrace_1527841
  have hstable : (prefixWord ++ tailWord_1527841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527841).length < 2 ^ (prefixWord ++ tailWord_1527841).sum := by decide
  have hdescent : baseEnd_1527841 < baseStart_1527841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527858 : List Nat := [3, 2, 1, 1, 2, 3, 3, 6]
def baseStart_1527858 : Nat := 118140960795 + 1527858 * 2 ^ 59
def prefixEnd_1527858 : Nat := 4983230072969 + 3 ^ 40 * 1527858 * 2
def baseEnd_1527858 : Nat := 116226003824768664036817

theorem tailTrace_1527858 : CollatzResearch.WordTrace tailWord_1527858 prefixEnd_1527858 116226003824768664036817 := by
  unfold tailWord_1527858
  simp only [CollatzResearch.WordTrace]
  refine ⟨13931389824709719554306057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37150372865892585478149485 13931389824709719554306057)
  ·
    refine ⟨10448542368532289665729543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13931389824709719554306057 10448542368532289665729543)
    ·
      refine ⟨15672813552798434498594315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10448542368532289665729543 15672813552798434498594315)
      ·
        refine ⟨23509220329197651747891473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15672813552798434498594315 23509220329197651747891473)
        ·
          refine ⟨17631915246898238810918605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23509220329197651747891473 17631915246898238810918605)
          ·
            refine ⟨6611968217586839554094477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17631915246898238810918605 6611968217586839554094477)
            ·
              refine ⟨2479488081595064832785429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6611968217586839554094477 2479488081595064832785429)
              ·
                refine ⟨116226003824768664036817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2479488081595064832785429 116226003824768664036817)
                ·
                  rfl

theorem cell21_1527858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 6].length) (baseStart_1527858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1527858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1527858 prefixEnd_1527858 := by exact prefixLift 1527858
  have htrace : WordTrace (prefixWord ++ tailWord_1527858) baseStart_1527858 baseEnd_1527858 := by
    simpa [prefixWord, tailWord_1527858, baseEnd_1527858] using wordTrace_append hprefix tailTrace_1527858
  have hstable : (prefixWord ++ tailWord_1527858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527858).length < 2 ^ (prefixWord ++ tailWord_1527858).sum := by decide
  have hdescent : baseEnd_1527858 < baseStart_1527858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527872 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 7]
def baseStart_1527872 : Nat := 118140960795 + 1527872 * 2 ^ 59
def prefixEnd_1527872 : Nat := 4983230072969 + 3 ^ 40 * 1527872 * 2
def baseEnd_1527872 : Nat := 348681206465045078877089

theorem tailTrace_1527872 : CollatzResearch.WordTrace tailWord_1527872 prefixEnd_1527872 348681206465045078877089 := by
  unfold tailWord_1527872
  simp only [CollatzResearch.WordTrace]
  refine ⟨27863034960394079304116935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37150713280525439072155913 27863034960394079304116935)
  ·
    refine ⟨41794552440591118956175403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27863034960394079304116935 41794552440591118956175403)
    ·
      refine ⟨62691828660886678434263105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41794552440591118956175403 62691828660886678434263105)
      ·
        refine ⟨47018871495665008825697329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62691828660886678434263105 47018871495665008825697329)
        ·
          refine ⟨35264153621748756619272997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47018871495665008825697329 35264153621748756619272997)
          ·
            refine ⟨6612028804077891866113687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35264153621748756619272997 6612028804077891866113687)
            ·
              refine ⟨9918043206116837799170531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6612028804077891866113687 9918043206116837799170531)
              ·
                refine ⟨14877064809175256698755797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9918043206116837799170531 14877064809175256698755797)
                ·
                  refine ⟨348681206465045078877089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14877064809175256698755797 348681206465045078877089)
                  ·
                    rfl

theorem cell21_1527872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 7].length) (baseStart_1527872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1527872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1527872 prefixEnd_1527872 := by exact prefixLift 1527872
  have htrace : WordTrace (prefixWord ++ tailWord_1527872) baseStart_1527872 baseEnd_1527872 := by
    simpa [prefixWord, tailWord_1527872, baseEnd_1527872] using wordTrace_append hprefix tailTrace_1527872
  have hstable : (prefixWord ++ tailWord_1527872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527872).length < 2 ^ (prefixWord ++ tailWord_1527872).sum := by decide
  have hdescent : baseEnd_1527872 < baseStart_1527872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527903 : List Nat := [1, 1, 2, 3, 1, 1, 2, 6, 4]
def baseStart_1527903 : Nat := 118140960795 + 1527903 * 2 ^ 59
def prefixEnd_1527903 : Nat := 4983230072969 + 3 ^ 40 * 1527903 * 2
def baseEnd_1527903 : Nat := 348688281087395913860359

theorem tailTrace_1527903 : CollatzResearch.WordTrace tailWord_1527903 prefixEnd_1527903 348688281087395913860359 := by
  unfold tailWord_1527903
  simp only [CollatzResearch.WordTrace]
  refine ⟨55727200583675850902612363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37151467055783900601741575 55727200583675850902612363)
  ·
    refine ⟨83590800875513776353918545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55727200583675850902612363 83590800875513776353918545)
    ·
      refine ⟨62693100656635332265438909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83590800875513776353918545 62693100656635332265438909)
      ·
        refine ⟨23509912746238249599539591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62693100656635332265438909 23509912746238249599539591)
        ·
          refine ⟨35264869119357374399309387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23509912746238249599539591 35264869119357374399309387)
          ·
            refine ⟨52897303679036061598964081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35264869119357374399309387 52897303679036061598964081)
            ·
              refine ⟨39672977759277046199223061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52897303679036061598964081 39672977759277046199223061)
              ·
                refine ⟨1859670832466111540588581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39672977759277046199223061 1859670832466111540588581)
                ·
                  refine ⟨348688281087395913860359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1859670832466111540588581 348688281087395913860359)
                  ·
                    rfl

theorem cell21_1527903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 4].length) (baseStart_1527903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1527903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1527903 prefixEnd_1527903 := by exact prefixLift 1527903
  have htrace : WordTrace (prefixWord ++ tailWord_1527903) baseStart_1527903 baseEnd_1527903 := by
    simpa [prefixWord, tailWord_1527903, baseEnd_1527903] using wordTrace_append hprefix tailTrace_1527903
  have hstable : (prefixWord ++ tailWord_1527903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527903).length < 2 ^ (prefixWord ++ tailWord_1527903).sum := by decide
  have hdescent : baseEnd_1527903 < baseStart_1527903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527965 : List Nat := [1, 4, 2, 1, 1, 3, 3, 1, 5]
def baseStart_1527965 : Nat := 118140960795 + 1527965 * 2 ^ 59
def prefixEnd_1527965 : Nat := 4983230072969 + 3 ^ 40 * 1527965 * 2
def baseEnd_1527965 : Nat := 348702430332097583826899

theorem tailTrace_1527965 : CollatzResearch.WordTrace tailWord_1527965 prefixEnd_1527965 348702430332097583826899 := by
  unfold tailWord_1527965
  simp only [CollatzResearch.WordTrace]
  refine ⟨55729461909451235491369349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37152974606300823660912899 55729461909451235491369349)
  ·
    refine ⟨10449274108022106654631753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55729461909451235491369349 10449274108022106654631753)
    ·
      refine ⟨7836955581016579990973815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10449274108022106654631753 7836955581016579990973815)
      ·
        refine ⟨11755433371524869986460723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7836955581016579990973815 11755433371524869986460723)
        ·
          refine ⟨17633150057287304979691085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11755433371524869986460723 17633150057287304979691085)
          ·
            refine ⟨6612431271482739367384157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17633150057287304979691085 6612431271482739367384157)
            ·
              refine ⟨2479661726806027262769059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6612431271482739367384157 2479661726806027262769059)
              ·
                refine ⟨3719492590209040894153589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2479661726806027262769059 3719492590209040894153589)
                ·
                  refine ⟨348702430332097583826899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3719492590209040894153589 348702430332097583826899)
                  ·
                    rfl

theorem cell21_1527965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_1527965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1527965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1527965 prefixEnd_1527965 := by exact prefixLift 1527965
  have htrace : WordTrace (prefixWord ++ tailWord_1527965) baseStart_1527965 baseEnd_1527965 := by
    simpa [prefixWord, tailWord_1527965, baseEnd_1527965] using wordTrace_append hprefix tailTrace_1527965
  have hstable : (prefixWord ++ tailWord_1527965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527965).length < 2 ^ (prefixWord ++ tailWord_1527965).sum := by decide
  have hdescent : baseEnd_1527965 < baseStart_1527965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527993 : List Nat := [1, 2, 1, 4, 1, 2, 1, 9]
def baseStart_1527993 : Nat := 118140960795 + 1527993 * 2 ^ 59
def prefixEnd_1527993 : Nat := 4983230072969 + 3 ^ 40 * 1527993 * 2
def baseEnd_1527993 : Nat := 116236273437858585786725

theorem tailTrace_1527993 : CollatzResearch.WordTrace tailWord_1527993 prefixEnd_1527993 116236273437858585786725 := by
  unfold tailWord_1527993
  simp only [CollatzResearch.WordTrace]
  refine ⟨55730483153349796273388633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37153655435566530848925755 55730483153349796273388633)
  ·
    refine ⟨41797862365012347205041475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55730483153349796273388633 41797862365012347205041475)
    ·
      refine ⟨62696793547518520807562213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41797862365012347205041475 62696793547518520807562213)
      ·
        refine ⟨11755648790159722651417915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62696793547518520807562213 11755648790159722651417915)
        ·
          refine ⟨17633473185239583977126873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11755648790159722651417915 17633473185239583977126873)
          ·
            refine ⟨13225104888929687982845155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17633473185239583977126873 13225104888929687982845155)
            ·
              refine ⟨19837657333394531974267733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13225104888929687982845155 19837657333394531974267733)
              ·
                refine ⟨116236273437858585786725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19837657333394531974267733 116236273437858585786725)
                ·
                  rfl

theorem cell21_1527993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 9].length) (baseStart_1527993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1527993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1527993 prefixEnd_1527993 := by exact prefixLift 1527993
  have htrace : WordTrace (prefixWord ++ tailWord_1527993) baseStart_1527993 baseEnd_1527993 := by
    simpa [prefixWord, tailWord_1527993, baseEnd_1527993] using wordTrace_append hprefix tailTrace_1527993
  have hstable : (prefixWord ++ tailWord_1527993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527993).length < 2 ^ (prefixWord ++ tailWord_1527993).sum := by decide
  have hdescent : baseEnd_1527993 < baseStart_1527993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528058 : List Nat := [3, 1, 1, 1, 1, 6, 2, 3, 3]
def baseStart_1528058 : Nat := 118140960795 + 1528058 * 2 ^ 59
def prefixEnd_1528058 : Nat := 4983230072969 + 3 ^ 40 * 1528058 * 2
def baseEnd_1528058 : Nat := 348723654199150088776709

theorem tailTrace_1528058 : CollatzResearch.WordTrace tailWord_1528058 prefixEnd_1528058 348723654199150088776709 := by
  unfold tailWord_1528058
  simp only [CollatzResearch.WordTrace]
  refine ⟨13933213474528578093626207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37155235932076208249669885 13933213474528578093626207)
  ·
    refine ⟨20899820211792867140439311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13933213474528578093626207 20899820211792867140439311)
    ·
      refine ⟨31349730317689300710658967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20899820211792867140439311 31349730317689300710658967)
      ·
        refine ⟨47024595476533951065988451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31349730317689300710658967 47024595476533951065988451)
        ·
          refine ⟨70536893214800926598982677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47024595476533951065988451 70536893214800926598982677)
          ·
            refine ⟨3306416869443793434327313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70536893214800926598982677 3306416869443793434327313)
            ·
              refine ⟨2479812652082845075745485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3306416869443793434327313 2479812652082845075745485)
              ·
                refine ⟨929929744531066903404557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2479812652082845075745485 929929744531066903404557)
                ·
                  refine ⟨348723654199150088776709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 929929744531066903404557 348723654199150088776709)
                  ·
                    rfl

theorem cell21_1528058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3, 3].length) (baseStart_1528058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1528058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1528058 prefixEnd_1528058 := by exact prefixLift 1528058
  have htrace : WordTrace (prefixWord ++ tailWord_1528058) baseStart_1528058 baseEnd_1528058 := by
    simpa [prefixWord, tailWord_1528058, baseEnd_1528058] using wordTrace_append hprefix tailTrace_1528058
  have hstable : (prefixWord ++ tailWord_1528058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528058).length < 2 ^ (prefixWord ++ tailWord_1528058).sum := by decide
  have hdescent : baseEnd_1528058 < baseStart_1528058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528072 : List Nat := [2, 1, 3, 2, 3, 1, 3, 2, 4]
def baseStart_1528072 : Nat := 118140960795 + 1528072 * 2 ^ 59
def prefixEnd_1528072 : Nat := 4983230072969 + 3 ^ 40 * 1528072 * 2
def baseEnd_1528072 : Nat := 348726849189889175543347

theorem tailTrace_1528072 : CollatzResearch.WordTrace tailWord_1528072 prefixEnd_1528072 348726849189889175543347 := by
  unfold tailWord_1528072
  simp only [CollatzResearch.WordTrace]
  refine ⟨27866682260031796382757235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37155576346709061843676313 27866682260031796382757235)
  ·
    refine ⟨41800023390047694574135853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27866682260031796382757235 41800023390047694574135853)
    ·
      refine ⟨15675008771267885465300945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41800023390047694574135853 15675008771267885465300945)
      ·
        refine ⟨11756256578450914098975709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15675008771267885465300945 11756256578450914098975709)
        ·
          refine ⟨4408596216919092787115891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11756256578450914098975709 4408596216919092787115891)
          ·
            refine ⟨6612894325378639180673837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4408596216919092787115891 6612894325378639180673837)
            ·
              refine ⟨2479835372016989692752689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6612894325378639180673837 2479835372016989692752689)
              ·
                refine ⟨1859876529012742269564517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2479835372016989692752689 1859876529012742269564517)
                ·
                  refine ⟨348726849189889175543347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1859876529012742269564517 348726849189889175543347)
                  ·
                    rfl

theorem cell21_1528072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 4].length) (baseStart_1528072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1528072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1528072 prefixEnd_1528072 := by exact prefixLift 1528072
  have htrace : WordTrace (prefixWord ++ tailWord_1528072) baseStart_1528072 baseEnd_1528072 := by
    simpa [prefixWord, tailWord_1528072, baseEnd_1528072] using wordTrace_append hprefix tailTrace_1528072
  have hstable : (prefixWord ++ tailWord_1528072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528072).length < 2 ^ (prefixWord ++ tailWord_1528072).sum := by decide
  have hdescent : baseEnd_1528072 < baseStart_1528072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528109 : List Nat := [1, 5, 3, 1, 3, 1, 1, 3, 3]
def baseStart_1528109 : Nat := 118140960795 + 1528109 * 2 ^ 59
def prefixEnd_1528109 : Nat := 4983230072969 + 3 ^ 40 * 1528109 * 2
def baseEnd_1528109 : Nat := 348735293093985333426605

theorem tailTrace_1528109 : CollatzResearch.WordTrace tailWord_1528109 prefixEnd_1528109 348735293093985333426605 := by
  unfold tailWord_1528109
  simp only [CollatzResearch.WordTrace]
  refine ⟨55734714020929548084611381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37156476013953032056407587 55734714020929548084611381)
  ·
    refine ⟨5225129439462145132932317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55734714020929548084611381 5225129439462145132932317)
    ·
      refine ⟨1959423539798304424849619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5225129439462145132932317 1959423539798304424849619)
      ·
        refine ⟨2939135309697456637274429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1959423539798304424849619 2939135309697456637274429)
        ·
          refine ⟨1102175741136546238977911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2939135309697456637274429 1102175741136546238977911)
          ·
            refine ⟨1653263611704819358466867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1102175741136546238977911 1653263611704819358466867)
            ·
              refine ⟨2479895417557229037700301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1653263611704819358466867 2479895417557229037700301)
              ·
                refine ⟨929960781583960889137613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2479895417557229037700301 929960781583960889137613)
                ·
                  refine ⟨348735293093985333426605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 929960781583960889137613 348735293093985333426605)
                  ·
                    rfl

theorem cell21_1528109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_1528109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1528109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1528109 prefixEnd_1528109 := by exact prefixLift 1528109
  have htrace : WordTrace (prefixWord ++ tailWord_1528109) baseStart_1528109 baseEnd_1528109 := by
    simpa [prefixWord, tailWord_1528109, baseEnd_1528109] using wordTrace_append hprefix tailTrace_1528109
  have hstable : (prefixWord ++ tailWord_1528109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528109).length < 2 ^ (prefixWord ++ tailWord_1528109).sum := by decide
  have hdescent : baseEnd_1528109 < baseStart_1528109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528145 : List Nat := [1, 2, 2, 1, 4, 2, 1, 8]
def baseStart_1528145 : Nat := 118140960795 + 1528145 * 2 ^ 59
def prefixEnd_1528145 : Nat := 4983230072969 + 3 ^ 40 * 1528145 * 2
def baseEnd_1528145 : Nat := 116247836261485756942177

theorem tailTrace_1528145 : CollatzResearch.WordTrace tailWord_1528145 prefixEnd_1528145 116247836261485756942177 := by
  unfold tailWord_1528145
  simp only [CollatzResearch.WordTrace]
  refine ⟨55736027048799126232921889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37157351365866084155281259 55736027048799126232921889)
  ·
    refine ⟨41802020286599344674691417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55736027048799126232921889 41802020286599344674691417)
    ·
      refine ⟨31351515214949508506018563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41802020286599344674691417 31351515214949508506018563)
      ·
        refine ⟨47027272822424262759027845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31351515214949508506018563 47027272822424262759027845)
        ·
          refine ⟨8817613654204549267317721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47027272822424262759027845 8817613654204549267317721)
          ·
            refine ⟨6613210240653411950488291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8817613654204549267317721 6613210240653411950488291)
            ·
              refine ⟨9919815360980117925732437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6613210240653411950488291 9919815360980117925732437)
              ·
                refine ⟨116247836261485756942177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9919815360980117925732437 116247836261485756942177)
                ·
                  rfl

theorem cell21_1528145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 8].length) (baseStart_1528145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1528145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1528145 prefixEnd_1528145 := by exact prefixLift 1528145
  have htrace : WordTrace (prefixWord ++ tailWord_1528145) baseStart_1528145 baseEnd_1528145 := by
    simpa [prefixWord, tailWord_1528145, baseEnd_1528145] using wordTrace_append hprefix tailTrace_1528145
  have hstable : (prefixWord ++ tailWord_1528145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528145).length < 2 ^ (prefixWord ++ tailWord_1528145).sum := by decide
  have hdescent : baseEnd_1528145 < baseStart_1528145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528148 : List Nat := [2, 4, 1, 1, 2, 3, 1, 3, 4]
def baseStart_1528148 : Nat := 118140960795 + 1528148 * 2 ^ 59
def prefixEnd_1528148 : Nat := 4983230072969 + 3 ^ 40 * 1528148 * 2
def baseEnd_1528148 : Nat := 348744193425329932276525

theorem tailTrace_1528148 : CollatzResearch.WordTrace tailWord_1528148 prefixEnd_1528148 348744193425329932276525 := by
  unfold tailWord_1528148
  simp only [CollatzResearch.WordTrace]
  refine ⟨27868068233894128872640549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37157424311858838496854065 27868068233894128872640549)
  ·
    refine ⟨5225262793855149163620103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27868068233894128872640549 5225262793855149163620103)
    ·
      refine ⟨7837894190782723745430155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5225262793855149163620103 7837894190782723745430155)
      ·
        refine ⟨11756841286174085618145233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7837894190782723745430155 11756841286174085618145233)
        ·
          refine ⟨8817630964630564213608925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11756841286174085618145233 8817630964630564213608925)
          ·
            refine ⟨3306611611736461580103347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8817630964630564213608925 3306611611736461580103347)
            ·
              refine ⟨4959917417604692370155021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3306611611736461580103347 4959917417604692370155021)
              ·
                refine ⟨1859969031601759638808133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4959917417604692370155021 1859969031601759638808133)
                ·
                  refine ⟨348744193425329932276525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1859969031601759638808133 348744193425329932276525)
                  ·
                    rfl

theorem cell21_1528148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_1528148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1528148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1528148 prefixEnd_1528148 := by exact prefixLift 1528148
  have htrace : WordTrace (prefixWord ++ tailWord_1528148) baseStart_1528148 baseEnd_1528148 := by
    simpa [prefixWord, tailWord_1528148, baseEnd_1528148] using wordTrace_append hprefix tailTrace_1528148
  have hstable : (prefixWord ++ tailWord_1528148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528148).length < 2 ^ (prefixWord ++ tailWord_1528148).sum := by decide
  have hdescent : baseEnd_1528148 < baseStart_1528148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528162 : List Nat := [3, 3, 2, 1, 1, 2, 2, 7]
def baseStart_1528162 : Nat := 118140960795 + 1528162 * 2 ^ 59
def prefixEnd_1528162 : Nat := 4983230072969 + 3 ^ 40 * 1528162 * 2
def baseEnd_1528162 : Nat := 116249129472023006347721

theorem tailTrace_1528162 : CollatzResearch.WordTrace tailWord_1528162 prefixEnd_1528162 116249129472023006347721 := by
  unfold tailWord_1528162
  simp only [CollatzResearch.WordTrace]
  refine ⟨13934161772434384534072685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37157764726491692090860493 13934161772434384534072685)
  ·
    refine ⟨5225310664662894200277257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13934161772434384534072685 5225310664662894200277257)
    ·
      refine ⟨3918982998497170650207943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5225310664662894200277257 3918982998497170650207943)
      ·
        refine ⟨5878474497745755975311915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3918982998497170650207943 5878474497745755975311915)
        ·
          refine ⟨8817711746618633962967873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5878474497745755975311915 8817711746618633962967873)
          ·
            refine ⟨6613283809963975472225905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8817711746618633962967873 6613283809963975472225905)
            ·
              refine ⟨4959962857472981604169429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6613283809963975472225905 4959962857472981604169429)
              ·
                refine ⟨116249129472023006347721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4959962857472981604169429 116249129472023006347721)
                ·
                  rfl

theorem cell21_1528162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_1528162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1528162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1528162 prefixEnd_1528162 := by exact prefixLift 1528162
  have htrace : WordTrace (prefixWord ++ tailWord_1528162) baseStart_1528162 baseEnd_1528162 := by
    simpa [prefixWord, tailWord_1528162, baseEnd_1528162] using wordTrace_append hprefix tailTrace_1528162
  have hstable : (prefixWord ++ tailWord_1528162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528162).length < 2 ^ (prefixWord ++ tailWord_1528162).sum := by decide
  have hdescent : baseEnd_1528162 < baseStart_1528162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528182 : List Nat := [5, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_1528182 : Nat := 118140960795 + 1528182 * 2 ^ 59
def prefixEnd_1528182 : Nat := 4983230072969 + 3 ^ 40 * 1528182 * 2
def baseEnd_1528182 : Nat := 348751952688553428709789

theorem tailTrace_1528182 : CollatzResearch.WordTrace tailWord_1528182 prefixEnd_1528182 348751952688553428709789 := by
  unfold tailWord_1528182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3483586034354067597001175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37158251033110054368012533 3483586034354067597001175)
  ·
    refine ⟨5225379051531101395501763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3483586034354067597001175 5225379051531101395501763)
    ·
      refine ⟨7838068577296652093252645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5225379051531101395501763 7838068577296652093252645)
      ·
        refine ⟨1469637858243122267484871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7838068577296652093252645 1469637858243122267484871)
        ·
          refine ⟨2204456787364683401227307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1469637858243122267484871 2204456787364683401227307)
          ·
            refine ⟨3306685181047025101840961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2204456787364683401227307 3306685181047025101840961)
            ·
              refine ⟨2480013885785268826380721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3306685181047025101840961 2480013885785268826380721)
              ·
                refine ⟨1860010414338951619785541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2480013885785268826380721 1860010414338951619785541)
                ·
                  refine ⟨348751952688553428709789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1860010414338951619785541 348751952688553428709789)
                  ·
                    rfl

theorem cell21_1528182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_1528182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1528182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1528182 prefixEnd_1528182 := by exact prefixLift 1528182
  have htrace : WordTrace (prefixWord ++ tailWord_1528182) baseStart_1528182 baseEnd_1528182 := by
    simpa [prefixWord, tailWord_1528182, baseEnd_1528182] using wordTrace_append hprefix tailTrace_1528182
  have hstable : (prefixWord ++ tailWord_1528182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528182).length < 2 ^ (prefixWord ++ tailWord_1528182).sum := by decide
  have hdescent : baseEnd_1528182 < baseStart_1528182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528362 : List Nat := [3, 1, 4, 1, 1, 3, 1, 4, 3]
def baseStart_1528362 : Nat := 118140960795 + 1528362 * 2 ^ 59
def prefixEnd_1528362 : Nat := 4983230072969 + 3 ^ 40 * 1528362 * 2
def baseEnd_1528362 : Nat := 348793031140913115709421

theorem tailTrace_1528362 : CollatzResearch.WordTrace tailWord_1528362 prefixEnd_1528362 348793031140913115709421 := by
  unfold tailWord_1528362
  simp only [CollatzResearch.WordTrace]
  refine ⟨13935985422253243073392835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37162627792675314862380893 13935985422253243073392835)
  ·
    refine ⟨20903978133379864610089253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13935985422253243073392835 20903978133379864610089253)
    ·
      refine ⟨3919495900008724614391735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20903978133379864610089253 3919495900008724614391735)
      ·
        refine ⟨5879243850013086921587603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3919495900008724614391735 5879243850013086921587603)
        ·
          refine ⟨8818865775019630382381405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5879243850013086921587603 8818865775019630382381405)
          ·
            refine ⟨3307074665632361393393027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8818865775019630382381405 3307074665632361393393027)
            ·
              refine ⟨4960611998448542090089541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3307074665632361393393027 4960611998448542090089541)
              ·
                refine ⟨930114749709101641891789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4960611998448542090089541 930114749709101641891789)
                ·
                  refine ⟨348793031140913115709421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 930114749709101641891789 348793031140913115709421)
                  ·
                    rfl

theorem cell21_1528362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4, 3].length) (baseStart_1528362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1528362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1528362 prefixEnd_1528362 := by exact prefixLift 1528362
  have htrace : WordTrace (prefixWord ++ tailWord_1528362) baseStart_1528362 baseEnd_1528362 := by
    simpa [prefixWord, tailWord_1528362, baseEnd_1528362] using wordTrace_append hprefix tailTrace_1528362
  have hstable : (prefixWord ++ tailWord_1528362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528362).length < 2 ^ (prefixWord ++ tailWord_1528362).sum := by decide
  have hdescent : baseEnd_1528362 < baseStart_1528362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528365 : List Nat := [1, 5, 4, 1, 1, 2, 1, 6]
def baseStart_1528365 : Nat := 118140960795 + 1528365 * 2 ^ 59
def prefixEnd_1528365 : Nat := 4983230072969 + 3 ^ 40 * 1528365 * 2
def baseEnd_1528365 : Nat := 116264571927261925719805

theorem tailTrace_1528365 : CollatzResearch.WordTrace tailWord_1528365 prefixEnd_1528365 116264571927261925719805 := by
  unfold tailWord_1528365
  simp only [CollatzResearch.WordTrace]
  refine ⟨55744051108002103805930549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37162700738668069203953699 55744051108002103805930549)
  ·
    refine ⟨5226004791375197231805989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55744051108002103805930549 5226004791375197231805989)
    ·
      refine ⟨979875898382849480963623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5226004791375197231805989 979875898382849480963623)
      ·
        refine ⟨1469813847574274221445435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 979875898382849480963623 1469813847574274221445435)
        ·
          refine ⟨2204720771361411332168153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1469813847574274221445435 2204720771361411332168153)
          ·
            refine ⟨1653540578521058499126115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2204720771361411332168153 1653540578521058499126115)
            ·
              refine ⟨2480310867781587748689173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1653540578521058499126115 2480310867781587748689173)
              ·
                refine ⟨116264571927261925719805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2480310867781587748689173 116264571927261925719805)
                ·
                  rfl

theorem cell21_1528365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 6].length) (baseStart_1528365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1528365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1528365 prefixEnd_1528365 := by exact prefixLift 1528365
  have htrace : WordTrace (prefixWord ++ tailWord_1528365) baseStart_1528365 baseEnd_1528365 := by
    simpa [prefixWord, tailWord_1528365, baseEnd_1528365] using wordTrace_append hprefix tailTrace_1528365
  have hstable : (prefixWord ++ tailWord_1528365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528365).length < 2 ^ (prefixWord ++ tailWord_1528365).sum := by decide
  have hdescent : baseEnd_1528365 < baseStart_1528365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528421 : List Nat := [1, 3, 1, 3, 4, 1, 2, 1, 5]
def baseStart_1528421 : Nat := 118140960795 + 1528421 * 2 ^ 59
def prefixEnd_1528421 : Nat := 4983230072969 + 3 ^ 40 * 1528421 * 2
def baseEnd_1528421 : Nat := 348806495744742124225967

theorem tailTrace_1528421 : CollatzResearch.WordTrace tailWord_1528421 prefixEnd_1528421 348806495744742124225967 := by
  unfold tailWord_1528421
  simp only [CollatzResearch.WordTrace]
  refine ⟨55746093595799225369969117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37164062397199483579979411 55746093595799225369969117)
  ·
    refine ⟨20904785098424709513738419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55746093595799225369969117 20904785098424709513738419)
    ·
      refine ⟨31357177647637064270607629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20904785098424709513738419 31357177647637064270607629)
      ·
        refine ⟨11758941617863899101477861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31357177647637064270607629 11758941617863899101477861)
        ·
          refine ⟨2204801553349481081527099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11758941617863899101477861 2204801553349481081527099)
          ·
            refine ⟨3307202330024221622290649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2204801553349481081527099 3307202330024221622290649)
            ·
              refine ⟨2480401747518166216717987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3307202330024221622290649 2480401747518166216717987)
              ·
                refine ⟨3720602621277249325076981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2480401747518166216717987 3720602621277249325076981)
                ·
                  refine ⟨348806495744742124225967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3720602621277249325076981 348806495744742124225967)
                  ·
                    rfl

theorem cell21_1528421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_1528421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1528421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1528421 prefixEnd_1528421 := by exact prefixLift 1528421
  have htrace : WordTrace (prefixWord ++ tailWord_1528421) baseStart_1528421 baseEnd_1528421 := by
    simpa [prefixWord, tailWord_1528421, baseEnd_1528421] using wordTrace_append hprefix tailTrace_1528421
  have hstable : (prefixWord ++ tailWord_1528421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528421).length < 2 ^ (prefixWord ++ tailWord_1528421).sum := by decide
  have hdescent : baseEnd_1528421 < baseStart_1528421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528449 : List Nat := [1, 2, 4, 2, 1, 1, 3, 7]
def baseStart_1528449 : Nat := 118140960795 + 1528449 * 2 ^ 59
def prefixEnd_1528449 : Nat := 4983230072969 + 3 ^ 40 * 1528449 * 2
def baseEnd_1528449 : Nat := 116270961908740099253081

theorem tailTrace_1528449 : CollatzResearch.WordTrace tailWord_1528449 prefixEnd_1528449 116270961908740099253081 := by
  unfold tailWord_1528449
  simp only [CollatzResearch.WordTrace]
  refine ⟨55747114839697786151988401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37164743226465190767992267 55747114839697786151988401)
  ·
    refine ⟨41810336129773339613991301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55747114839697786151988401 41810336129773339613991301)
    ·
      refine ⟨7839438024332501177623369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41810336129773339613991301 7839438024332501177623369)
      ·
        refine ⟨5879578518249375883217527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7839438024332501177623369 5879578518249375883217527)
        ·
          refine ⟨8819367777374063824826291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5879578518249375883217527 8819367777374063824826291)
          ·
            refine ⟨13229051666061095737239437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8819367777374063824826291 13229051666061095737239437)
            ·
              refine ⟨4960894374772910901464789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13229051666061095737239437 4960894374772910901464789)
              ·
                refine ⟨116270961908740099253081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4960894374772910901464789 116270961908740099253081)
                ·
                  rfl

theorem cell21_1528449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 7].length) (baseStart_1528449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1528449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1528449 prefixEnd_1528449 := by exact prefixLift 1528449
  have htrace : WordTrace (prefixWord ++ tailWord_1528449) baseStart_1528449 baseEnd_1528449 := by
    simpa [prefixWord, tailWord_1528449, baseEnd_1528449] using wordTrace_append hprefix tailTrace_1528449
  have hstable : (prefixWord ++ tailWord_1528449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528449).length < 2 ^ (prefixWord ++ tailWord_1528449).sum := by decide
  have hdescent : baseEnd_1528449 < baseStart_1528449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528466 : List Nat := [3, 2, 3, 1, 2, 3, 7]
def baseStart_1528466 : Nat := 118140960795 + 1528466 * 2 ^ 59
def prefixEnd_1528466 : Nat := 4983230072969 + 3 ^ 40 * 1528466 * 2
def baseEnd_1528466 : Nat := 38757418373092449552875

theorem tailTrace_1528466 : CollatzResearch.WordTrace tailWord_1528466 prefixEnd_1528466 38757418373092449552875 := by
  unfold tailWord_1528466
  simp only [CollatzResearch.WordTrace]
  refine ⟨13936933720159049513839313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37165156587090798703571501 13936933720159049513839313)
  ·
    refine ⟨10452700290119287135379485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13936933720159049513839313 10452700290119287135379485)
    ·
      refine ⟨3919762608794732675767307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10452700290119287135379485 3919762608794732675767307)
      ·
        refine ⟨5879643913192099013650961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3919762608794732675767307 5879643913192099013650961)
        ·
          refine ⟨4409732934894074260238221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5879643913192099013650961 4409732934894074260238221)
          ·
            refine ⟨1653649850585277847589333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4409732934894074260238221 1653649850585277847589333)
            ·
              refine ⟨38757418373092449552875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1653649850585277847589333 38757418373092449552875)
              ·
                rfl

theorem cell21_1528466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 7].length) (baseStart_1528466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1528466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1528466 prefixEnd_1528466 := by exact prefixLift 1528466
  have htrace : WordTrace (prefixWord ++ tailWord_1528466) baseStart_1528466 baseEnd_1528466 := by
    simpa [prefixWord, tailWord_1528466, baseEnd_1528466] using wordTrace_append hprefix tailTrace_1528466
  have hstable : (prefixWord ++ tailWord_1528466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528466).length < 2 ^ (prefixWord ++ tailWord_1528466).sum := by decide
  have hdescent : baseEnd_1528466 < baseStart_1528466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528573 : List Nat := [1, 4, 1, 1, 1, 1, 6, 3, 3]
def baseStart_1528573 : Nat := 118140960795 + 1528573 * 2 ^ 59
def prefixEnd_1528573 : Nat := 4983230072969 + 3 ^ 40 * 1528573 * 2
def baseEnd_1528573 : Nat := 348841184215623637692323

theorem tailTrace_1528573 : CollatzResearch.WordTrace tailWord_1528573 prefixEnd_1528573 348841184215623637692323 := by
  unfold tailWord_1528573
  simp only [CollatzResearch.WordTrace]
  refine ⟨55751637491248555329502373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37167758327499036886334915 55751637491248555329502373)
  ·
    refine ⟨10453432029609104124281695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55751637491248555329502373 10453432029609104124281695)
    ·
      refine ⟨15680148044413656186422543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10453432029609104124281695 15680148044413656186422543)
      ·
        refine ⟨23520222066620484279633815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15680148044413656186422543 23520222066620484279633815)
        ·
          refine ⟨35280333099930726419450723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23520222066620484279633815 35280333099930726419450723)
          ·
            refine ⟨52920499649896089629176085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35280333099930726419450723 52920499649896089629176085)
            ·
              refine ⟨2480648421088879201367629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52920499649896089629176085 2480648421088879201367629)
              ·
                refine ⟨930243157908329700512861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2480648421088879201367629 930243157908329700512861)
                ·
                  refine ⟨348841184215623637692323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 930243157908329700512861 348841184215623637692323)
                  ·
                    rfl

theorem cell21_1528573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_1528573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1528573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1528573 prefixEnd_1528573 := by exact prefixLift 1528573
  have htrace : WordTrace (prefixWord ++ tailWord_1528573) baseStart_1528573 baseEnd_1528573 := by
    simpa [prefixWord, tailWord_1528573, baseEnd_1528573] using wordTrace_append hprefix tailTrace_1528573
  have hstable : (prefixWord ++ tailWord_1528573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528573).length < 2 ^ (prefixWord ++ tailWord_1528573).sum := by decide
  have hdescent : baseEnd_1528573 < baseStart_1528573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528604 : List Nat := [2, 2, 3, 1, 1, 4, 3, 1, 4]
def baseStart_1528604 : Nat := 118140960795 + 1528604 * 2 ^ 59
def prefixEnd_1528604 : Nat := 4983230072969 + 3 ^ 40 * 1528604 * 2
def baseEnd_1528604 : Nat := 348848258837974472675593

theorem tailTrace_1528604 : CollatzResearch.WordTrace tailWord_1528604 prefixEnd_1528604 348848258837974472675593 := by
  unfold tailWord_1528604
  simp only [CollatzResearch.WordTrace]
  refine ⟨27876384077068123811940433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37168512102757498415920577 27876384077068123811940433)
  ·
    refine ⟨20907288057801092858955325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27876384077068123811940433 20907288057801092858955325)
    ·
      refine ⟨7840233021675409822108247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20907288057801092858955325 7840233021675409822108247)
      ·
        refine ⟨11760349532513114733162371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7840233021675409822108247 11760349532513114733162371)
        ·
          refine ⟨17640524298769672099743557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11760349532513114733162371 17640524298769672099743557)
          ·
            refine ⟨3307598306019313518701917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17640524298769672099743557 3307598306019313518701917)
            ·
              refine ⟨1240349364757242569513219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3307598306019313518701917 1240349364757242569513219)
              ·
                refine ⟨1860524047135863854269829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1240349364757242569513219 1860524047135863854269829)
                ·
                  refine ⟨348848258837974472675593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1860524047135863854269829 348848258837974472675593)
                  ·
                    rfl

theorem cell21_1528604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_1528604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1528604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1528604 prefixEnd_1528604 := by exact prefixLift 1528604
  have htrace : WordTrace (prefixWord ++ tailWord_1528604) baseStart_1528604 baseEnd_1528604 := by
    simpa [prefixWord, tailWord_1528604, baseEnd_1528604] using wordTrace_append hprefix tailTrace_1528604
  have hstable : (prefixWord ++ tailWord_1528604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528604).length < 2 ^ (prefixWord ++ tailWord_1528604).sum := by decide
  have hdescent : baseEnd_1528604 < baseStart_1528604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528663 : List Nat := [1, 1, 3, 2, 4, 2, 1, 3, 4]
def baseStart_1528663 : Nat := 118140960795 + 1528663 * 2 ^ 59
def prefixEnd_1528663 : Nat := 4983230072969 + 3 ^ 40 * 1528663 * 2
def baseEnd_1528663 : Nat := 348861723441803481192139

theorem tailTrace_1528663 : CollatzResearch.WordTrace tailWord_1528663 prefixEnd_1528663 348861723441803481192139 := by
  unfold tailWord_1528663
  simp only [CollatzResearch.WordTrace]
  refine ⟨55754920060922500700278643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37169946707281667133519095 55754920060922500700278643)
  ·
    refine ⟨83632380091383751050417965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55754920060922500700278643 83632380091383751050417965)
    ·
      refine ⟨31362142534268906643906737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83632380091383751050417965 31362142534268906643906737)
      ·
        refine ⟨23521606900701679982930053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31362142534268906643906737 23521606900701679982930053)
        ·
          refine ⟨4410301293881564996799385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23521606900701679982930053 4410301293881564996799385)
          ·
            refine ⟨3307725970411173747599539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4410301293881564996799385 3307725970411173747599539)
            ·
              refine ⟨4961588955616760621399309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3307725970411173747599539 4961588955616760621399309)
              ·
                refine ⟨1860595858356285233024741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4961588955616760621399309 1860595858356285233024741)
                ·
                  refine ⟨348861723441803481192139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1860595858356285233024741 348861723441803481192139)
                  ·
                    rfl

theorem cell21_1528663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 4].length) (baseStart_1528663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1528663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1528663 prefixEnd_1528663 := by exact prefixLift 1528663
  have htrace : WordTrace (prefixWord ++ tailWord_1528663) baseStart_1528663 baseEnd_1528663 := by
    simpa [prefixWord, tailWord_1528663, baseEnd_1528663] using wordTrace_append hprefix tailTrace_1528663
  have hstable : (prefixWord ++ tailWord_1528663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528663).length < 2 ^ (prefixWord ++ tailWord_1528663).sum := by decide
  have hdescent : baseEnd_1528663 < baseStart_1528663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528736 : List Nat := [2, 1, 1, 4, 1, 1, 2, 9]
def baseStart_1528736 : Nat := 118140960795 + 1528736 * 2 ^ 59
def prefixEnd_1528736 : Nat := 4983230072969 + 3 ^ 40 * 1528736 * 2
def baseEnd_1528736 : Nat := 116292794345457192158441

theorem tailTrace_1528736 : CollatzResearch.WordTrace tailWord_1528736 prefixEnd_1528736 116292794345457192158441 := by
  unfold tailWord_1528736
  simp only [CollatzResearch.WordTrace]
  refine ⟨27878791294829017083843031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37171721726438689445124041 27878791294829017083843031)
  ·
    refine ⟨41818186942243525625764547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27878791294829017083843031 41818186942243525625764547)
    ·
      refine ⟨62727280413365288438646821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41818186942243525625764547 62727280413365288438646821)
      ·
        refine ⟨11761365077505991582246279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62727280413365288438646821 11761365077505991582246279)
        ·
          refine ⟨17642047616258987373369419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11761365077505991582246279 17642047616258987373369419)
          ·
            refine ⟨26463071424388481060054129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17642047616258987373369419 26463071424388481060054129)
            ·
              refine ⟨19847303568291360795040597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26463071424388481060054129 19847303568291360795040597)
              ·
                refine ⟨116292794345457192158441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19847303568291360795040597 116292794345457192158441)
                ·
                  rfl

theorem cell21_1528736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 9].length) (baseStart_1528736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1528736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1528736 prefixEnd_1528736 := by exact prefixLift 1528736
  have htrace : WordTrace (prefixWord ++ tailWord_1528736) baseStart_1528736 baseEnd_1528736 := by
    simpa [prefixWord, tailWord_1528736, baseEnd_1528736] using wordTrace_append hprefix tailTrace_1528736
  have hstable : (prefixWord ++ tailWord_1528736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528736).length < 2 ^ (prefixWord ++ tailWord_1528736).sum := by decide
  have hdescent : baseEnd_1528736 < baseStart_1528736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528753 : List Nat := [1, 2, 2, 4, 3, 1, 8]
def baseStart_1528753 : Nat := 118140960795 + 1528753 * 2 ^ 59
def prefixEnd_1528753 : Nat := 4983230072969 + 3 ^ 40 * 1528753 * 2
def baseEnd_1528753 : Nat := 38764695851998147187995

theorem tailTrace_1528753 : CollatzResearch.WordTrace tailWord_1528753 prefixEnd_1528753 38764695851998147187995 := by
  unfold tailWord_1528753
  simp only [CollatzResearch.WordTrace]
  refine ⟨55758202630596446071054913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37172135087064297380703275 55758202630596446071054913)
  ·
    refine ⟨41818651972947334553291185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55758202630596446071054913 41818651972947334553291185)
    ·
      refine ⟨31363988979710500914968389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41818651972947334553291185 31363988979710500914968389)
      ·
        refine ⟨5880747933695718921556573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31363988979710500914968389 5880747933695718921556573)
        ·
          refine ⟨2205280475135894595583715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5880747933695718921556573 2205280475135894595583715)
          ·
            refine ⟨3307920712703841893375573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2205280475135894595583715 3307920712703841893375573)
            ·
              refine ⟨38764695851998147187995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3307920712703841893375573 38764695851998147187995)
              ·
                rfl

theorem cell21_1528753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 8].length) (baseStart_1528753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1528753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1528753 prefixEnd_1528753 := by exact prefixLift 1528753
  have htrace : WordTrace (prefixWord ++ tailWord_1528753) baseStart_1528753 baseEnd_1528753 := by
    simpa [prefixWord, tailWord_1528753, baseEnd_1528753] using wordTrace_append hprefix tailTrace_1528753
  have hstable : (prefixWord ++ tailWord_1528753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528753).length < 2 ^ (prefixWord ++ tailWord_1528753).sum := by decide
  have hdescent : baseEnd_1528753 < baseStart_1528753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528756 : List Nat := [2, 5, 2, 1, 1, 2, 1, 1, 6]
def baseStart_1528756 : Nat := 118140960795 + 1528756 * 2 ^ 59
def prefixEnd_1528756 : Nat := 4983230072969 + 3 ^ 40 * 1528756 * 2
def baseEnd_1528756 : Nat := 348882947308855986141949

theorem tailTrace_1528756 : CollatzResearch.WordTrace tailWord_1528756 prefixEnd_1528756 348882947308855986141949 := by
  unfold tailWord_1528756
  simp only [CollatzResearch.WordTrace]
  refine ⟨27879156024792788791707061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37172208033057051722276081 27879156024792788791707061)
  ·
    refine ⟨2613670877324323949222537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27879156024792788791707061 2613670877324323949222537)
    ·
      refine ⟨1960253157993242961916903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2613670877324323949222537 1960253157993242961916903)
      ·
        refine ⟨2940379736989864442875355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1960253157993242961916903 2940379736989864442875355)
        ·
          refine ⟨4410569605484796664313033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2940379736989864442875355 4410569605484796664313033)
          ·
            refine ⟨3307927204113597498234775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4410569605484796664313033 3307927204113597498234775)
            ·
              refine ⟨4961890806170396247352163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3307927204113597498234775 4961890806170396247352163)
              ·
                refine ⟨7442836209255594371028245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4961890806170396247352163 7442836209255594371028245)
                ·
                  refine ⟨348882947308855986141949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7442836209255594371028245 348882947308855986141949)
                  ·
                    rfl

theorem cell21_1528756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_1528756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1528756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1528756 prefixEnd_1528756 := by exact prefixLift 1528756
  have htrace : WordTrace (prefixWord ++ tailWord_1528756) baseStart_1528756 baseEnd_1528756 := by
    simpa [prefixWord, tailWord_1528756, baseEnd_1528756] using wordTrace_append hprefix tailTrace_1528756
  have hstable : (prefixWord ++ tailWord_1528756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528756).length < 2 ^ (prefixWord ++ tailWord_1528756).sum := by decide
  have hdescent : baseEnd_1528756 < baseStart_1528756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528818 : List Nat := [3, 2, 1, 5, 1, 2, 1, 1, 5]
def baseStart_1528818 : Nat := 118140960795 + 1528818 * 2 ^ 59
def prefixEnd_1528818 : Nat := 4983230072969 + 3 ^ 40 * 1528818 * 2
def baseEnd_1528818 : Nat := 348897096553557656108489

theorem tailTrace_1528818 : CollatzResearch.WordTrace tailWord_1528818 prefixEnd_1528818 348897096553557656108489 := by
  unfold tailWord_1528818
  simp only [CollatzResearch.WordTrace]
  refine ⟨13940143343840240543042777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37173715583573974781447405 13940143343840240543042777)
  ·
    refine ⟨10455107507880180407282083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13940143343840240543042777 10455107507880180407282083)
    ·
      refine ⟨15682661261820270610923125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10455107507880180407282083 15682661261820270610923125)
      ·
        refine ⟨1470249493295650369774043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15682661261820270610923125 1470249493295650369774043)
        ·
          refine ⟨2205374239943475554661065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1470249493295650369774043 2205374239943475554661065)
          ·
            refine ⟨1654030679957606665995799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2205374239943475554661065 1654030679957606665995799)
            ·
              refine ⟨2481046019936409998993699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1654030679957606665995799 2481046019936409998993699)
              ·
                refine ⟨3721569029904614998490549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2481046019936409998993699 3721569029904614998490549)
                ·
                  refine ⟨348897096553557656108489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3721569029904614998490549 348897096553557656108489)
                  ·
                    rfl

theorem cell21_1528818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_1528818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1528818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1528818 prefixEnd_1528818 := by exact prefixLift 1528818
  have htrace : WordTrace (prefixWord ++ tailWord_1528818) baseStart_1528818 baseEnd_1528818 := by
    simpa [prefixWord, tailWord_1528818, baseEnd_1528818] using wordTrace_append hprefix tailTrace_1528818
  have hstable : (prefixWord ++ tailWord_1528818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528818).length < 2 ^ (prefixWord ++ tailWord_1528818).sum := by decide
  have hdescent : baseEnd_1528818 < baseStart_1528818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528857 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 8]
def baseStart_1528857 : Nat := 118140960795 + 1528857 * 2 ^ 59
def prefixEnd_1528857 : Nat := 4983230072969 + 3 ^ 40 * 1528857 * 2
def baseEnd_1528857 : Nat := 348905996884902254958409

theorem tailTrace_1528857 : CollatzResearch.WordTrace tailWord_1528857 prefixEnd_1528857 348905996884902254958409 := by
  unfold tailWord_1528857
  simp only [CollatzResearch.WordTrace]
  refine ⟨55761995822219671832840825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37174663881479781221893883 55761995822219671832840825)
  ·
    refine ⟨41821496866664753874630619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55761995822219671832840825 41821496866664753874630619)
    ·
      refine ⟨62732245299997130811945929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41821496866664753874630619 62732245299997130811945929)
      ·
        refine ⟨47049183974997848108959447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62732245299997130811945929 47049183974997848108959447)
        ·
          refine ⟨70573775962496772163439171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47049183974997848108959447 70573775962496772163439171)
          ·
            refine ⟨105860663943745158245158757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70573775962496772163439171 105860663943745158245158757)
            ·
              refine ⟨19848874489452217170967267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105860663943745158245158757 19848874489452217170967267)
              ·
                refine ⟨29773311734178325756450901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19848874489452217170967267 29773311734178325756450901)
                ·
                  refine ⟨348905996884902254958409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29773311734178325756450901 348905996884902254958409)
                  ·
                    rfl

theorem cell21_1528857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_1528857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1528857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1528857 prefixEnd_1528857 := by exact prefixLift 1528857
  have htrace : WordTrace (prefixWord ++ tailWord_1528857) baseStart_1528857 baseEnd_1528857 := by
    simpa [prefixWord, tailWord_1528857, baseEnd_1528857] using wordTrace_append hprefix tailTrace_1528857
  have hstable : (prefixWord ++ tailWord_1528857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528857).length < 2 ^ (prefixWord ++ tailWord_1528857).sum := by decide
  have hdescent : baseEnd_1528857 < baseStart_1528857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528925 : List Nat := [1, 4, 4, 1, 2, 2, 1, 2, 4]
def baseStart_1528925 : Nat := 118140960795 + 1528925 * 2 ^ 59
def prefixEnd_1528925 : Nat := 4983230072969 + 3 ^ 40 * 1528925 * 2
def baseEnd_1528925 : Nat := 348921515411349247824937

theorem tailTrace_1528925 : CollatzResearch.WordTrace tailWord_1528925 prefixEnd_1528925 348921515411349247824937 := by
  unfold tailWord_1528925
  simp only [CollatzResearch.WordTrace]
  refine ⟨55764475985973319446316229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37176317323982212964210819 55764475985973319446316229)
  ·
    refine ⟨10455839247369997396184293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55764475985973319446316229 10455839247369997396184293)
    ·
      refine ⟨1960469858881874511784555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10455839247369997396184293 1960469858881874511784555)
      ·
        refine ⟨2940704788322811767676833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1960469858881874511784555 2940704788322811767676833)
        ·
          refine ⟨2205528591242108825757625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2940704788322811767676833 2205528591242108825757625)
          ·
            refine ⟨1654146443431581619318219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2205528591242108825757625 1654146443431581619318219)
            ·
              refine ⟨2481219665147372428977329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1654146443431581619318219 2481219665147372428977329)
              ·
                refine ⟨1860914748860529321732997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2481219665147372428977329 1860914748860529321732997)
                ·
                  refine ⟨348921515411349247824937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1860914748860529321732997 348921515411349247824937)
                  ·
                    rfl

theorem cell21_1528925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_1528925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1528925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1528925 prefixEnd_1528925 := by exact prefixLift 1528925
  have htrace : WordTrace (prefixWord ++ tailWord_1528925) baseStart_1528925 baseEnd_1528925 := by
    simpa [prefixWord, tailWord_1528925, baseEnd_1528925] using wordTrace_append hprefix tailTrace_1528925
  have hstable : (prefixWord ++ tailWord_1528925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528925).length < 2 ^ (prefixWord ++ tailWord_1528925).sum := by decide
  have hdescent : baseEnd_1528925 < baseStart_1528925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529057 : List Nat := [1, 2, 3, 1, 3, 4, 1, 6]
def baseStart_1529057 : Nat := 118140960795 + 1529057 * 2 ^ 59
def prefixEnd_1529057 : Nat := 4983230072969 + 3 ^ 40 * 1529057 * 2
def baseEnd_1529057 : Nat := 116317213203248783874889

theorem tailTrace_1529057 : CollatzResearch.WordTrace tailWord_1529057 prefixEnd_1529057 116317213203248783874889 := by
  unfold tailWord_1529057
  simp only [CollatzResearch.WordTrace]
  refine ⟨55769290421495105990121425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37179526947663403993414283 55769290421495105990121425)
  ·
    refine ⟨41826967816121329492591069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55769290421495105990121425 41826967816121329492591069)
    ·
      refine ⟨15685112931045498559721651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41826967816121329492591069 15685112931045498559721651)
      ·
        refine ⟨23527669396568247839582477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15685112931045498559721651 23527669396568247839582477)
        ·
          refine ⟨8822876023713092939843429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23527669396568247839582477 8822876023713092939843429)
          ·
            refine ⟨1654289254446204926220643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8822876023713092939843429 1654289254446204926220643)
            ·
              refine ⟨2481433881669307389330965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1654289254446204926220643 2481433881669307389330965)
              ·
                refine ⟨116317213203248783874889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2481433881669307389330965 116317213203248783874889)
                ·
                  rfl

theorem cell21_1529057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 6].length) (baseStart_1529057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1529057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1529057 prefixEnd_1529057 := by exact prefixLift 1529057
  have htrace : WordTrace (prefixWord ++ tailWord_1529057) baseStart_1529057 baseEnd_1529057 := by
    simpa [prefixWord, tailWord_1529057, baseEnd_1529057] using wordTrace_append hprefix tailTrace_1529057
  have hstable : (prefixWord ++ tailWord_1529057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529057).length < 2 ^ (prefixWord ++ tailWord_1529057).sum := by decide
  have hdescent : baseEnd_1529057 < baseStart_1529057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529074 : List Nat := [3, 2, 1, 3, 3, 1, 3, 5]
def baseStart_1529074 : Nat := 118140960795 + 1529074 * 2 ^ 59
def prefixEnd_1529074 : Nat := 4983230072969 + 3 ^ 40 * 1529074 * 2
def baseEnd_1529074 : Nat := 116318506413786033280433

theorem tailTrace_1529074 : CollatzResearch.WordTrace tailWord_1529074 prefixEnd_1529074 116318506413786033280433 := by
  unfold tailWord_1529074
  simp only [CollatzResearch.WordTrace]
  refine ⟨13942477615608379473372569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37179940308289011928993517 13942477615608379473372569)
  ·
    refine ⟨10456858211706284605029427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13942477615608379473372569 10456858211706284605029427)
    ·
      refine ⟨15685287317559426907544141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10456858211706284605029427 15685287317559426907544141)
      ·
        refine ⟨5881982744084785090329053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15685287317559426907544141 5881982744084785090329053)
        ·
          refine ⟨2205743529031794408873395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5881982744084785090329053 2205743529031794408873395)
          ·
            refine ⟨3308615293547691613310093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2205743529031794408873395 3308615293547691613310093)
            ·
              refine ⟨1240730735080384354991285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3308615293547691613310093 1240730735080384354991285)
              ·
                refine ⟨116318506413786033280433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1240730735080384354991285 116318506413786033280433)
                ·
                  rfl

theorem cell21_1529074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 5].length) (baseStart_1529074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1529074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1529074 prefixEnd_1529074 := by exact prefixLift 1529074
  have htrace : WordTrace (prefixWord ++ tailWord_1529074) baseStart_1529074 baseEnd_1529074 := by
    simpa [prefixWord, tailWord_1529074, baseEnd_1529074] using wordTrace_append hprefix tailTrace_1529074
  have hstable : (prefixWord ++ tailWord_1529074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529074).length < 2 ^ (prefixWord ++ tailWord_1529074).sum := by decide
  have hdescent : baseEnd_1529074 < baseStart_1529074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529102 : List Nat := [4, 1, 1, 2, 1, 4, 1, 1, 6]
def baseStart_1529102 : Nat := 118140960795 + 1529102 * 2 ^ 59
def prefixEnd_1529102 : Nat := 4983230072969 + 3 ^ 40 * 1529102 * 2
def baseEnd_1529102 : Nat := 348961909222836273374575

theorem tailTrace_1529102 : CollatzResearch.WordTrace tailWord_1529102 prefixEnd_1529102 348961909222836273374575 := by
  unfold tailWord_1529102
  simp only [CollatzResearch.WordTrace]
  refine ⟨6971366463291509834438695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37180621137554719117006373 6971366463291509834438695)
  ·
    refine ⟨10457049694937264751658043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6971366463291509834438695 10457049694937264751658043)
    ·
      refine ⟨15685574542405897127487065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10457049694937264751658043 15685574542405897127487065)
      ·
        refine ⟨11764180906804422845615299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15685574542405897127487065 11764180906804422845615299)
        ·
          refine ⟨17646271360206634268422949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11764180906804422845615299 17646271360206634268422949)
          ·
            refine ⟨3308675880038743925329303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17646271360206634268422949 3308675880038743925329303)
            ·
              refine ⟨4963013820058115887993955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3308675880038743925329303 4963013820058115887993955)
              ·
                refine ⟨7444520730087173831990933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4963013820058115887993955 7444520730087173831990933)
                ·
                  refine ⟨348961909222836273374575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7444520730087173831990933 348961909222836273374575)
                  ·
                    rfl

theorem cell21_1529102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_1529102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1529102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1529102 prefixEnd_1529102 := by exact prefixLift 1529102
  have htrace : WordTrace (prefixWord ++ tailWord_1529102) baseStart_1529102 baseEnd_1529102 := by
    simpa [prefixWord, tailWord_1529102, baseEnd_1529102] using wordTrace_append hprefix tailTrace_1529102
  have hstable : (prefixWord ++ tailWord_1529102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529102).length < 2 ^ (prefixWord ++ tailWord_1529102).sum := by decide
  have hdescent : baseEnd_1529102 < baseStart_1529102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529161 : List Nat := [1, 2, 1, 1, 2, 3, 4, 1, 6]
def baseStart_1529161 : Nat := 118140960795 + 1529161 * 2 ^ 59
def prefixEnd_1529161 : Nat := 4983230072969 + 3 ^ 40 * 1529161 * 2
def baseEnd_1529161 : Nat := 348975373826665281891121

theorem tailTrace_1529161 : CollatzResearch.WordTrace tailWord_1529161 prefixEnd_1529161 348975373826665281891121 := by
  unfold tailWord_1529161
  simp only [CollatzResearch.WordTrace]
  refine ⟨55773083613118331751907337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37182055742078887834604891 55773083613118331751907337)
  ·
    refine ⟨41829812709838748813930503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55773083613118331751907337 41829812709838748813930503)
    ·
      refine ⟨62744719064758123220895755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41829812709838748813930503 62744719064758123220895755)
      ·
        refine ⟨94117078597137184831343633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62744719064758123220895755 94117078597137184831343633)
        ·
          refine ⟨70587808947852888623507725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94117078597137184831343633 70587808947852888623507725)
          ·
            refine ⟨26470428355444833233815397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70587808947852888623507725 26470428355444833233815397)
            ·
              refine ⟨4963205316645906231340387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26470428355444833233815397 4963205316645906231340387)
              ·
                refine ⟨7444807974968859347010581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4963205316645906231340387 7444807974968859347010581)
                ·
                  refine ⟨348975373826665281891121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7444807974968859347010581 348975373826665281891121)
                  ·
                    rfl

theorem cell21_1529161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 6].length) (baseStart_1529161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1529161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1529161 prefixEnd_1529161 := by exact prefixLift 1529161
  have htrace : WordTrace (prefixWord ++ tailWord_1529161) baseStart_1529161 baseEnd_1529161 := by
    simpa [prefixWord, tailWord_1529161, baseEnd_1529161] using wordTrace_append hprefix tailTrace_1529161
  have hstable : (prefixWord ++ tailWord_1529161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529161).length < 2 ^ (prefixWord ++ tailWord_1529161).sum := by decide
  have hdescent : baseEnd_1529161 < baseStart_1529161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529164 : List Nat := [2, 2, 1, 3, 2, 4, 1, 1, 5]
def baseStart_1529164 : Nat := 118140960795 + 1529164 * 2 ^ 59
def prefixEnd_1529164 : Nat := 4983230072969 + 3 ^ 40 * 1529164 * 2
def baseEnd_1529164 : Nat := 348976058467537943341115

theorem tailTrace_1529164 : CollatzResearch.WordTrace tailWord_1529164 prefixEnd_1529164 348976058467537943341115 := by
  unfold tailWord_1529164
  simp only [CollatzResearch.WordTrace]
  refine ⟨27886596516053731632133273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37182128688071642176177697 27886596516053731632133273)
  ·
    refine ⟨20914947387040298724099955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27886596516053731632133273 20914947387040298724099955)
    ·
      refine ⟨31372421080560448086149933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20914947387040298724099955 31372421080560448086149933)
      ·
        refine ⟨11764657905210168032306225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31372421080560448086149933 11764657905210168032306225)
        ·
          refine ⟨8823493428907626024229669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11764657905210168032306225 8823493428907626024229669)
          ·
            refine ⟨1654405017920179879543063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8823493428907626024229669 1654405017920179879543063)
            ·
              refine ⟨2481607526880269819314595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1654405017920179879543063 2481607526880269819314595)
              ·
                refine ⟨3722411290320404728971893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2481607526880269819314595 3722411290320404728971893)
                ·
                  refine ⟨348976058467537943341115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3722411290320404728971893 348976058467537943341115)
                  ·
                    rfl

theorem cell21_1529164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_1529164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1529164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1529164 prefixEnd_1529164 := by exact prefixLift 1529164
  have htrace : WordTrace (prefixWord ++ tailWord_1529164) baseStart_1529164 baseEnd_1529164 := by
    simpa [prefixWord, tailWord_1529164, baseEnd_1529164] using wordTrace_append hprefix tailTrace_1529164
  have hstable : (prefixWord ++ tailWord_1529164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529164).length < 2 ^ (prefixWord ++ tailWord_1529164).sum := by decide
  have hdescent : baseEnd_1529164 < baseStart_1529164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529240 : List Nat := [2, 1, 2, 5, 2, 1, 1, 2, 5]
def baseStart_1529240 : Nat := 118140960795 + 1529240 * 2 ^ 59
def prefixEnd_1529240 : Nat := 4983230072969 + 3 ^ 40 * 1529240 * 2
def baseEnd_1529240 : Nat := 348993402702978700074293

theorem tailTrace_1529240 : CollatzResearch.WordTrace tailWord_1529240 prefixEnd_1529240 348993402702978700074293 := by
  unfold tailWord_1529240
  simp only [CollatzResearch.WordTrace]
  refine ⟨27887982489916064122016587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37183976653221418829355449 27887982489916064122016587)
  ·
    refine ⟨41831973734874096183024881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27887982489916064122016587 41831973734874096183024881)
    ·
      refine ⟨31373980301155572137268661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41831973734874096183024881 31373980301155572137268661)
      ·
        refine ⟨2941310653233334887868937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31373980301155572137268661 2941310653233334887868937)
        ·
          refine ⟨2205982989925001165901703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2941310653233334887868937 2205982989925001165901703)
          ·
            refine ⟨3308974484887501748852555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2205982989925001165901703 3308974484887501748852555)
            ·
              refine ⟨4963461727331252623278833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3308974484887501748852555 4963461727331252623278833)
              ·
                refine ⟨3722596295498439467459125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4963461727331252623278833 3722596295498439467459125)
                ·
                  refine ⟨348993402702978700074293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3722596295498439467459125 348993402702978700074293)
                  ·
                    rfl

theorem cell21_1529240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 5].length) (baseStart_1529240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1529240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1529240 prefixEnd_1529240 := by exact prefixLift 1529240
  have htrace : WordTrace (prefixWord ++ tailWord_1529240) baseStart_1529240 baseEnd_1529240 := by
    simpa [prefixWord, tailWord_1529240, baseEnd_1529240] using wordTrace_append hprefix tailTrace_1529240
  have hstable : (prefixWord ++ tailWord_1529240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529240).length < 2 ^ (prefixWord ++ tailWord_1529240).sum := by decide
  have hdescent : baseEnd_1529240 < baseStart_1529240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529302 : List Nat := [5, 2, 1, 1, 1, 2, 4, 5]
def baseStart_1529302 : Nat := 118140960795 + 1529302 * 2 ^ 59
def prefixEnd_1529302 : Nat := 4983230072969 + 3 ^ 40 * 1529302 * 2
def baseEnd_1529302 : Nat := 116335850649226790013611

theorem tailTrace_1529302 : CollatzResearch.WordTrace tailWord_1529302 prefixEnd_1529302 116335850649226790013611 := by
  unfold tailWord_1529302
  simp only [CollatzResearch.WordTrace]
  refine ⟨3486139144100469552049385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37185484203738341888526773 3486139144100469552049385)
  ·
    refine ⟨2614604358075352164037039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3486139144100469552049385 2614604358075352164037039)
    ·
      refine ⟨3921906537113028246055559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2614604358075352164037039 3921906537113028246055559)
      ·
        refine ⟨5882859805669542369083339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3921906537113028246055559 5882859805669542369083339)
        ·
          refine ⟨8824289708504313553625009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5882859805669542369083339 8824289708504313553625009)
          ·
            refine ⟨6618217281378235165218757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8824289708504313553625009 6618217281378235165218757)
            ·
              refine ⟨1240915740258419093478517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6618217281378235165218757 1240915740258419093478517)
              ·
                refine ⟨116335850649226790013611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1240915740258419093478517 116335850649226790013611)
                ·
                  rfl

theorem cell21_1529302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_1529302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1529302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1529302 prefixEnd_1529302 := by exact prefixLift 1529302
  have htrace : WordTrace (prefixWord ++ tailWord_1529302) baseStart_1529302 baseEnd_1529302 := by
    simpa [prefixWord, tailWord_1529302, baseEnd_1529302] using wordTrace_append hprefix tailTrace_1529302
  have hstable : (prefixWord ++ tailWord_1529302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529302).length < 2 ^ (prefixWord ++ tailWord_1529302).sum := by decide
  have hdescent : baseEnd_1529302 < baseStart_1529302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529313 : List Nat := [1, 2, 3, 1, 2, 3, 1, 2, 6]
def baseStart_1529313 : Nat := 118140960795 + 1529313 * 2 ^ 59
def prefixEnd_1529313 : Nat := 4983230072969 + 3 ^ 40 * 1529313 * 2
def baseEnd_1529313 : Nat := 349010062297546795357477

theorem tailTrace_1529313 : CollatzResearch.WordTrace tailWord_1529313 prefixEnd_1529313 349010062297546795357477 := by
  unfold tailWord_1529313
  simp only [CollatzResearch.WordTrace]
  refine ⟨55778627508567661711440593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37185751672378441140960395 55778627508567661711440593)
  ·
    refine ⟨41833970631425746283580445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55778627508567661711440593 41833970631425746283580445)
    ·
      refine ⟨15687738986784654856342667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41833970631425746283580445 15687738986784654856342667)
      ·
        refine ⟨23531608480176982284514001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15687738986784654856342667 23531608480176982284514001)
        ·
          refine ⟨17648706360132736713385501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23531608480176982284514001 17648706360132736713385501)
          ·
            refine ⟨6618264885049776267519563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17648706360132736713385501 6618264885049776267519563)
            ·
              refine ⟨9927397327574664401279345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6618264885049776267519563 9927397327574664401279345)
              ·
                refine ⟨7445547995680998300959509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9927397327574664401279345 7445547995680998300959509)
                ·
                  refine ⟨349010062297546795357477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7445547995680998300959509 349010062297546795357477)
                  ·
                    rfl

theorem cell21_1529313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 6].length) (baseStart_1529313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1529313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1529313 prefixEnd_1529313 := by exact prefixLift 1529313
  have htrace : WordTrace (prefixWord ++ tailWord_1529313) baseStart_1529313 baseEnd_1529313 := by
    simpa [prefixWord, tailWord_1529313, baseEnd_1529313] using wordTrace_append hprefix tailTrace_1529313
  have hstable : (prefixWord ++ tailWord_1529313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529313).length < 2 ^ (prefixWord ++ tailWord_1529313).sum := by decide
  have hdescent : baseEnd_1529313 < baseStart_1529313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529327 : List Nat := [1, 1, 2, 1, 4, 1, 11]
def baseStart_1529327 : Nat := 118140960795 + 1529327 * 2 ^ 59
def prefixEnd_1529327 : Nat := 4983230072969 + 3 ^ 40 * 1529327 * 2
def baseEnd_1529327 : Nat := 38779250809809542458235

theorem tailTrace_1529327 : CollatzResearch.WordTrace tailWord_1529327 prefixEnd_1529327 38779250809809542458235 := by
  unfold tailWord_1529327
  simp only [CollatzResearch.WordTrace]
  refine ⟨55779138130516942102450235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37186092087011294734966823 55779138130516942102450235)
  ·
    refine ⟨83668707195775413153675353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55779138130516942102450235 83668707195775413153675353)
    ·
      refine ⟨62751530396831559865256515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83668707195775413153675353 62751530396831559865256515)
      ·
        refine ⟨94127295595247339797884773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62751530396831559865256515 94127295595247339797884773)
        ·
          refine ⟨17648867924108876212103395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94127295595247339797884773 17648867924108876212103395)
          ·
            refine ⟨26473301886163314318155093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17648867924108876212103395 26473301886163314318155093)
            ·
              refine ⟨38779250809809542458235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26473301886163314318155093 38779250809809542458235)
              ·
                rfl

theorem cell21_1529327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 11].length) (baseStart_1529327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1529327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1529327 prefixEnd_1529327 := by exact prefixLift 1529327
  have htrace : WordTrace (prefixWord ++ tailWord_1529327) baseStart_1529327 baseEnd_1529327 := by
    simpa [prefixWord, tailWord_1529327, baseEnd_1529327] using wordTrace_append hprefix tailTrace_1529327
  have hstable : (prefixWord ++ tailWord_1529327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529327).length < 2 ^ (prefixWord ++ tailWord_1529327).sum := by decide
  have hdescent : baseEnd_1529327 < baseStart_1529327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529330 : List Nat := [3, 2, 1, 4, 1, 1, 2, 1, 6]
def baseStart_1529330 : Nat := 118140960795 + 1529330 * 2 ^ 59
def prefixEnd_1529330 : Nat := 4983230072969 + 3 ^ 40 * 1529330 * 2
def baseEnd_1529330 : Nat := 349013941929158543574109

theorem tailTrace_1529330 : CollatzResearch.WordTrace tailWord_1529330 prefixEnd_1529330 349013941929158543574109 := by
  unfold tailWord_1529330
  simp only [CollatzResearch.WordTrace]
  refine ⟨13944811887376518403702361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37186165033004049076539629 13944811887376518403702361)
  ·
    refine ⟨10458608915532388802776771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13944811887376518403702361 10458608915532388802776771)
    ·
      refine ⟨15687913373298583204165157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10458608915532388802776771 15687913373298583204165157)
      ·
        refine ⟨2941483757493484350780967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15687913373298583204165157 2941483757493484350780967)
        ·
          refine ⟨4412225636240226526171451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2941483757493484350780967 4412225636240226526171451)
          ·
            refine ⟨6618338454360339789257177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4412225636240226526171451 6618338454360339789257177)
            ·
              refine ⟨4963753840770254841942883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6618338454360339789257177 4963753840770254841942883)
              ·
                refine ⟨7445630761155382262914325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4963753840770254841942883 7445630761155382262914325)
                ·
                  refine ⟨349013941929158543574109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7445630761155382262914325 349013941929158543574109)
                  ·
                    rfl

theorem cell21_1529330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_1529330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1529330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1529330 prefixEnd_1529330 := by exact prefixLift 1529330
  have htrace : WordTrace (prefixWord ++ tailWord_1529330) baseStart_1529330 baseEnd_1529330 := by
    simpa [prefixWord, tailWord_1529330, baseEnd_1529330] using wordTrace_append hprefix tailTrace_1529330
  have hstable : (prefixWord ++ tailWord_1529330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529330).length < 2 ^ (prefixWord ++ tailWord_1529330).sum := by decide
  have hdescent : baseEnd_1529330 < baseStart_1529330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529333 : List Nat := [1, 3, 5, 1, 1, 3, 1, 1, 5]
def baseStart_1529333 : Nat := 118140960795 + 1529333 * 2 ^ 59
def prefixEnd_1529333 : Nat := 4983230072969 + 3 ^ 40 * 1529333 * 2
def baseEnd_1529333 : Nat := 349014626570031205024103

theorem tailTrace_1529333 : CollatzResearch.WordTrace tailWord_1529333 prefixEnd_1529333 349014626570031205024103 := by
  unfold tailWord_1529333
  simp only [CollatzResearch.WordTrace]
  refine ⟨55779356968495205127168653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37186237978996803418112435 55779356968495205127168653)
  ·
    refine ⟨20917258863185701922688245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55779356968495205127168653 20917258863185701922688245)
    ·
      refine ⟨1960993018423659555252023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20917258863185701922688245 1960993018423659555252023)
      ·
        refine ⟨2941489527635489332878035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1960993018423659555252023 2941489527635489332878035)
        ·
          refine ⟨4412234291453233999317053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2941489527635489332878035 4412234291453233999317053)
          ·
            refine ⟨1654587859294962749743895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4412234291453233999317053 1654587859294962749743895)
            ·
              refine ⟨2481881788942444124615843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1654587859294962749743895 2481881788942444124615843)
              ·
                refine ⟨3722822683413666186923765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2481881788942444124615843 3722822683413666186923765)
                ·
                  refine ⟨349014626570031205024103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3722822683413666186923765 349014626570031205024103)
                  ·
                    rfl

theorem cell21_1529333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_1529333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1529333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1529333 prefixEnd_1529333 := by exact prefixLift 1529333
  have htrace : WordTrace (prefixWord ++ tailWord_1529333) baseStart_1529333 baseEnd_1529333 := by
    simpa [prefixWord, tailWord_1529333, baseEnd_1529333] using wordTrace_append hprefix tailTrace_1529333
  have hstable : (prefixWord ++ tailWord_1529333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529333).length < 2 ^ (prefixWord ++ tailWord_1529333).sum := by decide
  have hdescent : baseEnd_1529333 < baseStart_1529333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529496 : List Nat := [2, 1, 2, 4, 1, 4, 7]
def baseStart_1529496 : Nat := 118140960795 + 1529496 * 2 ^ 59
def prefixEnd_1529496 : Nat := 4983230072969 + 3 ^ 40 * 1529496 * 2
def baseEnd_1529496 : Nat := 38783536154531015978567

theorem tailTrace_1529496 : CollatzResearch.WordTrace tailWord_1529496 prefixEnd_1529496 38783536154531015978567 := by
  unfold tailWord_1529496
  simp only [CollatzResearch.WordTrace]
  refine ⟨27892651033452341982676171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37190201377936455976901561 27892651033452341982676171)
  ·
    refine ⟨41838976550178512974014257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27892651033452341982676171 41838976550178512974014257)
    ·
      refine ⟨31379232412633884730510693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41838976550178512974014257 31379232412633884730510693)
      ·
        refine ⟨5883606077368853386970755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31379232412633884730510693 5883606077368853386970755)
        ·
          refine ⟨8825409116053280080456133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5883606077368853386970755 8825409116053280080456133)
          ·
            refine ⟨1654764209259990015085525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8825409116053280080456133 1654764209259990015085525)
            ·
              refine ⟨38783536154531015978567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1654764209259990015085525 38783536154531015978567)
              ·
                rfl

theorem cell21_1529496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 7].length) (baseStart_1529496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1529496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1529496 prefixEnd_1529496 := by exact prefixLift 1529496
  have htrace : WordTrace (prefixWord ++ tailWord_1529496) baseStart_1529496 baseEnd_1529496 := by
    simpa [prefixWord, tailWord_1529496, baseEnd_1529496] using wordTrace_append hprefix tailTrace_1529496
  have hstable : (prefixWord ++ tailWord_1529496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529496).length < 2 ^ (prefixWord ++ tailWord_1529496).sum := by decide
  have hdescent : baseEnd_1529496 < baseStart_1529496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529502 : List Nat := [4, 3, 1, 1, 1, 3, 3, 2, 3]
def baseStart_1529502 : Nat := 118140960795 + 1529502 * 2 ^ 59
def prefixEnd_1529502 : Nat := 4983230072969 + 3 ^ 40 * 1529502 * 2
def baseEnd_1529502 : Nat := 349053194672524466707091

theorem tailTrace_1529502 : CollatzResearch.WordTrace tailWord_1529502 prefixEnd_1529502 349053194672524466707091 := by
  unfold tailWord_1529502
  simp only [CollatzResearch.WordTrace]
  refine ⟨6973190113110368373758845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37190347269921964660047173 6973190113110368373758845)
  ·
    refine ⟨2614946292416388140159567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6973190113110368373758845 2614946292416388140159567)
    ·
      refine ⟨3922419438624582210239351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2614946292416388140159567 3922419438624582210239351)
      ·
        refine ⟨5883629157936873315359027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3922419438624582210239351 5883629157936873315359027)
        ·
          refine ⟨8825443736905309973038541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5883629157936873315359027 8825443736905309973038541)
          ·
            refine ⟨3309541401339491239889453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8825443736905309973038541 3309541401339491239889453)
            ·
              refine ⟨1241078025502309214958545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3309541401339491239889453 1241078025502309214958545)
              ·
                refine ⟨930808519126731911218909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1241078025502309214958545 930808519126731911218909)
                ·
                  refine ⟨349053194672524466707091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 930808519126731911218909 349053194672524466707091)
                  ·
                    rfl

theorem cell21_1529502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_1529502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1529502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1529502 prefixEnd_1529502 := by exact prefixLift 1529502
  have htrace : WordTrace (prefixWord ++ tailWord_1529502) baseStart_1529502 baseEnd_1529502 := by
    simpa [prefixWord, tailWord_1529502, baseEnd_1529502] using wordTrace_append hprefix tailTrace_1529502
  have hstable : (prefixWord ++ tailWord_1529502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529502).length < 2 ^ (prefixWord ++ tailWord_1529502).sum := by decide
  have hdescent : baseEnd_1529502 < baseStart_1529502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529561 : List Nat := [1, 2, 1, 2, 3, 5, 2, 2, 3]
def baseStart_1529561 : Nat := 118140960795 + 1529561 * 2 ^ 59
def prefixEnd_1529561 : Nat := 4983230072969 + 3 ^ 40 * 1529561 * 2
def baseEnd_1529561 : Nat := 349066659276353475223637

theorem tailTrace_1529561 : CollatzResearch.WordTrace tailWord_1529561 prefixEnd_1529561 349066659276353475223637 := by
  unfold tailWord_1529561
  simp only [CollatzResearch.WordTrace]
  refine ⟨55787672811669200066468537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37191781874446133377645691 55787672811669200066468537)
  ·
    refine ⟨41840754608751900049851403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55787672811669200066468537 41840754608751900049851403)
    ·
      refine ⟨62761131913127850074777105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41840754608751900049851403 62761131913127850074777105)
      ·
        refine ⟨47070848934845887556082829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62761131913127850074777105 47070848934845887556082829)
        ·
          refine ⟨17651568350567207833531061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47070848934845887556082829 17651568350567207833531061)
          ·
            refine ⟨1654834532865675734393537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17651568350567207833531061 1654834532865675734393537)
            ·
              refine ⟨1241125899649256800795153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1654834532865675734393537 1241125899649256800795153)
              ·
                refine ⟨930844424736942600596365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1241125899649256800795153 930844424736942600596365)
                ·
                  refine ⟨349066659276353475223637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 930844424736942600596365 349066659276353475223637)
                  ·
                    rfl

theorem cell21_1529561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2, 3].length) (baseStart_1529561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1529561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1529561 prefixEnd_1529561 := by exact prefixLift 1529561
  have htrace : WordTrace (prefixWord ++ tailWord_1529561) baseStart_1529561 baseEnd_1529561 := by
    simpa [prefixWord, tailWord_1529561, baseEnd_1529561] using wordTrace_append hprefix tailTrace_1529561
  have hstable : (prefixWord ++ tailWord_1529561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529561).length < 2 ^ (prefixWord ++ tailWord_1529561).sum := by decide
  have hdescent : baseEnd_1529561 < baseStart_1529561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529600 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 8]
def baseStart_1529600 : Nat := 118140960795 + 1529600 * 2 ^ 59
def prefixEnd_1529600 : Nat := 4983230072969 + 3 ^ 40 * 1529600 * 2
def baseEnd_1529600 : Nat := 349075559607698074073557

theorem tailTrace_1529600 : CollatzResearch.WordTrace tailWord_1529600 prefixEnd_1529600 349075559607698074073557 := by
  unfold tailWord_1529600
  simp only [CollatzResearch.WordTrace]
  refine ⟨27894547629263954863569127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37192730172351939818092169 27894547629263954863569127)
  ·
    refine ⟨41841821443895932295353691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27894547629263954863569127 41841821443895932295353691)
    ·
      refine ⟨62762732165843898443030537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41841821443895932295353691 62762732165843898443030537)
      ·
        refine ⟨47072049124382923832272903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62762732165843898443030537 47072049124382923832272903)
        ·
          refine ⟨70608073686574385748409355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47072049124382923832272903 70608073686574385748409355)
          ·
            refine ⟨105912110529861578622614033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70608073686574385748409355 105912110529861578622614033)
            ·
              refine ⟨79434082897396183966960525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105912110529861578622614033 79434082897396183966960525)
              ·
                refine ⟨29787781086523568987610197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79434082897396183966960525 29787781086523568987610197)
                ·
                  refine ⟨349075559607698074073557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29787781086523568987610197 349075559607698074073557)
                  ·
                    rfl

theorem cell21_1529600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_1529600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1529600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1529600 prefixEnd_1529600 := by exact prefixLift 1529600
  have htrace : WordTrace (prefixWord ++ tailWord_1529600) baseStart_1529600 baseEnd_1529600 := by
    simpa [prefixWord, tailWord_1529600, baseEnd_1529600] using wordTrace_append hprefix tailTrace_1529600
  have hstable : (prefixWord ++ tailWord_1529600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529600).length < 2 ^ (prefixWord ++ tailWord_1529600).sum := by decide
  have hdescent : baseEnd_1529600 < baseStart_1529600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529603 : List Nat := [1, 1, 1, 3, 2, 2, 3, 5, 3]
def baseStart_1529603 : Nat := 118140960795 + 1529603 * 2 ^ 59
def prefixEnd_1529603 : Nat := 4983230072969 + 3 ^ 40 * 1529603 * 2
def baseEnd_1529603 : Nat := 349076244248570735523551

theorem tailTrace_1529603 : CollatzResearch.WordTrace tailWord_1529603 prefixEnd_1529603 349076244248570735523551 := by
  unfold tailWord_1529603
  simp only [CollatzResearch.WordTrace]
  refine ⟨55789204677517041239497463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37192803118344694159664975 55789204677517041239497463)
  ·
    refine ⟨83683807016275561859246195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55789204677517041239497463 83683807016275561859246195)
    ·
      refine ⟨125525710524413342788869293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83683807016275561859246195 125525710524413342788869293)
      ·
        refine ⟨47072141446655003545825985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125525710524413342788869293 47072141446655003545825985)
        ·
          refine ⟨35304106084991252659369489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47072141446655003545825985 35304106084991252659369489)
          ·
            refine ⟨26478079563743439494527117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35304106084991252659369489 26478079563743439494527117)
            ·
              refine ⟨9929279836403789810447669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26478079563743439494527117 9929279836403789810447669)
              ·
                refine ⟨930869984662855294729469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9929279836403789810447669 930869984662855294729469)
                ·
                  refine ⟨349076244248570735523551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 930869984662855294729469 349076244248570735523551)
                  ·
                    rfl

theorem cell21_1529603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5, 3].length) (baseStart_1529603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1529603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1529603 prefixEnd_1529603 := by exact prefixLift 1529603
  have htrace : WordTrace (prefixWord ++ tailWord_1529603) baseStart_1529603 baseEnd_1529603 := by
    simpa [prefixWord, tailWord_1529603, baseEnd_1529603] using wordTrace_append hprefix tailTrace_1529603
  have hstable : (prefixWord ++ tailWord_1529603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529603).length < 2 ^ (prefixWord ++ tailWord_1529603).sum := by decide
  have hdescent : baseEnd_1529603 < baseStart_1529603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529631 : List Nat := [1, 1, 2, 4, 2, 1, 2, 8]
def baseStart_1529631 : Nat := 118140960795 + 1529631 * 2 ^ 59
def prefixEnd_1529631 : Nat := 4983230072969 + 3 ^ 40 * 1529631 * 2
def baseEnd_1529631 : Nat := 116360878076682969685609

theorem tailTrace_1529631 : CollatzResearch.WordTrace tailWord_1529631 prefixEnd_1529631 116360878076682969685609 := by
  unfold tailWord_1529631
  simp only [CollatzResearch.WordTrace]
  refine ⟨55790225921415602021516747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37193483947610401347677831 55790225921415602021516747)
  ·
    refine ⟨83685338882123403032275121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55790225921415602021516747 83685338882123403032275121)
    ·
      refine ⟨62764004161592552274206341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83685338882123403032275121 62764004161592552274206341)
      ·
        refine ⟨11768250780298603551413689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62764004161592552274206341 11768250780298603551413689)
        ·
          refine ⟨8826188085223952663560267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11768250780298603551413689 8826188085223952663560267)
          ·
            refine ⟨13239282127835928995340401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8826188085223952663560267 13239282127835928995340401)
            ·
              refine ⟨9929461595876946746505301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13239282127835928995340401 9929461595876946746505301)
              ·
                refine ⟨116360878076682969685609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9929461595876946746505301 116360878076682969685609)
                ·
                  rfl

theorem cell21_1529631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 8].length) (baseStart_1529631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1529631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1529631 prefixEnd_1529631 := by exact prefixLift 1529631
  have htrace : WordTrace (prefixWord ++ tailWord_1529631) baseStart_1529631 baseEnd_1529631 := by
    simpa [prefixWord, tailWord_1529631, baseEnd_1529631] using wordTrace_append hprefix tailTrace_1529631
  have hstable : (prefixWord ++ tailWord_1529631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529631).length < 2 ^ (prefixWord ++ tailWord_1529631).sum := by decide
  have hdescent : baseEnd_1529631 < baseStart_1529631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529654 : List Nat := [5, 1, 2, 2, 1, 3, 1, 3, 3]
def baseStart_1529654 : Nat := 118140960795 + 1529654 * 2 ^ 59
def prefixEnd_1529654 : Nat := 4983230072969 + 3 ^ 40 * 1529654 * 2
def baseEnd_1529654 : Nat := 349087883143405980173447

theorem tailTrace_1529654 : CollatzResearch.WordTrace tailWord_1529654 prefixEnd_1529654 349087883143405980173447 := by
  unfold tailWord_1529654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3486941550020767309350251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37194043200221517966402677 3486941550020767309350251)
  ·
    refine ⟨5230412325031150964025377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3486941550020767309350251 5230412325031150964025377)
    ·
      refine ⟨3922809243773363223019033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5230412325031150964025377 3922809243773363223019033)
      ·
        refine ⟨2942106932830022417264275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3922809243773363223019033 2942106932830022417264275)
        ·
          refine ⟨4413160399245033625896413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2942106932830022417264275 4413160399245033625896413)
          ·
            refine ⟨1654935149716887609711155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4413160399245033625896413 1654935149716887609711155)
            ·
              refine ⟨2482402724575331414566733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1654935149716887609711155 2482402724575331414566733)
              ·
                refine ⟨930901021715749280462525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2482402724575331414566733 930901021715749280462525)
                ·
                  refine ⟨349087883143405980173447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 930901021715749280462525 349087883143405980173447)
                  ·
                    rfl

theorem cell21_1529654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_1529654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1529654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1529654 prefixEnd_1529654 := by exact prefixLift 1529654
  have htrace : WordTrace (prefixWord ++ tailWord_1529654) baseStart_1529654 baseEnd_1529654 := by
    simpa [prefixWord, tailWord_1529654, baseEnd_1529654] using wordTrace_append hprefix tailTrace_1529654
  have hstable : (prefixWord ++ tailWord_1529654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529654).length < 2 ^ (prefixWord ++ tailWord_1529654).sum := by decide
  have hdescent : baseEnd_1529654 < baseStart_1529654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529817 : List Nat := [1, 2, 1, 2, 6, 2, 2, 5]
def baseStart_1529817 : Nat := 118140960795 + 1529817 * 2 ^ 59
def prefixEnd_1529817 : Nat := 4983230072969 + 3 ^ 40 * 1529817 * 2
def baseEnd_1529817 : Nat := 116375027321384639652149

theorem tailTrace_1529817 : CollatzResearch.WordTrace tailWord_1529817 prefixEnd_1529817 116375027321384639652149 := by
  unfold tailWord_1529817
  simp only [CollatzResearch.WordTrace]
  refine ⟨55797009898741755787787705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37198006599161170525191803 55797009898741755787787705)
  ·
    refine ⟨41847757424056316840840779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55797009898741755787787705 41847757424056316840840779)
    ·
      refine ⟨62771636136084475261261169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41847757424056316840840779 62771636136084475261261169)
      ·
        refine ⟨47078727102063356445945877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62771636136084475261261169 47078727102063356445945877)
        ·
          refine ⟨2206815332909219833403713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47078727102063356445945877 2206815332909219833403713)
          ·
            refine ⟨1655111499681914875052785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2206815332909219833403713 1655111499681914875052785)
            ·
              refine ⟨1241333624761436156289589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1655111499681914875052785 1241333624761436156289589)
              ·
                refine ⟨116375027321384639652149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1241333624761436156289589 116375027321384639652149)
                ·
                  rfl

theorem cell21_1529817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 5].length) (baseStart_1529817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1529817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1529817 prefixEnd_1529817 := by exact prefixLift 1529817
  have htrace : WordTrace (prefixWord ++ tailWord_1529817) baseStart_1529817 baseEnd_1529817 := by
    simpa [prefixWord, tailWord_1529817, baseEnd_1529817] using wordTrace_append hprefix tailTrace_1529817
  have hstable : (prefixWord ++ tailWord_1529817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529817).length < 2 ^ (prefixWord ++ tailWord_1529817).sum := by decide
  have hdescent : baseEnd_1529817 < baseStart_1529817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529828 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 8]
def baseStart_1529828 : Nat := 118140960795 + 1529828 * 2 ^ 59
def prefixEnd_1529828 : Nat := 4983230072969 + 3 ^ 40 * 1529828 * 2
def baseEnd_1529828 : Nat := 349127592314020344273091

theorem tailTrace_1529828 : CollatzResearch.WordTrace tailWord_1529828 prefixEnd_1529828 349127592314020344273091 := by
  unfold tailWord_1529828
  simp only [CollatzResearch.WordTrace]
  refine ⟨27898705550850952333219069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37198274067801269777625425 27898705550850952333219069)
  ·
    refine ⟨10462014581569107124957151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27898705550850952333219069 10462014581569107124957151)
    ·
      refine ⟨15693021872353660687435727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10462014581569107124957151 15693021872353660687435727)
      ·
        refine ⟨23539532808530491031153591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15693021872353660687435727 23539532808530491031153591)
        ·
          refine ⟨35309299212795736546730387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23539532808530491031153591 35309299212795736546730387)
          ·
            refine ⟨52963948819193604820095581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35309299212795736546730387 52963948819193604820095581)
            ·
              refine ⟨19861480807197601807535843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52963948819193604820095581 19861480807197601807535843)
              ·
                refine ⟨29792221210796402711303765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19861480807197601807535843 29792221210796402711303765)
                ·
                  refine ⟨349127592314020344273091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29792221210796402711303765 349127592314020344273091)
                  ·
                    rfl

theorem cell21_1529828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_1529828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1529828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1529828 prefixEnd_1529828 := by exact prefixLift 1529828
  have htrace : WordTrace (prefixWord ++ tailWord_1529828) baseStart_1529828 baseEnd_1529828 := by
    simpa [prefixWord, tailWord_1529828, baseEnd_1529828] using wordTrace_append hprefix tailTrace_1529828
  have hstable : (prefixWord ++ tailWord_1529828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529828).length < 2 ^ (prefixWord ++ tailWord_1529828).sum := by decide
  have hdescent : baseEnd_1529828 < baseStart_1529828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530135 : List Nat := [1, 1, 3, 4, 1, 2, 2, 4, 3]
def baseStart_1530135 : Nat := 118140960795 + 1530135 * 2 ^ 59
def prefixEnd_1530135 : Nat := 4983230072969 + 3 ^ 40 * 1530135 * 2
def baseEnd_1530135 : Nat := 349197653896656032655797

theorem tailTrace_1530135 : CollatzResearch.WordTrace tailWord_1530135 prefixEnd_1530135 349197653896656032655797 := by
  unfold tailWord_1530135
  simp only [CollatzResearch.WordTrace]
  refine ⟨55808608311589696097863859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37205738874393130731909239 55808608311589696097863859)
  ·
    refine ⟨83712912467384544146795789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55808608311589696097863859 83712912467384544146795789)
    ·
      refine ⟨31392342175269204055048421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83712912467384544146795789 31392342175269204055048421)
      ·
        refine ⟨5886064157862975760321579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31392342175269204055048421 5886064157862975760321579)
        ·
          refine ⟨8829096236794463640482369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5886064157862975760321579 8829096236794463640482369)
          ·
            refine ⟨6621822177595847730361777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8829096236794463640482369 6621822177595847730361777)
            ·
              refine ⟨4966366633196885797771333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6621822177595847730361777 4966366633196885797771333)
              ·
                refine ⟨931193743724416087082125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4966366633196885797771333 931193743724416087082125)
                ·
                  refine ⟨349197653896656032655797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 931193743724416087082125 349197653896656032655797)
                  ·
                    rfl

theorem cell21_1530135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4, 3].length) (baseStart_1530135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1530135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1530135 prefixEnd_1530135 := by exact prefixLift 1530135
  have htrace : WordTrace (prefixWord ++ tailWord_1530135) baseStart_1530135 baseEnd_1530135 := by
    simpa [prefixWord, tailWord_1530135, baseEnd_1530135] using wordTrace_append hprefix tailTrace_1530135
  have hstable : (prefixWord ++ tailWord_1530135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530135).length < 2 ^ (prefixWord ++ tailWord_1530135).sum := by decide
  have hdescent : baseEnd_1530135 < baseStart_1530135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530194 : List Nat := [3, 2, 2, 1, 1, 1, 5, 1, 5]
def baseStart_1530194 : Nat := 118140960795 + 1530194 * 2 ^ 59
def prefixEnd_1530194 : Nat := 4983230072969 + 3 ^ 40 * 1530194 * 2
def baseEnd_1530194 : Nat := 349211118500485041172343

theorem tailTrace_1530194 : CollatzResearch.WordTrace tailWord_1530194 prefixEnd_1530194 349211118500485041172343 := by
  unfold tailWord_1530194
  simp only [CollatzResearch.WordTrace]
  refine ⟨13952690054593987293565409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37207173478917299449507757 13952690054593987293565409)
  ·
    refine ⟨10464517540945490470174057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13952690054593987293565409 10464517540945490470174057)
    ·
      refine ⟨7848388155709117852630543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10464517540945490470174057 7848388155709117852630543)
      ·
        refine ⟨11772582233563676778945815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7848388155709117852630543 11772582233563676778945815)
        ·
          refine ⟨17658873350345515168418723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11772582233563676778945815 17658873350345515168418723)
          ·
            refine ⟨26488310025518272752628085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17658873350345515168418723 26488310025518272752628085)
            ·
              refine ⟨2483279064892338070558883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26488310025518272752628085 2483279064892338070558883)
              ·
                refine ⟨3724918597338507105838325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2483279064892338070558883 3724918597338507105838325)
                ·
                  refine ⟨349211118500485041172343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3724918597338507105838325 349211118500485041172343)
                  ·
                    rfl

theorem cell21_1530194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_1530194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1530194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1530194 prefixEnd_1530194 := by exact prefixLift 1530194
  have htrace : WordTrace (prefixWord ++ tailWord_1530194) baseStart_1530194 baseEnd_1530194 := by
    simpa [prefixWord, tailWord_1530194, baseEnd_1530194] using wordTrace_append hprefix tailTrace_1530194
  have hstable : (prefixWord ++ tailWord_1530194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530194).length < 2 ^ (prefixWord ++ tailWord_1530194).sum := by decide
  have hdescent : baseEnd_1530194 < baseStart_1530194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530273 : List Nat := [1, 2, 3, 5, 1, 1, 3, 5]
def baseStart_1530273 : Nat := 118140960795 + 1530273 * 2 ^ 59
def prefixEnd_1530273 : Nat := 4983230072969 + 3 ^ 40 * 1530273 * 2
def baseEnd_1530273 : Nat := 116409715792266153118505

theorem tailTrace_1530273 : CollatzResearch.WordTrace tailWord_1530273 prefixEnd_1530273 116409715792266153118505 := by
  unfold tailWord_1530273
  simp only [CollatzResearch.WordTrace]
  refine ⟨55813641585089745666387473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37209094390059830444258315 55813641585089745666387473)
  ·
    refine ⟨41860231188817309249790605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55813641585089745666387473 41860231188817309249790605)
    ·
      refine ⟨15697586695806490968671477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41860231188817309249790605 15697586695806490968671477)
      ·
        refine ⟨1471648752731858528312951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15697586695806490968671477 1471648752731858528312951)
        ·
          refine ⟨2207473129097787792469427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1471648752731858528312951 2207473129097787792469427)
          ·
            refine ⟨3311209693646681688704141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2207473129097787792469427 3311209693646681688704141)
            ·
              refine ⟨1241703635117505633264053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3311209693646681688704141 1241703635117505633264053)
              ·
                refine ⟨116409715792266153118505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1241703635117505633264053 116409715792266153118505)
                ·
                  rfl

theorem cell21_1530273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 5].length) (baseStart_1530273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1530273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1530273 prefixEnd_1530273 := by exact prefixLift 1530273
  have htrace : WordTrace (prefixWord ++ tailWord_1530273) baseStart_1530273 baseEnd_1530273 := by
    simpa [prefixWord, tailWord_1530273, baseEnd_1530273] using wordTrace_append hprefix tailTrace_1530273
  have hstable : (prefixWord ++ tailWord_1530273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530273).length < 2 ^ (prefixWord ++ tailWord_1530273).sum := by decide
  have hdescent : baseEnd_1530273 < baseStart_1530273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530301 : List Nat := [1, 4, 1, 2, 2, 2, 3, 2, 4]
def baseStart_1530301 : Nat := 118140960795 + 1530301 * 2 ^ 59
def prefixEnd_1530301 : Nat := 4983230072969 + 3 ^ 40 * 1530301 * 2
def baseEnd_1530301 : Nat := 349235537358276632888791

theorem tailTrace_1530301 : CollatzResearch.WordTrace tailWord_1530301 prefixEnd_1530301 349235537358276632888791 := by
  unfold tailWord_1530301
  simp only [CollatzResearch.WordTrace]
  refine ⟨55814662828988306448406757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37209775219325537632271171 55814662828988306448406757)
  ·
    refine ⟨10465249280435307459076267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55814662828988306448406757 10465249280435307459076267)
    ·
      refine ⟨15697873920652961188614401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10465249280435307459076267 15697873920652961188614401)
      ·
        refine ⟨11773405440489720891460801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15697873920652961188614401 11773405440489720891460801)
        ·
          refine ⟨8830054080367290668595601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11773405440489720891460801 8830054080367290668595601)
          ·
            refine ⟨6622540560275468001446701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8830054080367290668595601 6622540560275468001446701)
            ·
              refine ⟨2483452710103300500542513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6622540560275468001446701 2483452710103300500542513)
              ·
                refine ⟨1862589532577475375406885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2483452710103300500542513 1862589532577475375406885)
                ·
                  refine ⟨349235537358276632888791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1862589532577475375406885 349235537358276632888791)
                  ·
                    rfl

theorem cell21_1530301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_1530301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1530301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1530301 prefixEnd_1530301 := by exact prefixLift 1530301
  have htrace : WordTrace (prefixWord ++ tailWord_1530301) baseStart_1530301 baseEnd_1530301 := by
    simpa [prefixWord, tailWord_1530301, baseEnd_1530301] using wordTrace_append hprefix tailTrace_1530301
  have hstable : (prefixWord ++ tailWord_1530301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530301).length < 2 ^ (prefixWord ++ tailWord_1530301).sum := by decide
  have hdescent : baseEnd_1530301 < baseStart_1530301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530329 : List Nat := [1, 2, 1, 2, 4, 1, 1, 4, 5]
def baseStart_1530329 : Nat := 118140960795 + 1530329 * 2 ^ 59
def prefixEnd_1530329 : Nat := 4983230072969 + 3 ^ 40 * 1530329 * 2
def baseEnd_1530329 : Nat := 349241927339754806422067

theorem tailTrace_1530329 : CollatzResearch.WordTrace tailWord_1530329 prefixEnd_1530329 349241927339754806422067 := by
  unfold tailWord_1530329
  simp only [CollatzResearch.WordTrace]
  refine ⟨55815684072886867230426041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37210456048591244820284027 55815684072886867230426041)
  ·
    refine ⟨41861763054665150422819531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55815684072886867230426041 41861763054665150422819531)
    ·
      refine ⟨62792644581997725634229297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41861763054665150422819531 62792644581997725634229297)
      ·
        refine ⟨47094483436498294225671973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62792644581997725634229297 47094483436498294225671973)
        ·
          refine ⟨8830215644343430167313495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47094483436498294225671973 8830215644343430167313495)
          ·
            refine ⟨13245323466515145250970243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8830215644343430167313495 13245323466515145250970243)
            ·
              refine ⟨19867985199772717876455365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13245323466515145250970243 19867985199772717876455365)
              ·
                refine ⟨3725247224957384601835381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19867985199772717876455365 3725247224957384601835381)
                ·
                  refine ⟨349241927339754806422067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3725247224957384601835381 349241927339754806422067)
                  ·
                    rfl

theorem cell21_1530329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 5].length) (baseStart_1530329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1530329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1530329 prefixEnd_1530329 := by exact prefixLift 1530329
  have htrace : WordTrace (prefixWord ++ tailWord_1530329) baseStart_1530329 baseEnd_1530329 := by
    simpa [prefixWord, tailWord_1530329, baseEnd_1530329] using wordTrace_append hprefix tailTrace_1530329
  have hstable : (prefixWord ++ tailWord_1530329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530329).length < 2 ^ (prefixWord ++ tailWord_1530329).sum := by decide
  have hdescent : baseEnd_1530329 < baseStart_1530329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530338 : List Nat := [3, 3, 3, 2, 1, 2, 1, 3, 3]
def baseStart_1530338 : Nat := 118140960795 + 1530338 * 2 ^ 59
def prefixEnd_1530338 : Nat := 4983230072969 + 3 ^ 40 * 1530338 * 2
def baseEnd_1530338 : Nat := 349243981262372790772049

theorem tailTrace_1530338 : CollatzResearch.WordTrace tailWord_1530338 prefixEnd_1530338 349243981262372790772049 := by
  unfold tailWord_1530338
  simp only [CollatzResearch.WordTrace]
  refine ⟨13954003082463565441875917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37210674886569507845002445 13954003082463565441875917)
  ·
    refine ⟨5232751155923837040703469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13954003082463565441875917 5232751155923837040703469)
    ·
      refine ⟨1962281683471438890263801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5232751155923837040703469 1962281683471438890263801)
      ·
        refine ⟨1471711262603579167697851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1962281683471438890263801 1471711262603579167697851)
        ·
          refine ⟨2207566893905368751546777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1471711262603579167697851 2207566893905368751546777)
          ·
            refine ⟨1655675170429026563660083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2207566893905368751546777 1655675170429026563660083)
            ·
              refine ⟨2483512755643539845490125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1655675170429026563660083 2483512755643539845490125)
              ·
                refine ⟨931317283366327442058797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2483512755643539845490125 931317283366327442058797)
                ·
                  refine ⟨349243981262372790772049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 931317283366327442058797 349243981262372790772049)
                  ·
                    rfl

theorem cell21_1530338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_1530338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1530338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1530338 prefixEnd_1530338 := by exact prefixLift 1530338
  have htrace : WordTrace (prefixWord ++ tailWord_1530338) baseStart_1530338 baseEnd_1530338 := by
    simpa [prefixWord, tailWord_1530338, baseEnd_1530338] using wordTrace_append hprefix tailTrace_1530338
  have hstable : (prefixWord ++ tailWord_1530338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530338).length < 2 ^ (prefixWord ++ tailWord_1530338).sum := by decide
  have hdescent : baseEnd_1530338 < baseStart_1530338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530360 : List Nat := [2, 1, 2, 1, 1, 4, 2, 4, 4]
def baseStart_1530360 : Nat := 118140960795 + 1530360 * 2 ^ 59
def prefixEnd_1530360 : Nat := 4983230072969 + 3 ^ 40 * 1530360 * 2
def baseEnd_1530360 : Nat := 349249001962105641405337

theorem tailTrace_1530360 : CollatzResearch.WordTrace tailWord_1530360 prefixEnd_1530360 349249001962105641405337 := by
  unfold tailWord_1530360
  simp only [CollatzResearch.WordTrace]
  refine ⟨27908407367887279762402267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37211209823849706349869689 27908407367887279762402267)
  ·
    refine ⟨41862611051830919643603401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27908407367887279762402267 41862611051830919643603401)
    ·
      refine ⟨31396958288873189732702551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41862611051830919643603401 31396958288873189732702551)
      ·
        refine ⟨47095437433309784599053827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31396958288873189732702551 47095437433309784599053827)
        ·
          refine ⟨70643156149964676898580741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47095437433309784599053827 70643156149964676898580741)
          ·
            refine ⟨13245591778118376918483889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70643156149964676898580741 13245591778118376918483889)
            ·
              refine ⟨9934193833588782688862917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13245591778118376918483889 9934193833588782688862917)
              ·
                refine ⟨1862661343797896754161797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9934193833588782688862917 1862661343797896754161797)
                ·
                  refine ⟨349249001962105641405337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1862661343797896754161797 349249001962105641405337)
                  ·
                    rfl

theorem cell21_1530360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 4].length) (baseStart_1530360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1530360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1530360 prefixEnd_1530360 := by exact prefixLift 1530360
  have htrace : WordTrace (prefixWord ++ tailWord_1530360) baseStart_1530360 baseEnd_1530360 := by
    simpa [prefixWord, tailWord_1530360, baseEnd_1530360] using wordTrace_append hprefix tailTrace_1530360
  have hstable : (prefixWord ++ tailWord_1530360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530360).length < 2 ^ (prefixWord ++ tailWord_1530360).sum := by decide
  have hdescent : baseEnd_1530360 < baseStart_1530360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530414 : List Nat := [4, 1, 3, 1, 4, 1, 2, 2, 3]
def baseStart_1530414 : Nat := 118140960795 + 1530414 * 2 ^ 59
def prefixEnd_1530414 : Nat := 4983230072969 + 3 ^ 40 * 1530414 * 2
def baseEnd_1530414 : Nat := 349261325497813547505227

theorem tailTrace_1530414 : CollatzResearch.WordTrace tailWord_1530414 prefixEnd_1530414 349261325497813547505227 := by
  unfold tailWord_1530414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6977348034697365843408787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37212522851719284498180197 6977348034697365843408787)
  ·
    refine ⟨10466022052046048765113181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6977348034697365843408787 10466022052046048765113181)
    ·
      refine ⟨3924758269517268286917443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10466022052046048765113181 3924758269517268286917443)
      ·
        refine ⟨5887137404275902430376165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3924758269517268286917443 5887137404275902430376165)
        ·
          refine ⟨1103838263301731705695531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5887137404275902430376165 1103838263301731705695531)
          ·
            refine ⟨1655757394952597558543297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1103838263301731705695531 1655757394952597558543297)
            ·
              refine ⟨1241818046214448168907473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1655757394952597558543297 1241818046214448168907473)
              ·
                refine ⟨931363534660836126680605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1241818046214448168907473 931363534660836126680605)
                ·
                  refine ⟨349261325497813547505227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 931363534660836126680605 349261325497813547505227)
                  ·
                    rfl

theorem cell21_1530414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_1530414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1530414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1530414 prefixEnd_1530414 := by exact prefixLift 1530414
  have htrace : WordTrace (prefixWord ++ tailWord_1530414) baseStart_1530414 baseEnd_1530414 := by
    simpa [prefixWord, tailWord_1530414, baseEnd_1530414] using wordTrace_append hprefix tailTrace_1530414
  have hstable : (prefixWord ++ tailWord_1530414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530414).length < 2 ^ (prefixWord ++ tailWord_1530414).sum := by decide
  have hdescent : baseEnd_1530414 < baseStart_1530414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530591 : List Nat := [1, 1, 2, 3, 2, 3, 4, 2, 3]
def baseStart_1530591 : Nat := 118140960795 + 1530591 * 2 ^ 59
def prefixEnd_1530591 : Nat := 4983230072969 + 3 ^ 40 * 1530591 * 2
def baseEnd_1530591 : Nat := 349301719309300573054865

theorem tailTrace_1530591 : CollatzResearch.WordTrace tailWord_1530591 prefixEnd_1530591 349301719309300573054865 := by
  unfold tailWord_1530591
  simp only [CollatzResearch.WordTrace]
  refine ⟨55825239997937685976463627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37216826665291790650975751 55825239997937685976463627)
  ·
    refine ⟨83737859996906528964695441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55825239997937685976463627 83737859996906528964695441)
    ·
      refine ⟨62803394997679896723521581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83737859996906528964695441 62803394997679896723521581)
      ·
        refine ⟨23551273124129961271320593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62803394997679896723521581 23551273124129961271320593)
        ·
          refine ⟨17663454843097470953490445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23551273124129961271320593 17663454843097470953490445)
          ·
            refine ⟨6623795566161551607558917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17663454843097470953490445 6623795566161551607558917)
            ·
              refine ⟨1241961668655290926417297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6623795566161551607558917 1241961668655290926417297)
              ·
                refine ⟨931471251491468194812973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1241961668655290926417297 931471251491468194812973)
                ·
                  refine ⟨349301719309300573054865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 931471251491468194812973 349301719309300573054865)
                  ·
                    rfl

theorem cell21_1530591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2, 3].length) (baseStart_1530591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1530591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1530591 prefixEnd_1530591 := by exact prefixLift 1530591
  have htrace : WordTrace (prefixWord ++ tailWord_1530591) baseStart_1530591 baseEnd_1530591 := by
    simpa [prefixWord, tailWord_1530591, baseEnd_1530591] using wordTrace_append hprefix tailTrace_1530591
  have hstable : (prefixWord ++ tailWord_1530591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530591).length < 2 ^ (prefixWord ++ tailWord_1530591).sum := by decide
  have hdescent : baseEnd_1530591 < baseStart_1530591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530650 : List Nat := [3, 1, 1, 3, 2, 1, 1, 6, 3]
def baseStart_1530650 : Nat := 118140960795 + 1530650 * 2 ^ 59
def prefixEnd_1530650 : Nat := 4983230072969 + 3 ^ 40 * 1530650 * 2
def baseEnd_1530650 : Nat := 349315183913129581571411

theorem tailTrace_1530650 : CollatzResearch.WordTrace tailWord_1530650 prefixEnd_1530650 349315183913129581571411 := by
  unfold tailWord_1530650
  simp only [CollatzResearch.WordTrace]
  refine ⟨13956847976180984763215351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37218261269815959368574269 13956847976180984763215351)
  ·
    refine ⟨20935271964271477144823027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13956847976180984763215351 20935271964271477144823027)
    ·
      refine ⟨31402907946407215717234541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20935271964271477144823027 31402907946407215717234541)
      ·
        refine ⟨11776090479902705893962953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31402907946407215717234541 11776090479902705893962953)
        ·
          refine ⟨8832067859927029420472215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11776090479902705893962953 8832067859927029420472215)
          ·
            refine ⟨13248101789890544130708323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8832067859927029420472215 13248101789890544130708323)
            ·
              refine ⟨19872152684835816196062485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13248101789890544130708323 19872152684835816196062485)
              ·
                refine ⟨931507157101678884190429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19872152684835816196062485 931507157101678884190429)
                ·
                  refine ⟨349315183913129581571411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 931507157101678884190429 349315183913129581571411)
                  ·
                    rfl

theorem cell21_1530650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6, 3].length) (baseStart_1530650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1530650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1530650 prefixEnd_1530650 := by exact prefixLift 1530650
  have htrace : WordTrace (prefixWord ++ tailWord_1530650) baseStart_1530650 baseEnd_1530650 := by
    simpa [prefixWord, tailWord_1530650, baseEnd_1530650] using wordTrace_append hprefix tailTrace_1530650
  have hstable : (prefixWord ++ tailWord_1530650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530650).length < 2 ^ (prefixWord ++ tailWord_1530650).sum := by decide
  have hdescent : baseEnd_1530650 < baseStart_1530650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530701 : List Nat := [1, 6, 1, 2, 2, 1, 3, 2, 3]
def baseStart_1530701 : Nat := 118140960795 + 1530701 * 2 ^ 59
def prefixEnd_1530701 : Nat := 4983230072969 + 3 ^ 40 * 1530701 * 2
def baseEnd_1530701 : Nat := 349326822807964826221307

theorem tailTrace_1530701 : CollatzResearch.WordTrace tailWord_1530701 prefixEnd_1530701 349326822807964826221307 := by
  unfold tailWord_1530701
  simp only [CollatzResearch.WordTrace]
  refine ⟨55829252027539174762967957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37219501351692783175311971 55829252027539174762967957)
  ·
    refine ⟨2616996188790898817014123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55829252027539174762967957 2616996188790898817014123)
    ·
      refine ⟨3925494283186348225521185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2616996188790898817014123 3925494283186348225521185)
      ·
        refine ⟨2944120712389761169140889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3925494283186348225521185 2944120712389761169140889)
        ·
          refine ⟨2208090534292320876855667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2944120712389761169140889 2208090534292320876855667)
          ·
            refine ⟨3312135801438481315283501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2208090534292320876855667 3312135801438481315283501)
            ·
              refine ⟨1242050925539430493231313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3312135801438481315283501 1242050925539430493231313)
              ·
                refine ⟨931538194154572869923485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1242050925539430493231313 931538194154572869923485)
                ·
                  refine ⟨349326822807964826221307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 931538194154572869923485 349326822807964826221307)
                  ·
                    rfl

theorem cell21_1530701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_1530701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1530701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1530701 prefixEnd_1530701 := by exact prefixLift 1530701
  have htrace : WordTrace (prefixWord ++ tailWord_1530701) baseStart_1530701 baseEnd_1530701 := by
    simpa [prefixWord, tailWord_1530701, baseEnd_1530701] using wordTrace_append hprefix tailTrace_1530701
  have hstable : (prefixWord ++ tailWord_1530701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530701).length < 2 ^ (prefixWord ++ tailWord_1530701).sum := by decide
  have hdescent : baseEnd_1530701 < baseStart_1530701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530760 : List Nat := [2, 1, 3, 3, 2, 3, 2, 2, 3]
def baseStart_1530760 : Nat := 118140960795 + 1530760 * 2 ^ 59
def prefixEnd_1530760 : Nat := 4983230072969 + 3 ^ 40 * 1530760 * 2
def baseEnd_1530760 : Nat := 349340287411793834737853

theorem tailTrace_1530760 : CollatzResearch.WordTrace tailWord_1530760 prefixEnd_1530760 349340287411793834737853 := by
  unfold tailWord_1530760
  simp only [CollatzResearch.WordTrace]
  refine ⟨27915701967162713919682867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37220935956216951892910489 27915701967162713919682867)
  ·
    refine ⟨41873552950744070879524301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27915701967162713919682867 41873552950744070879524301)
    ·
      refine ⟨15702582356529026579821613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41873552950744070879524301 15702582356529026579821613)
      ·
        refine ⟨5888468383698384967433105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15702582356529026579821613 5888468383698384967433105)
        ·
          refine ⟨4416351287773788725574829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5888468383698384967433105 4416351287773788725574829)
          ·
            refine ⟨1656131732915170772090561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4416351287773788725574829 1656131732915170772090561)
            ·
              refine ⟨1242098799686378079067921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1656131732915170772090561 1242098799686378079067921)
              ·
                refine ⟨931574099764783559300941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1242098799686378079067921 931574099764783559300941)
                ·
                  refine ⟨349340287411793834737853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 931574099764783559300941 349340287411793834737853)
                  ·
                    rfl

theorem cell21_1530760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2, 3].length) (baseStart_1530760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1530760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1530760 prefixEnd_1530760 := by exact prefixLift 1530760
  have htrace : WordTrace (prefixWord ++ tailWord_1530760) baseStart_1530760 baseEnd_1530760 := by
    simpa [prefixWord, tailWord_1530760, baseEnd_1530760] using wordTrace_append hprefix tailTrace_1530760
  have hstable : (prefixWord ++ tailWord_1530760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530760).length < 2 ^ (prefixWord ++ tailWord_1530760).sum := by decide
  have hdescent : baseEnd_1530760 < baseStart_1530760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530785 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 7]
def baseStart_1530785 : Nat := 118140960795 + 1530785 * 2 ^ 59
def prefixEnd_1530785 : Nat := 4983230072969 + 3 ^ 40 * 1530785 * 2
def baseEnd_1530785 : Nat := 349345992752399346821135

theorem tailTrace_1530785 : CollatzResearch.WordTrace tailWord_1530785 prefixEnd_1530785 349345992752399346821135 := by
  unfold tailWord_1530785
  simp only [CollatzResearch.WordTrace]
  refine ⟨55832315759234857109025809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37221543839489904739350539 55832315759234857109025809)
  ·
    refine ⟨41874236819426142831769357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55832315759234857109025809 41874236819426142831769357)
    ·
      refine ⟨15702838807284803561913509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41874236819426142831769357 15702838807284803561913509)
      ·
        refine ⟨2944282276365900667858783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15702838807284803561913509 2944282276365900667858783)
        ·
          refine ⟨4416423414548851001788175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2944282276365900667858783 4416423414548851001788175)
          ·
            refine ⟨6624635121823276502682263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4416423414548851001788175 6624635121823276502682263)
            ·
              refine ⟨9936952682734914754023395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6624635121823276502682263 9936952682734914754023395)
              ·
                refine ⟨14905429024102372131035093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9936952682734914754023395 14905429024102372131035093)
                ·
                  refine ⟨349345992752399346821135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14905429024102372131035093 349345992752399346821135)
                  ·
                    rfl

theorem cell21_1530785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 7].length) (baseStart_1530785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1530785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1530785 prefixEnd_1530785 := by exact prefixLift 1530785
  have htrace : WordTrace (prefixWord ++ tailWord_1530785) baseStart_1530785 baseEnd_1530785 := by
    simpa [prefixWord, tailWord_1530785, baseEnd_1530785] using wordTrace_append hprefix tailTrace_1530785
  have hstable : (prefixWord ++ tailWord_1530785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530785).length < 2 ^ (prefixWord ++ tailWord_1530785).sum := by decide
  have hdescent : baseEnd_1530785 < baseStart_1530785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530816 : List Nat := [2, 1, 1, 2, 3, 3, 3, 2, 4]
def baseStart_1530816 : Nat := 118140960795 + 1530816 * 2 ^ 59
def prefixEnd_1530816 : Nat := 4983230072969 + 3 ^ 40 * 1530816 * 2
def baseEnd_1530816 : Nat := 349353067374750181804405

theorem tailTrace_1530816 : CollatzResearch.WordTrace tailWord_1530816 prefixEnd_1530816 349353067374750181804405 := by
  unfold tailWord_1530816
  simp only [CollatzResearch.WordTrace]
  refine ⟨27916723211061274701702151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37222297614748366268936201 27916723211061274701702151)
  ·
    refine ⟨41875084816591912052553227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27916723211061274701702151 41875084816591912052553227)
    ·
      refine ⟨62812627224887868078829841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41875084816591912052553227 62812627224887868078829841)
      ·
        refine ⟨47109470418665901059122381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62812627224887868078829841 47109470418665901059122381)
        ·
          refine ⟨17666051406999712897170893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47109470418665901059122381 17666051406999712897170893)
          ·
            refine ⟨6624769277624892336439085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17666051406999712897170893 6624769277624892336439085)
            ·
              refine ⟨2484288479109334626164657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6624769277624892336439085 2484288479109334626164657)
              ·
                refine ⟨1863216359332000969623493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2484288479109334626164657 1863216359332000969623493)
                ·
                  refine ⟨349353067374750181804405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1863216359332000969623493 349353067374750181804405)
                  ·
                    rfl

theorem cell21_1530816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 4].length) (baseStart_1530816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1530816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1530816 prefixEnd_1530816 := by exact prefixLift 1530816
  have htrace : WordTrace (prefixWord ++ tailWord_1530816) baseStart_1530816 baseEnd_1530816 := by
    simpa [prefixWord, tailWord_1530816, baseEnd_1530816] using wordTrace_append hprefix tailTrace_1530816
  have hstable : (prefixWord ++ tailWord_1530816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530816).length < 2 ^ (prefixWord ++ tailWord_1530816).sum := by decide
  have hdescent : baseEnd_1530816 < baseStart_1530816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530853 : List Nat := [1, 3, 1, 6, 2, 1, 1, 3, 3]
def baseStart_1530853 : Nat := 118140960795 + 1530853 * 2 ^ 59
def prefixEnd_1530853 : Nat := 4983230072969 + 3 ^ 40 * 1530853 * 2
def baseEnd_1530853 : Nat := 349361511278846339687663

theorem tailTrace_1530853 : CollatzResearch.WordTrace tailWord_1530853 prefixEnd_1530853 349361511278846339687663 := by
  unfold tailWord_1530853
  simp only [CollatzResearch.WordTrace]
  refine ⟨55834795922988504722501213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37223197281992336481667475 55834795922988504722501213)
  ·
    refine ⟨20938048471120689270937955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55834795922988504722501213 20938048471120689270937955)
    ·
      refine ⟨31407072706681033906406933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20938048471120689270937955 31407072706681033906406933)
      ·
        refine ⟨1472206533125673464362825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31407072706681033906406933 1472206533125673464362825)
        ·
          refine ⟨1104154899844255098272119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1472206533125673464362825 1104154899844255098272119)
          ·
            refine ⟨1656232349766382647408179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1104154899844255098272119 1656232349766382647408179)
            ·
              refine ⟨2484348524649573971112269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1656232349766382647408179 2484348524649573971112269)
              ·
                refine ⟨931630696743590239167101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2484348524649573971112269 931630696743590239167101)
                ·
                  refine ⟨349361511278846339687663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 931630696743590239167101 349361511278846339687663)
                  ·
                    rfl

theorem cell21_1530853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3, 3].length) (baseStart_1530853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1530853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1530853 prefixEnd_1530853 := by exact prefixLift 1530853
  have htrace : WordTrace (prefixWord ++ tailWord_1530853) baseStart_1530853 baseEnd_1530853 := by
    simpa [prefixWord, tailWord_1530853, baseEnd_1530853] using wordTrace_append hprefix tailTrace_1530853
  have hstable : (prefixWord ++ tailWord_1530853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530853).length < 2 ^ (prefixWord ++ tailWord_1530853).sum := by decide
  have hdescent : baseEnd_1530853 < baseStart_1530853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530875 : List Nat := [1, 1, 1, 1, 1, 3, 3, 6, 4]
def baseStart_1530875 : Nat := 118140960795 + 1530875 * 2 ^ 59
def prefixEnd_1530875 : Nat := 4983230072969 + 3 ^ 40 * 1530875 * 2
def baseEnd_1530875 : Nat := 349366531978579190320951

theorem tailTrace_1530875 : CollatzResearch.WordTrace tailWord_1530875 prefixEnd_1530875 349366531978579190320951 := by
  unfold tailWord_1530875
  simp only [CollatzResearch.WordTrace]
  refine ⟨55835598328908802479802079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37223732219272534986534719 55835598328908802479802079)
  ·
    refine ⟨83753397493363203719703119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55835598328908802479802079 83753397493363203719703119)
    ·
      refine ⟨125630096240044805579554679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83753397493363203719703119 125630096240044805579554679)
      ·
        refine ⟨188445144360067208369332019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125630096240044805579554679 188445144360067208369332019)
        ·
          refine ⟨282667716540100812553998029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188445144360067208369332019 282667716540100812553998029)
          ·
            refine ⟨106000393702537804707749261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282667716540100812553998029 106000393702537804707749261)
            ·
              refine ⟨39750147638451676765405973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106000393702537804707749261 39750147638451676765405973)
              ·
                refine ⟨1863288170552422348378405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39750147638451676765405973 1863288170552422348378405)
                ·
                  refine ⟨349366531978579190320951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1863288170552422348378405 349366531978579190320951)
                  ·
                    rfl

theorem cell21_1530875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 4].length) (baseStart_1530875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1530875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1530875 prefixEnd_1530875 := by exact prefixLift 1530875
  have htrace : WordTrace (prefixWord ++ tailWord_1530875) baseStart_1530875 baseEnd_1530875 := by
    simpa [prefixWord, tailWord_1530875, baseEnd_1530875] using wordTrace_append hprefix tailTrace_1530875
  have hstable : (prefixWord ++ tailWord_1530875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530875).length < 2 ^ (prefixWord ++ tailWord_1530875).sum := by decide
  have hdescent : baseEnd_1530875 < baseStart_1530875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530892 : List Nat := [2, 2, 1, 2, 3, 3, 1, 3, 4]
def baseStart_1530892 : Nat := 118140960795 + 1530892 * 2 ^ 59
def prefixEnd_1530892 : Nat := 4983230072969 + 3 ^ 40 * 1530892 * 2
def baseEnd_1530892 : Nat := 349370411610190938537583

theorem tailTrace_1530892 : CollatzResearch.WordTrace tailWord_1530892 prefixEnd_1530892 349370411610190938537583 := by
  unfold tailWord_1530892
  simp only [CollatzResearch.WordTrace]
  refine ⟨27918109184923607191585465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37224145579898142922113953 27918109184923607191585465)
  ·
    refine ⟨20938581888692705393689099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27918109184923607191585465 20938581888692705393689099)
    ·
      refine ⟨31407872833039058090533649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20938581888692705393689099 31407872833039058090533649)
      ·
        refine ⟨23555904624779293567900237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31407872833039058090533649 23555904624779293567900237)
        ·
          refine ⟨8833464234292235087962589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23555904624779293567900237 8833464234292235087962589)
          ·
            refine ⟨3312549087859588157985971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8833464234292235087962589 3312549087859588157985971)
            ·
              refine ⟨4968823631789382236978957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3312549087859588157985971 4968823631789382236978957)
              ·
                refine ⟨1863308861921018338867109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4968823631789382236978957 1863308861921018338867109)
                ·
                  refine ⟨349370411610190938537583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1863308861921018338867109 349370411610190938537583)
                  ·
                    rfl

theorem cell21_1530892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_1530892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1530892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1530892 prefixEnd_1530892 := by exact prefixLift 1530892
  have htrace : WordTrace (prefixWord ++ tailWord_1530892) baseStart_1530892 baseEnd_1530892 := by
    simpa [prefixWord, tailWord_1530892, baseEnd_1530892] using wordTrace_append hprefix tailTrace_1530892
  have hstable : (prefixWord ++ tailWord_1530892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530892).length < 2 ^ (prefixWord ++ tailWord_1530892).sum := by decide
  have hdescent : baseEnd_1530892 < baseStart_1530892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531016 : List Nat := [2, 1, 3, 4, 2, 2, 2, 5]
def baseStart_1531016 : Nat := 118140960795 + 1531016 * 2 ^ 59
def prefixEnd_1531016 : Nat := 4983230072969 + 3 ^ 40 * 1531016 * 2
def baseEnd_1531016 : Nat := 116466236699864759490221

theorem tailTrace_1531016 : CollatzResearch.WordTrace tailWord_1531016 prefixEnd_1531016 116466236699864759490221 := by
  unfold tailWord_1531016
  simp only [CollatzResearch.WordTrace]
  refine ⟨27920370510698991780342451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37227160680931989040456601 27920370510698991780342451)
  ·
    refine ⟨41880555766048487670513677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27920370510698991780342451 41880555766048487670513677)
    ·
      refine ⟨15705208412268182876442629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41880555766048487670513677 15705208412268182876442629)
      ·
        refine ⟨2944726577300284289332993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15705208412268182876442629 2944726577300284289332993)
        ·
          refine ⟨2208544932975213216999745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2944726577300284289332993 2208544932975213216999745)
          ·
            refine ⟨1656408699731409912749809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2208544932975213216999745 1656408699731409912749809)
            ·
              refine ⟨1242306524798557434562357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1656408699731409912749809 1242306524798557434562357)
              ·
                refine ⟨116466236699864759490221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1242306524798557434562357 116466236699864759490221)
                ·
                  rfl

theorem cell21_1531016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 5].length) (baseStart_1531016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1531016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1531016 prefixEnd_1531016 := by exact prefixLift 1531016
  have htrace : WordTrace (prefixWord ++ tailWord_1531016) baseStart_1531016 baseEnd_1531016 := by
    simpa [prefixWord, tailWord_1531016, baseEnd_1531016] using wordTrace_append hprefix tailTrace_1531016
  have hstable : (prefixWord ++ tailWord_1531016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531016).length < 2 ^ (prefixWord ++ tailWord_1531016).sum := by decide
  have hdescent : baseEnd_1531016 < baseStart_1531016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531058 : List Nat := [3, 2, 1, 1, 1, 5, 2, 6]
def baseStart_1531058 : Nat := 118140960795 + 1531058 * 2 ^ 59
def prefixEnd_1531058 : Nat := 4983230072969 + 3 ^ 40 * 1531058 * 2
def baseEnd_1531058 : Nat := 116469431690603846256859

theorem tailTrace_1531058 : CollatzResearch.WordTrace tailWord_1531058 prefixEnd_1531058 116469431690603846256859 := by
  unfold tailWord_1531058
  simp only [CollatzResearch.WordTrace]
  refine ⟨13960568221811456183428457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37228181924830549822475885 13960568221811456183428457)
  ·
    refine ⟨10470426166358592137571343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13960568221811456183428457 10470426166358592137571343)
    ·
      refine ⟨15705639249537888206357015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10470426166358592137571343 15705639249537888206357015)
      ·
        refine ⟨23558458874306832309535523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15705639249537888206357015 23558458874306832309535523)
        ·
          refine ⟨35337688311460248464303285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23558458874306832309535523 35337688311460248464303285)
          ·
            refine ⟨3312908279199398293528433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35337688311460248464303285 3312908279199398293528433)
            ·
              refine ⟨2484681209399548720146325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3312908279199398293528433 2484681209399548720146325)
              ·
                refine ⟨116469431690603846256859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2484681209399548720146325 116469431690603846256859)
                ·
                  rfl

theorem cell21_1531058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 6].length) (baseStart_1531058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1531058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1531058 prefixEnd_1531058 := by exact prefixLift 1531058
  have htrace : WordTrace (prefixWord ++ tailWord_1531058) baseStart_1531058 baseEnd_1531058 := by
    simpa [prefixWord, tailWord_1531058, baseEnd_1531058] using wordTrace_append hprefix tailTrace_1531058
  have hstable : (prefixWord ++ tailWord_1531058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531058).length < 2 ^ (prefixWord ++ tailWord_1531058).sum := by decide
  have hdescent : baseEnd_1531058 < baseStart_1531058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531089 : List Nat := [1, 2, 2, 1, 2, 2, 1, 7, 3]
def baseStart_1531089 : Nat := 118140960795 + 1531089 * 2 ^ 59
def prefixEnd_1531089 : Nat := 4983230072969 + 3 ^ 40 * 1531089 * 2
def baseEnd_1531089 : Nat := 349415369694162373753847

theorem tailTrace_1531089 : CollatzResearch.WordTrace tailWord_1531089 prefixEnd_1531089 349415369694162373753847 := by
  unfold tailWord_1531089
  simp only [CollatzResearch.WordTrace]
  refine ⟨55843403550133517028092321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37228935700089011352061547 55843403550133517028092321)
  ·
    refine ⟨41882552662600137771069241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55843403550133517028092321 41882552662600137771069241)
    ·
      refine ⟨31411914496950103328301931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41882552662600137771069241 31411914496950103328301931)
      ·
        refine ⟨47117871745425154992452897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31411914496950103328301931 47117871745425154992452897)
        ·
          refine ⟨35338403809068866244339673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47117871745425154992452897 35338403809068866244339673)
          ·
            refine ⟨26503802856801649683254755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35338403809068866244339673 26503802856801649683254755)
            ·
              refine ⟨39755704285202474524882133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26503802856801649683254755 39755704285202474524882133)
              ·
                refine ⟨931774319184432996676925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 39755704285202474524882133 931774319184432996676925)
                ·
                  refine ⟨349415369694162373753847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 931774319184432996676925 349415369694162373753847)
                  ·
                    rfl

theorem cell21_1531089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7, 3].length) (baseStart_1531089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1531089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1531089 prefixEnd_1531089 := by exact prefixLift 1531089
  have htrace : WordTrace (prefixWord ++ tailWord_1531089) baseStart_1531089 baseEnd_1531089 := by
    simpa [prefixWord, tailWord_1531089, baseEnd_1531089] using wordTrace_append hprefix tailTrace_1531089
  have hstable : (prefixWord ++ tailWord_1531089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531089).length < 2 ^ (prefixWord ++ tailWord_1531089).sum := by decide
  have hdescent : baseEnd_1531089 < baseStart_1531089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531103 : List Nat := [1, 1, 2, 3, 2, 1, 3, 4, 4]
def baseStart_1531103 : Nat := 118140960795 + 1531103 * 2 ^ 59
def prefixEnd_1531103 : Nat := 4983230072969 + 3 ^ 40 * 1531103 * 2
def baseEnd_1531103 : Nat := 349418564684901460520485

theorem tailTrace_1531103 : CollatzResearch.WordTrace tailWord_1531103 prefixEnd_1531103 349418564684901460520485 := by
  unfold tailWord_1531103
  simp only [CollatzResearch.WordTrace]
  refine ⟨55843914172082797419101963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37229276114721864946067975 55843914172082797419101963)
  ·
    refine ⟨83765871258124196128652945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55843914172082797419101963 83765871258124196128652945)
    ·
      refine ⟨62824403443593147096489709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83765871258124196128652945 62824403443593147096489709)
      ·
        refine ⟨23559151291347430161183641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62824403443593147096489709 23559151291347430161183641)
        ·
          refine ⟨17669363468510572620887731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23559151291347430161183641 17669363468510572620887731)
          ·
            refine ⟨26504045202765858931331597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17669363468510572620887731 26504045202765858931331597)
            ·
              refine ⟨9939016951037197099249349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26504045202765858931331597 9939016951037197099249349)
              ·
                refine ⟨1863565678319474456109253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9939016951037197099249349 1863565678319474456109253)
                ·
                  refine ⟨349418564684901460520485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1863565678319474456109253 349418564684901460520485)
                  ·
                    rfl

theorem cell21_1531103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 4].length) (baseStart_1531103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1531103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1531103 prefixEnd_1531103 := by exact prefixLift 1531103
  have htrace : WordTrace (prefixWord ++ tailWord_1531103) baseStart_1531103 baseEnd_1531103 := by
    simpa [prefixWord, tailWord_1531103, baseEnd_1531103] using wordTrace_append hprefix tailTrace_1531103
  have hstable : (prefixWord ++ tailWord_1531103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531103).length < 2 ^ (prefixWord ++ tailWord_1531103).sum := by decide
  have hdescent : baseEnd_1531103 < baseStart_1531103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531165 : List Nat := [1, 4, 2, 3, 1, 1, 1, 3, 5]
def baseStart_1531165 : Nat := 118140960795 + 1531165 * 2 ^ 59
def prefixEnd_1531165 : Nat := 4983230072969 + 3 ^ 40 * 1531165 * 2
def baseEnd_1531165 : Nat := 349432713929603130487025

theorem tailTrace_1531165 : CollatzResearch.WordTrace tailWord_1531165 prefixEnd_1531165 349432713929603130487025 := by
  unfold tailWord_1531165
  simp only [CollatzResearch.WordTrace]
  refine ⟨55846175497858182007858949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37230783665238788005239299 55846175497858182007858949)
  ·
    refine ⟨10471157905848409126473553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55846175497858182007858949 10471157905848409126473553)
    ·
      refine ⟨7853368429386306844855165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10471157905848409126473553 7853368429386306844855165)
      ·
        refine ⟨2945013161019865066820687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7853368429386306844855165 2945013161019865066820687)
        ·
          refine ⟨4417519741529797600231031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2945013161019865066820687 4417519741529797600231031)
          ·
            refine ⟨6626279612294696400346547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4417519741529797600231031 6626279612294696400346547)
            ·
              refine ⟨9939419418442044600519821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6626279612294696400346547 9939419418442044600519821)
              ·
                refine ⟨3727282281915766725194933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9939419418442044600519821 3727282281915766725194933)
                ·
                  refine ⟨349432713929603130487025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3727282281915766725194933 349432713929603130487025)
                  ·
                    rfl

theorem cell21_1531165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_1531165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1531165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1531165 prefixEnd_1531165 := by exact prefixLift 1531165
  have htrace : WordTrace (prefixWord ++ tailWord_1531165) baseStart_1531165 baseEnd_1531165 := by
    simpa [prefixWord, tailWord_1531165, baseEnd_1531165] using wordTrace_append hprefix tailTrace_1531165
  have hstable : (prefixWord ++ tailWord_1531165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531165).length < 2 ^ (prefixWord ++ tailWord_1531165).sum := by decide
  have hdescent : baseEnd_1531165 < baseStart_1531165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531272 : List Nat := [2, 1, 3, 3, 1, 3, 2, 2, 4]
def baseStart_1531272 : Nat := 118140960795 + 1531272 * 2 ^ 59
def prefixEnd_1531272 : Nat := 4983230072969 + 3 ^ 40 * 1531272 * 2
def baseEnd_1531272 : Nat := 349457132787394722203473

theorem tailTrace_1531272 : CollatzResearch.WordTrace tailWord_1531272 prefixEnd_1531272 349457132787394722203473 := by
  unfold tailWord_1531272
  simp only [CollatzResearch.WordTrace]
  refine ⟨27925039054235269641002035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37233385405647026188002713 27925039054235269641002035)
  ·
    refine ⟨41887558581352904461503053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27925039054235269641002035 41887558581352904461503053)
    ·
      refine ⟨15707834468007339173063645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41887558581352904461503053 15707834468007339173063645)
      ·
        refine ⟨5890437925502752189898867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15707834468007339173063645 5890437925502752189898867)
        ·
          refine ⟨8835656888254128284848301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5890437925502752189898867 8835656888254128284848301)
          ·
            refine ⟨3313371333095298106818113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8835656888254128284848301 3313371333095298106818113)
            ·
              refine ⟨2485028499821473580113585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3313371333095298106818113 2485028499821473580113585)
              ·
                refine ⟨1863771374866105185085189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2485028499821473580113585 1863771374866105185085189)
                ·
                  refine ⟨349457132787394722203473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1863771374866105185085189 349457132787394722203473)
                  ·
                    rfl

theorem cell21_1531272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 4].length) (baseStart_1531272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1531272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1531272 prefixEnd_1531272 := by exact prefixLift 1531272
  have htrace : WordTrace (prefixWord ++ tailWord_1531272) baseStart_1531272 baseEnd_1531272 := by
    simpa [prefixWord, tailWord_1531272, baseEnd_1531272] using wordTrace_append hprefix tailTrace_1531272
  have hstable : (prefixWord ++ tailWord_1531272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531272).length < 2 ^ (prefixWord ++ tailWord_1531272).sum := by decide
  have hdescent : baseEnd_1531272 < baseStart_1531272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531283 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 11]
def baseStart_1531283 : Nat := 118140960795 + 1531283 * 2 ^ 59
def prefixEnd_1531283 : Nat := 4983230072969 + 3 ^ 40 * 1531283 * 2
def baseEnd_1531283 : Nat := 349459643137261147520117

theorem tailTrace_1531283 : CollatzResearch.WordTrace tailWord_1531283 prefixEnd_1531283 349459643137261147520117 := by
  unfold tailWord_1531283
  simp only [CollatzResearch.WordTrace]
  refine ⟨55850479311430688160654503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37233652874287125440436335 55850479311430688160654503)
  ·
    refine ⟨83775718967146032240981755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55850479311430688160654503 83775718967146032240981755)
    ·
      refine ⟨125663578450719048361472633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83775718967146032240981755 125663578450719048361472633)
      ·
        refine ⟨94247683838039286271104475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125663578450719048361472633 94247683838039286271104475)
        ·
          refine ⟨141371525757058929406656713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94247683838039286271104475 141371525757058929406656713)
          ·
            refine ⟨106028644317794197054992535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141371525757058929406656713 106028644317794197054992535)
            ·
              refine ⟨159042966476691295582488803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106028644317794197054992535 159042966476691295582488803)
              ·
                refine ⟨238564449715036943373733205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159042966476691295582488803 238564449715036943373733205)
                ·
                  refine ⟨349459643137261147520117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 238564449715036943373733205 349459643137261147520117)
                  ·
                    rfl

theorem cell21_1531283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 11].length) (baseStart_1531283 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1531283 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1531283 prefixEnd_1531283 := by exact prefixLift 1531283
  have htrace : WordTrace (prefixWord ++ tailWord_1531283) baseStart_1531283 baseEnd_1531283 := by
    simpa [prefixWord, tailWord_1531283, baseEnd_1531283] using wordTrace_append hprefix tailTrace_1531283
  have hstable : (prefixWord ++ tailWord_1531283).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531283).length < 2 ^ (prefixWord ++ tailWord_1531283).sum := by decide
  have hdescent : baseEnd_1531283 < baseStart_1531283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531331 : List Nat := [1, 1, 1, 3, 1, 1, 7, 2, 4]
def baseStart_1531331 : Nat := 118140960795 + 1531331 * 2 ^ 59
def prefixEnd_1531331 : Nat := 4983230072969 + 3 ^ 40 * 1531331 * 2
def baseEnd_1531331 : Nat := 349470597391223730720019

theorem tailTrace_1531331 : CollatzResearch.WordTrace tailWord_1531331 prefixEnd_1531331 349470597391223730720019 := by
  unfold tailWord_1531331
  simp only [CollatzResearch.WordTrace]
  refine ⟨55852230015256792358401847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37234820010171194905601231 55852230015256792358401847)
  ·
    refine ⟨83778345022885188537602771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55852230015256792358401847 83778345022885188537602771)
    ·
      refine ⟨125667517534327782806404157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83778345022885188537602771 125667517534327782806404157)
      ·
        refine ⟨47125319075372918552401559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125667517534327782806404157 47125319075372918552401559)
        ·
          refine ⟨70687978613059377828602339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47125319075372918552401559 70687978613059377828602339)
          ·
            refine ⟨106031967919589066742903509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70687978613059377828602339 106031967919589066742903509)
            ·
              refine ⟨2485124248115368751786801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 106031967919589066742903509 2485124248115368751786801)
              ·
                refine ⟨1863843186086526563840101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2485124248115368751786801 1863843186086526563840101)
                ·
                  refine ⟨349470597391223730720019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1863843186086526563840101 349470597391223730720019)
                  ·
                    rfl

theorem cell21_1531331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 4].length) (baseStart_1531331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1531331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1531331 prefixEnd_1531331 := by exact prefixLift 1531331
  have htrace : WordTrace (prefixWord ++ tailWord_1531331) baseStart_1531331 baseEnd_1531331 := by
    simpa [prefixWord, tailWord_1531331, baseEnd_1531331] using wordTrace_append hprefix tailTrace_1531331
  have hstable : (prefixWord ++ tailWord_1531331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531331).length < 2 ^ (prefixWord ++ tailWord_1531331).sum := by decide
  have hdescent : baseEnd_1531331 < baseStart_1531331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531421 : List Nat := [1, 4, 2, 2, 1, 1, 1, 9]
def baseStart_1531421 : Nat := 118140960795 + 1531421 * 2 ^ 59
def prefixEnd_1531421 : Nat := 4983230072969 + 3 ^ 40 * 1531421 * 2
def baseEnd_1531421 : Nat := 116497045539134524739945

theorem tailTrace_1531421 : CollatzResearch.WordTrace tailWord_1531421 prefixEnd_1531421 116497045539134524739945 := by
  unfold tailWord_1531421
  simp only [CollatzResearch.WordTrace]
  refine ⟨55855512584930737729178117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37237008389953825152785411 55855512584930737729178117)
  ·
    refine ⟨10472908609674513324220897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55855512584930737729178117 10472908609674513324220897)
    ·
      refine ⟨7854681457255884993165673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10472908609674513324220897 7854681457255884993165673)
      ·
        refine ⟨5891011092941913744874255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7854681457255884993165673 5891011092941913744874255)
        ·
          refine ⟨8836516639412870617311383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5891011092941913744874255 8836516639412870617311383)
          ·
            refine ⟨13254774959119305925967075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8836516639412870617311383 13254774959119305925967075)
            ·
              refine ⟨19882162438678958888950613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13254774959119305925967075 19882162438678958888950613)
              ·
                refine ⟨116497045539134524739945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19882162438678958888950613 116497045539134524739945)
                ·
                  rfl

theorem cell21_1531421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 9].length) (baseStart_1531421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1531421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1531421 prefixEnd_1531421 := by exact prefixLift 1531421
  have htrace : WordTrace (prefixWord ++ tailWord_1531421) baseStart_1531421 baseEnd_1531421 := by
    simpa [prefixWord, tailWord_1531421, baseEnd_1531421] using wordTrace_append hprefix tailTrace_1531421
  have hstable : (prefixWord ++ tailWord_1531421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531421).length < 2 ^ (prefixWord ++ tailWord_1531421).sum := by decide
  have hdescent : baseEnd_1531421 < baseStart_1531421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531613 : List Nat := [1, 4, 3, 3, 2, 1, 2, 2, 3]
def baseStart_1531613 : Nat := 118140960795 + 1531613 * 2 ^ 59
def prefixEnd_1531613 : Nat := 4983230072969 + 3 ^ 40 * 1531613 * 2
def baseEnd_1531613 : Nat := 349534953633253907019443

theorem tailTrace_1531613 : CollatzResearch.WordTrace tailWord_1531613 prefixEnd_1531613 349534953633253907019443 := by
  unfold tailWord_1531613
  simp only [CollatzResearch.WordTrace]
  refine ⟨55862515400235154520167493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37241676933490103013444995 55862515400235154520167493)
  ·
    refine ⟨10474221637544091472531405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55862515400235154520167493 10474221637544091472531405)
    ·
      refine ⟨3927833114079034302199277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10474221637544091472531405 3927833114079034302199277)
      ·
        refine ⟨1472937417779637863324729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3927833114079034302199277 1472937417779637863324729)
        ·
          refine ⟨1104703063334728397493547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1472937417779637863324729 1104703063334728397493547)
          ·
            refine ⟨1657054595002092596240321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1104703063334728397493547 1657054595002092596240321)
            ·
              refine ⟨1242790946251569447180241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1657054595002092596240321 1242790946251569447180241)
              ·
                refine ⟨932093209688677085385181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1242790946251569447180241 932093209688677085385181)
                ·
                  refine ⟨349534953633253907019443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 932093209688677085385181 349534953633253907019443)
                  ·
                    rfl

theorem cell21_1531613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_1531613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1531613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1531613 prefixEnd_1531613 := by exact prefixLift 1531613
  have htrace : WordTrace (prefixWord ++ tailWord_1531613) baseStart_1531613 baseEnd_1531613 := by
    simpa [prefixWord, tailWord_1531613, baseEnd_1531613] using wordTrace_append hprefix tailTrace_1531613
  have hstable : (prefixWord ++ tailWord_1531613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531613).length < 2 ^ (prefixWord ++ tailWord_1531613).sum := by decide
  have hdescent : baseEnd_1531613 < baseStart_1531613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531621 : List Nat := [1, 3, 1, 4, 1, 1, 3, 4, 3]
def baseStart_1531621 : Nat := 118140960795 + 1531621 * 2 ^ 59
def prefixEnd_1531621 : Nat := 4983230072969 + 3 ^ 40 * 1531621 * 2
def baseEnd_1531621 : Nat := 349536779342247670886093

theorem tailTrace_1531621 : CollatzResearch.WordTrace tailWord_1531621 prefixEnd_1531621 349536779342247670886093 := by
  unfold tailWord_1531621
  simp only [CollatzResearch.WordTrace]
  refine ⟨55862807184206171886458717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37241871456137447924305811 55862807184206171886458717)
  ·
    refine ⟨20948552694077314457422019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55862807184206171886458717 20948552694077314457422019)
    ·
      refine ⟨31422829041115971686133029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20948552694077314457422019 31422829041115971686133029)
      ·
        refine ⟨5891780445209244691149943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31422829041115971686133029 5891780445209244691149943)
        ·
          refine ⟨8837670667813867036724915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5891780445209244691149943 8837670667813867036724915)
          ·
            refine ⟨13256506001720800555087373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8837670667813867036724915 13256506001720800555087373)
            ·
              refine ⟨4971189750645300208157765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13256506001720800555087373 4971189750645300208157765)
              ·
                refine ⟨932098078245993789029581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4971189750645300208157765 932098078245993789029581)
                ·
                  refine ⟨349536779342247670886093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 932098078245993789029581 349536779342247670886093)
                  ·
                    rfl

theorem cell21_1531621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4, 3].length) (baseStart_1531621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1531621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1531621 prefixEnd_1531621 := by exact prefixLift 1531621
  have htrace : WordTrace (prefixWord ++ tailWord_1531621) baseStart_1531621 baseEnd_1531621 := by
    simpa [prefixWord, tailWord_1531621, baseEnd_1531621] using wordTrace_append hprefix tailTrace_1531621
  have hstable : (prefixWord ++ tailWord_1531621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531621).length < 2 ^ (prefixWord ++ tailWord_1531621).sum := by decide
  have hdescent : baseEnd_1531621 < baseStart_1531621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531632 : List Nat := [2, 1, 1, 1, 3, 1, 2, 10]
def baseStart_1531632 : Nat := 118140960795 + 1531632 * 2 ^ 59
def prefixEnd_1531632 : Nat := 4983230072969 + 3 ^ 40 * 1531632 * 2
def baseEnd_1531632 : Nat := 116513096564038032067579

theorem tailTrace_1531632 : CollatzResearch.WordTrace tailWord_1531632 prefixEnd_1531632 116513096564038032067579 := by
  unfold tailWord_1531632
  simp only [CollatzResearch.WordTrace]
  refine ⟨27931604193583160382554575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37242138924777547176739433 27931604193583160382554575)
  ·
    refine ⟨41897406290374740573831863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27931604193583160382554575 41897406290374740573831863)
    ·
      refine ⟨62846109435562110860747795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41897406290374740573831863 62846109435562110860747795)
      ·
        refine ⟨94269164153343166291121693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62846109435562110860747795 94269164153343166291121693)
        ·
          refine ⟨35350936557503687359170635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94269164153343166291121693 35350936557503687359170635)
          ·
            refine ⟨53026404836255531038755953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35350936557503687359170635 53026404836255531038755953)
            ·
              refine ⟨39769803627191648279066965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53026404836255531038755953 39769803627191648279066965)
              ·
                refine ⟨116513096564038032067579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39769803627191648279066965 116513096564038032067579)
                ·
                  rfl

theorem cell21_1531632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 10].length) (baseStart_1531632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1531632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1531632 prefixEnd_1531632 := by exact prefixLift 1531632
  have htrace : WordTrace (prefixWord ++ tailWord_1531632) baseStart_1531632 baseEnd_1531632 := by
    simpa [prefixWord, tailWord_1531632, baseEnd_1531632] using wordTrace_append hprefix tailTrace_1531632
  have hstable : (prefixWord ++ tailWord_1531632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531632).length < 2 ^ (prefixWord ++ tailWord_1531632).sum := by decide
  have hdescent : baseEnd_1531632 < baseStart_1531632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531666 : List Nat := [3, 2, 4, 1, 1, 2, 8]
def baseStart_1531666 : Nat := 118140960795 + 1531666 * 2 ^ 59
def prefixEnd_1531666 : Nat := 4983230072969 + 3 ^ 40 * 1531666 * 2
def baseEnd_1531666 : Nat := 38838560995037510292889

theorem tailTrace_1531666 : CollatzResearch.WordTrace tailWord_1531666 prefixEnd_1531666 38838560995037510292889 := by
  unfold tailWord_1531666
  simp only [CollatzResearch.WordTrace]
  refine ⟨13966112117260786142961713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37242965646028763047897901 13966112117260786142961713)
  ·
    refine ⟨10474584087945589607221285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13966112117260786142961713 10474584087945589607221285)
    ·
      refine ⟨1963984516489798051353991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10474584087945589607221285 1963984516489798051353991)
      ·
        refine ⟨2945976774734697077030987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1963984516489798051353991 2945976774734697077030987)
        ·
          refine ⟨4418965162102045615546481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2945976774734697077030987 4418965162102045615546481)
          ·
            refine ⟨3314223871576534211659861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4418965162102045615546481 3314223871576534211659861)
            ·
              refine ⟨38838560995037510292889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3314223871576534211659861 38838560995037510292889)
              ·
                rfl

theorem cell21_1531666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 8].length) (baseStart_1531666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1531666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1531666 prefixEnd_1531666 := by exact prefixLift 1531666
  have htrace : WordTrace (prefixWord ++ tailWord_1531666) baseStart_1531666 baseEnd_1531666 := by
    simpa [prefixWord, tailWord_1531666, baseEnd_1531666] using wordTrace_append hprefix tailTrace_1531666
  have hstable : (prefixWord ++ tailWord_1531666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531666).length < 2 ^ (prefixWord ++ tailWord_1531666).sum := by decide
  have hdescent : baseEnd_1531666 < baseStart_1531666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531680 : List Nat := [2, 1, 1, 5, 1, 1, 4, 1, 5]
def baseStart_1531680 : Nat := 118140960795 + 1531680 * 2 ^ 59
def prefixEnd_1531680 : Nat := 4983230072969 + 3 ^ 40 * 1531680 * 2
def baseEnd_1531680 : Nat := 349550243946076679402639

theorem tailTrace_1531680 : CollatzResearch.WordTrace tailWord_1531680 prefixEnd_1531680 349550243946076679402639 := by
  unfold tailWord_1531680
  simp only [CollatzResearch.WordTrace]
  refine ⟨27932479545496212481428247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37243306060661616641904329 27932479545496212481428247)
  ·
    refine ⟨41898719318244318722142371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27932479545496212481428247 41898719318244318722142371)
    ·
      refine ⟨62848078977366478083213557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41898719318244318722142371 62848078977366478083213557)
      ·
        refine ⟨5892007404128107320301271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62848078977366478083213557 5892007404128107320301271)
        ·
          refine ⟨8838011106192160980451907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5892007404128107320301271 8838011106192160980451907)
          ·
            refine ⟨13257016659288241470677861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8838011106192160980451907 13257016659288241470677861)
            ·
              refine ⟨2485690623616545275752099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13257016659288241470677861 2485690623616545275752099)
              ·
                refine ⟨3728535935424817913628149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2485690623616545275752099 3728535935424817913628149)
                ·
                  refine ⟨349550243946076679402639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3728535935424817913628149 349550243946076679402639)
                  ·
                    rfl

theorem cell21_1531680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 5].length) (baseStart_1531680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1531680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1531680 prefixEnd_1531680 := by exact prefixLift 1531680
  have htrace : WordTrace (prefixWord ++ tailWord_1531680) baseStart_1531680 baseEnd_1531680 := by
    simpa [prefixWord, tailWord_1531680, baseEnd_1531680] using wordTrace_append hprefix tailTrace_1531680
  have hstable : (prefixWord ++ tailWord_1531680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531680).length < 2 ^ (prefixWord ++ tailWord_1531680).sum := by decide
  have hdescent : baseEnd_1531680 < baseStart_1531680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531784 : List Nat := [2, 1, 3, 3, 12]
def baseStart_1531784 : Nat := 118140960795 + 1531784 * 2 ^ 59
def prefixEnd_1531784 : Nat := 4983230072969 + 3 ^ 40 * 1531784 * 2
def baseEnd_1531784 : Nat := 4315728125469081600853

theorem tailTrace_1531784 : CollatzResearch.WordTrace tailWord_1531784 prefixEnd_1531784 4315728125469081600853 := by
  unfold tailWord_1531784
  simp only [CollatzResearch.WordTrace]
  refine ⟨27934376141307825362321203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37245834855077100483094937 27934376141307825362321203)
  ·
    refine ⟨41901564211961738043481805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27934376141307825362321203 41901564211961738043481805)
    ·
      refine ⟨15713086579485651766305677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41901564211961738043481805 15713086579485651766305677)
      ·
        refine ⟨5892407467307119412364629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15713086579485651766305677 5892407467307119412364629)
        ·
          refine ⟨4315728125469081600853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5892407467307119412364629 4315728125469081600853)
          ·
            rfl

theorem cell21_1531784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 12].length) (baseStart_1531784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1531784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1531784 prefixEnd_1531784 := by exact prefixLift 1531784
  have htrace : WordTrace (prefixWord ++ tailWord_1531784) baseStart_1531784 baseEnd_1531784 := by
    simpa [prefixWord, tailWord_1531784, baseEnd_1531784] using wordTrace_append hprefix tailTrace_1531784
  have hstable : (prefixWord ++ tailWord_1531784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531784).length < 2 ^ (prefixWord ++ tailWord_1531784).sum := by decide
  have hdescent : baseEnd_1531784 < baseStart_1531784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531863 : List Nat := [1, 1, 3, 2, 1, 1, 7, 1, 4]
def baseStart_1531863 : Nat := 118140960795 + 1531863 * 2 ^ 59
def prefixEnd_1531863 : Nat := 4983230072969 + 3 ^ 40 * 1531863 * 2
def baseEnd_1531863 : Nat := 349592007039309027852265

theorem tailTrace_1531863 : CollatzResearch.WordTrace tailWord_1531863 prefixEnd_1531863 349592007039309027852265 := by
  unfold tailWord_1531863
  simp only [CollatzResearch.WordTrace]
  refine ⟨55871633649329447216768243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37247755766219631477845495 55871633649329447216768243)
  ·
    refine ⟨83807450473994170825152365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55871633649329447216768243 83807450473994170825152365)
    ·
      refine ⟨31427793927747814059432137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83807450473994170825152365 31427793927747814059432137)
      ·
        refine ⟨23570845445810860544574103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31427793927747814059432137 23570845445810860544574103)
        ·
          refine ⟨35356268168716290816861155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23570845445810860544574103 35356268168716290816861155)
          ·
            refine ⟨53034402253074436225291733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35356268168716290816861155 53034402253074436225291733)
            ·
              refine ⟨1242993802806432099030275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 53034402253074436225291733 1242993802806432099030275)
              ·
                refine ⟨1864490704209648148545413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1242993802806432099030275 1864490704209648148545413)
                ·
                  refine ⟨349592007039309027852265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1864490704209648148545413 349592007039309027852265)
                  ·
                    rfl

theorem cell21_1531863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 4].length) (baseStart_1531863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1531863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1531863 prefixEnd_1531863 := by exact prefixLift 1531863
  have htrace : WordTrace (prefixWord ++ tailWord_1531863) baseStart_1531863 baseEnd_1531863 := by
    simpa [prefixWord, tailWord_1531863, baseEnd_1531863] using wordTrace_append hprefix tailTrace_1531863
  have hstable : (prefixWord ++ tailWord_1531863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531863).length < 2 ^ (prefixWord ++ tailWord_1531863).sum := by decide
  have hdescent : baseEnd_1531863 < baseStart_1531863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531894 : List Nat := [5, 1, 1, 1, 4, 2, 7]
def baseStart_1531894 : Nat := 118140960795 + 1531894 * 2 ^ 59
def prefixEnd_1531894 : Nat := 4983230072969 + 3 ^ 40 * 1531894 * 2
def baseEnd_1531894 : Nat := 38844342406851095870615

theorem tailTrace_1531894 : CollatzResearch.WordTrace tailWord_1531894 prefixEnd_1531894 38844342406851095870615 := by
  unfold tailWord_1531894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3492047769513571219446671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37248509541478093007431157 3492047769513571219446671)
  ·
    refine ⟨5238071654270356829170007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3492047769513571219446671 5238071654270356829170007)
    ·
      refine ⟨7857107481405535243755011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5238071654270356829170007 7857107481405535243755011)
      ·
        refine ⟨11785661222108302865632517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7857107481405535243755011 11785661222108302865632517)
        ·
          refine ⟨2209811479145306787306097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11785661222108302865632517 2209811479145306787306097)
          ·
            refine ⟨1657358609358980090479573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2209811479145306787306097 1657358609358980090479573)
            ·
              refine ⟨38844342406851095870615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1657358609358980090479573 38844342406851095870615)
              ·
                rfl

theorem cell21_1531894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 7].length) (baseStart_1531894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1531894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1531894 prefixEnd_1531894 := by exact prefixLift 1531894
  have htrace : WordTrace (prefixWord ++ tailWord_1531894) baseStart_1531894 baseEnd_1531894 := by
    simpa [prefixWord, tailWord_1531894, baseEnd_1531894] using wordTrace_append hprefix tailTrace_1531894
  have hstable : (prefixWord ++ tailWord_1531894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531894).length < 2 ^ (prefixWord ++ tailWord_1531894).sum := by decide
  have hdescent : baseEnd_1531894 < baseStart_1531894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532012 : List Nat := [2, 2, 1, 1, 3, 4, 8]
def baseStart_1532012 : Nat := 118140960795 + 1532012 * 2 ^ 59
def prefixEnd_1532012 : Nat := 4983230072969 + 3 ^ 40 * 1532012 * 2
def baseEnd_1532012 : Nat := 38847334541035319985403

theorem tailTrace_1532012 : CollatzResearch.WordTrace tailWord_1532012 prefixEnd_1532012 38847334541035319985403 := by
  unfold tailWord_1532012
  simp only [CollatzResearch.WordTrace]
  refine ⟨27938534062894822831971145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37251378750526430442628193 27938534062894822831971145)
  ·
    refine ⟨20953900547171117123978359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27938534062894822831971145 20953900547171117123978359)
    ·
      refine ⟨31430850820756675685967539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20953900547171117123978359 31430850820756675685967539)
      ·
        refine ⟨47146276231135013528951309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31430850820756675685967539 47146276231135013528951309)
        ·
          refine ⟨17679853586675630073356741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47146276231135013528951309 17679853586675630073356741)
          ·
            refine ⟨3314972547501680638754389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17679853586675630073356741 3314972547501680638754389)
            ·
              refine ⟨38847334541035319985403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3314972547501680638754389 38847334541035319985403)
              ·
                rfl

theorem cell21_1532012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 8].length) (baseStart_1532012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532012 prefixEnd_1532012 := by exact prefixLift 1532012
  have htrace : WordTrace (prefixWord ++ tailWord_1532012) baseStart_1532012 baseEnd_1532012 := by
    simpa [prefixWord, tailWord_1532012, baseEnd_1532012] using wordTrace_append hprefix tailTrace_1532012
  have hstable : (prefixWord ++ tailWord_1532012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532012).length < 2 ^ (prefixWord ++ tailWord_1532012).sum := by decide
  have hdescent : baseEnd_1532012 < baseStart_1532012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532015 : List Nat := [1, 1, 2, 1, 3, 6, 1, 2, 4]
def baseStart_1532015 : Nat := 118140960795 + 1532015 * 2 ^ 59
def prefixEnd_1532015 : Nat := 4983230072969 + 3 ^ 40 * 1532015 * 2
def baseEnd_1532015 : Nat := 349626695510190541318621

theorem tailTrace_1532015 : CollatzResearch.WordTrace tailWord_1532015 prefixEnd_1532015 349626695510190541318621 := by
  unfold tailWord_1532015
  simp only [CollatzResearch.WordTrace]
  refine ⟨55877177544778777176301499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37251451696519184784200999 55877177544778777176301499)
  ·
    refine ⟨83815766317168165764452249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55877177544778777176301499 83815766317168165764452249)
    ·
      refine ⟨62861824737876124323339187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83815766317168165764452249 62861824737876124323339187)
      ·
        refine ⟨94292737106814186485008781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62861824737876124323339187 94292737106814186485008781)
        ·
          refine ⟨35359776415055319931878293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94292737106814186485008781 35359776415055319931878293)
          ·
            refine ⟨1657489519455718121806795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35359776415055319931878293 1657489519455718121806795)
            ·
              refine ⟨2486234279183577182710193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1657489519455718121806795 2486234279183577182710193)
              ·
                refine ⟨1864675709387682887032645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2486234279183577182710193 1864675709387682887032645)
                ·
                  refine ⟨349626695510190541318621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1864675709387682887032645 349626695510190541318621)
                  ·
                    rfl

theorem cell21_1532015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 4].length) (baseStart_1532015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532015 prefixEnd_1532015 := by exact prefixLift 1532015
  have htrace : WordTrace (prefixWord ++ tailWord_1532015) baseStart_1532015 baseEnd_1532015 := by
    simpa [prefixWord, tailWord_1532015, baseEnd_1532015] using wordTrace_append hprefix tailTrace_1532015
  have hstable : (prefixWord ++ tailWord_1532015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532015).length < 2 ^ (prefixWord ++ tailWord_1532015).sum := by decide
  have hdescent : baseEnd_1532015 < baseStart_1532015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532052 : List Nat := [2, 4, 2, 3, 2, 1, 1, 3, 3]
def baseStart_1532052 : Nat := 118140960795 + 1532052 * 2 ^ 59
def prefixEnd_1532052 : Nat := 4983230072969 + 3 ^ 40 * 1532052 * 2
def baseEnd_1532052 : Nat := 349635139414286699201879

theorem tailTrace_1532052 : CollatzResearch.WordTrace tailWord_1532052 prefixEnd_1532052 349635139414286699201879 := by
  unfold tailWord_1532052
  simp only [CollatzResearch.WordTrace]
  refine ⟨27939263522822366247699205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37252351363763154996932273 27939263522822366247699205)
  ·
    refine ⟨5238611910529193671443601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27939263522822366247699205 5238611910529193671443601)
    ·
      refine ⟨3928958932896895253582701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5238611910529193671443601 3928958932896895253582701)
      ·
        refine ⟨1473359599836335720093513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3928958932896895253582701 1473359599836335720093513)
        ·
          refine ⟨1105019699877251790070135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1473359599836335720093513 1105019699877251790070135)
          ·
            refine ⟨1657529549815877685105203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1105019699877251790070135 1657529549815877685105203)
            ·
              refine ⟨2486294324723816527657805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1657529549815877685105203 2486294324723816527657805)
              ·
                refine ⟨932360371771431197871677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2486294324723816527657805 932360371771431197871677)
                ·
                  refine ⟨349635139414286699201879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 932360371771431197871677 349635139414286699201879)
                  ·
                    rfl

theorem cell21_1532052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_1532052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532052 prefixEnd_1532052 := by exact prefixLift 1532052
  have htrace : WordTrace (prefixWord ++ tailWord_1532052) baseStart_1532052 baseEnd_1532052 := by
    simpa [prefixWord, tailWord_1532052, baseEnd_1532052] using wordTrace_append hprefix tailTrace_1532052
  have hstable : (prefixWord ++ tailWord_1532052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532052).length < 2 ^ (prefixWord ++ tailWord_1532052).sum := by decide
  have hdescent : baseEnd_1532052 < baseStart_1532052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532077 : List Nat := [1, 5, 2, 1, 2, 3, 1, 1, 5]
def baseStart_1532077 : Nat := 118140960795 + 1532077 * 2 ^ 59
def prefixEnd_1532077 : Nat := 4983230072969 + 3 ^ 40 * 1532077 * 2
def baseEnd_1532077 : Nat := 349640844754892211285161

theorem tailTrace_1532077 : CollatzResearch.WordTrace tailWord_1532077 prefixEnd_1532077 349640844754892211285161 := by
  unfold tailWord_1532077
  simp only [CollatzResearch.WordTrace]
  refine ⟨55879438870554161765058485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37252959247036107843372323 55879438870554161765058485)
  ·
    refine ⟨5238697394114452665474233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55879438870554161765058485 5238697394114452665474233)
    ·
      refine ⟨3929023045585839499105675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5238697394114452665474233 3929023045585839499105675)
      ·
        refine ⟨5893534568378759248658513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3929023045585839499105675 5893534568378759248658513)
        ·
          refine ⟨4420150926284069436493885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5893534568378759248658513 4420150926284069436493885)
          ·
            refine ⟨1657556597356526038685207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4420150926284069436493885 1657556597356526038685207)
            ·
              refine ⟨2486334896034789058027811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1657556597356526038685207 2486334896034789058027811)
              ·
                refine ⟨3729502344052183587041717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2486334896034789058027811 3729502344052183587041717)
                ·
                  refine ⟨349640844754892211285161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3729502344052183587041717 349640844754892211285161)
                  ·
                    rfl

theorem cell21_1532077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_1532077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532077 prefixEnd_1532077 := by exact prefixLift 1532077
  have htrace : WordTrace (prefixWord ++ tailWord_1532077) baseStart_1532077 baseEnd_1532077 := by
    simpa [prefixWord, tailWord_1532077, baseEnd_1532077] using wordTrace_append hprefix tailTrace_1532077
  have hstable : (prefixWord ++ tailWord_1532077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532077).length < 2 ^ (prefixWord ++ tailWord_1532077).sum := by decide
  have hdescent : baseEnd_1532077 < baseStart_1532077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532088 : List Nat := [2, 1, 2, 1, 2, 1, 6, 6]
def baseStart_1532088 : Nat := 118140960795 + 1532088 * 2 ^ 59
def prefixEnd_1532088 : Nat := 4983230072969 + 3 ^ 40 * 1532088 * 2
def baseEnd_1532088 : Nat := 116547785034919545533935

theorem tailTrace_1532088 : CollatzResearch.WordTrace tailWord_1532088 prefixEnd_1532088 116547785034919545533935 := by
  unfold tailWord_1532088
  simp only [CollatzResearch.WordTrace]
  refine ⟨27939920036757155321854459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37253226715676207095805945 27939920036757155321854459)
  ·
    refine ⟨41909880055135732982781689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27939920036757155321854459 41909880055135732982781689)
    ·
      refine ⟨31432410041351799737086267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41909880055135732982781689 31432410041351799737086267)
      ·
        refine ⟨47148615062027699605629401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31432410041351799737086267 47148615062027699605629401)
        ·
          refine ⟨35361461296520774704222051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47148615062027699605629401 35361461296520774704222051)
          ·
            refine ⟨53042191944781162056333077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35361461296520774704222051 53042191944781162056333077)
            ·
              refine ⟨2486352747411616971390613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53042191944781162056333077 2486352747411616971390613)
              ·
                refine ⟨116547785034919545533935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2486352747411616971390613 116547785034919545533935)
                ·
                  rfl

theorem cell21_1532088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 6].length) (baseStart_1532088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532088 prefixEnd_1532088 := by exact prefixLift 1532088
  have htrace : WordTrace (prefixWord ++ tailWord_1532088) baseStart_1532088 baseEnd_1532088 := by
    simpa [prefixWord, tailWord_1532088, baseEnd_1532088] using wordTrace_append hprefix tailTrace_1532088
  have hstable : (prefixWord ++ tailWord_1532088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532088).length < 2 ^ (prefixWord ++ tailWord_1532088).sum := by decide
  have hdescent : baseEnd_1532088 < baseStart_1532088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532195 : List Nat := [1, 1, 1, 4, 2, 2, 4, 1, 5]
def baseStart_1532195 : Nat := 118140960795 + 1532195 * 2 ^ 59
def prefixEnd_1532195 : Nat := 4983230072969 + 3 ^ 40 * 1532195 * 2
def baseEnd_1532195 : Nat := 349667773962550228318253

theorem tailTrace_1532195 : CollatzResearch.WordTrace tailWord_1532195 prefixEnd_1532195 349667773962550228318253 := by
  unfold tailWord_1532195
  simp only [CollatzResearch.WordTrace]
  refine ⟨55883742684126667917854039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37255828456084445278569359 55883742684126667917854039)
  ·
    refine ⟨83825614026190001876781059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55883742684126667917854039 83825614026190001876781059)
    ·
      refine ⟨125738421039285002815171589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83825614026190001876781059 125738421039285002815171589)
      ·
        refine ⟨23575953944865938027844673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125738421039285002815171589 23575953944865938027844673)
        ·
          refine ⟨17681965458649453520883505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23575953944865938027844673 17681965458649453520883505)
          ·
            refine ⟨13261474093987090140662629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17681965458649453520883505 13261474093987090140662629)
            ·
              refine ⟨2486526392622579401374243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13261474093987090140662629 2486526392622579401374243)
              ·
                refine ⟨3729789588933869102061365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2486526392622579401374243 3729789588933869102061365)
                ·
                  refine ⟨349667773962550228318253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3729789588933869102061365 349667773962550228318253)
                  ·
                    rfl

theorem cell21_1532195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 5].length) (baseStart_1532195 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532195 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532195 prefixEnd_1532195 := by exact prefixLift 1532195
  have htrace : WordTrace (prefixWord ++ tailWord_1532195) baseStart_1532195 baseEnd_1532195 := by
    simpa [prefixWord, tailWord_1532195, baseEnd_1532195] using wordTrace_append hprefix tailTrace_1532195
  have hstable : (prefixWord ++ tailWord_1532195).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532195).length < 2 ^ (prefixWord ++ tailWord_1532195).sum := by decide
  have hdescent : baseEnd_1532195 < baseStart_1532195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532212 : List Nat := [2, 5, 1, 1, 1, 2, 2, 2, 5]
def baseStart_1532212 : Nat := 118140960795 + 1532212 * 2 ^ 59
def prefixEnd_1532212 : Nat := 4983230072969 + 3 ^ 40 * 1532212 * 2
def baseEnd_1532212 : Nat := 349671653594161976534885

theorem tailTrace_1532212 : CollatzResearch.WordTrace tailWord_1532212 prefixEnd_1532212 349671653594161976534885 := by
  unfold tailWord_1532212
  simp only [CollatzResearch.WordTrace]
  refine ⟨27942181362532539910611445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37256241816710053214148593 27942181362532539910611445)
  ·
    refine ⟨2619579502737425616619823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27942181362532539910611445 2619579502737425616619823)
    ·
      refine ⟨3929369254106138424929735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2619579502737425616619823 3929369254106138424929735)
      ·
        refine ⟨5894053881159207637394603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3929369254106138424929735 5894053881159207637394603)
        ·
          refine ⟨8841080821738811456091905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5894053881159207637394603 8841080821738811456091905)
          ·
            refine ⟨6630810616304108592068929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8841080821738811456091905 6630810616304108592068929)
            ·
              refine ⟨4973107962228081444051697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6630810616304108592068929 4973107962228081444051697)
              ·
                refine ⟨3729830971671061083038773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4973107962228081444051697 3729830971671061083038773)
                ·
                  refine ⟨349671653594161976534885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3729830971671061083038773 349671653594161976534885)
                  ·
                    rfl

theorem cell21_1532212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_1532212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532212 prefixEnd_1532212 := by exact prefixLift 1532212
  have htrace : WordTrace (prefixWord ++ tailWord_1532212) baseStart_1532212 baseEnd_1532212 := by
    simpa [prefixWord, tailWord_1532212, baseEnd_1532212] using wordTrace_append hprefix tailTrace_1532212
  have hstable : (prefixWord ++ tailWord_1532212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532212).length < 2 ^ (prefixWord ++ tailWord_1532212).sum := by decide
  have hdescent : baseEnd_1532212 < baseStart_1532212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532240 : List Nat := [2, 1, 1, 1, 1, 8, 7]
def baseStart_1532240 : Nat := 118140960795 + 1532240 * 2 ^ 59
def prefixEnd_1532240 : Nat := 4983230072969 + 3 ^ 40 * 1532240 * 2
def baseEnd_1532240 : Nat := 38853115952848905563129

theorem tailTrace_1532240 : CollatzResearch.WordTrace tailWord_1532240 prefixEnd_1532240 38853115952848905563129 := by
  unfold tailWord_1532240
  simp only [CollatzResearch.WordTrace]
  refine ⟨27942691984481820301621087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37256922645975760402161449 27942691984481820301621087)
  ·
    refine ⟨41914037976722730452431631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27942691984481820301621087 41914037976722730452431631)
    ·
      refine ⟨62871056965084095678647447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41914037976722730452431631 62871056965084095678647447)
      ·
        refine ⟨94306585447626143517971171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62871056965084095678647447 94306585447626143517971171)
        ·
          refine ⟨141459878171439215276956757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94306585447626143517971171 141459878171439215276956757)
          ·
            refine ⟨1657732947321553304026837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 141459878171439215276956757 1657732947321553304026837)
            ·
              refine ⟨38853115952848905563129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1657732947321553304026837 38853115952848905563129)
              ·
                rfl

theorem cell21_1532240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 7].length) (baseStart_1532240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532240 prefixEnd_1532240 := by exact prefixLift 1532240
  have htrace : WordTrace (prefixWord ++ tailWord_1532240) baseStart_1532240 baseEnd_1532240 := by
    simpa [prefixWord, tailWord_1532240, baseEnd_1532240] using wordTrace_append hprefix tailTrace_1532240
  have hstable : (prefixWord ++ tailWord_1532240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532240).length < 2 ^ (prefixWord ++ tailWord_1532240).sum := by decide
  have hdescent : baseEnd_1532240 < baseStart_1532240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532299 : List Nat := [1, 1, 1, 1, 4, 13]
def baseStart_1532299 : Nat := 118140960795 + 1532299 * 2 ^ 59
def prefixEnd_1532299 : Nat := 4983230072969 + 3 ^ 40 * 1532299 * 2
def baseEnd_1532299 : Nat := 12951537339980339206841

theorem tailTrace_1532299 : CollatzResearch.WordTrace tailWord_1532299 prefixEnd_1532299 12951537339980339206841 := by
  unfold tailWord_1532299
  simp only [CollatzResearch.WordTrace]
  refine ⟨55887535875749893679639951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37258357250499929119759967 55887535875749893679639951)
  ·
    refine ⟨83831303813624840519459927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55887535875749893679639951 83831303813624840519459927)
    ·
      refine ⟨125746955720437260779189891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83831303813624840519459927 125746955720437260779189891)
      ·
        refine ⟨188620433580655891168784837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125746955720437260779189891 188620433580655891168784837)
        ·
          refine ⟨35366331296372979594147157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188620433580655891168784837 35366331296372979594147157)
          ·
            refine ⟨12951537339980339206841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 35366331296372979594147157 12951537339980339206841)
            ·
              rfl

theorem cell21_1532299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 13].length) (baseStart_1532299 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532299 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532299 prefixEnd_1532299 := by exact prefixLift 1532299
  have htrace : WordTrace (prefixWord ++ tailWord_1532299) baseStart_1532299 baseEnd_1532299 := by
    simpa [prefixWord, tailWord_1532299, baseEnd_1532299] using wordTrace_append hprefix tailTrace_1532299
  have hstable : (prefixWord ++ tailWord_1532299).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532299).length < 2 ^ (prefixWord ++ tailWord_1532299).sum := by decide
  have hdescent : baseEnd_1532299 < baseStart_1532299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532364 : List Nat := [2, 2, 1, 4, 3, 1, 2, 1, 5]
def baseStart_1532364 : Nat := 118140960795 + 1532364 * 2 ^ 59
def prefixEnd_1532364 : Nat := 4983230072969 + 3 ^ 40 * 1532364 * 2
def baseEnd_1532364 : Nat := 349706342065043490001241

theorem tailTrace_1532364 : CollatzResearch.WordTrace tailWord_1532364 prefixEnd_1532364 349706342065043490001241 := by
  unfold tailWord_1532364
  simp only [CollatzResearch.WordTrace]
  refine ⟨27944953310257204890378073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37259937747009606520504097 27944953310257204890378073)
  ·
    refine ⟨20958714982692903667783555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27944953310257204890378073 20958714982692903667783555)
    ·
      refine ⟨31438072474039355501675333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20958714982692903667783555 31438072474039355501675333)
      ·
        refine ⟨5894638588882379156564125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31438072474039355501675333 5894638588882379156564125)
        ·
          refine ⟨2210489470830892183711547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5894638588882379156564125 2210489470830892183711547)
          ·
            refine ⟨3315734206246338275567321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2210489470830892183711547 3315734206246338275567321)
            ·
              refine ⟨2486800654684753706675491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3315734206246338275567321 2486800654684753706675491)
              ·
                refine ⟨3730200982027130560013237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2486800654684753706675491 3730200982027130560013237)
                ·
                  refine ⟨349706342065043490001241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3730200982027130560013237 349706342065043490001241)
                  ·
                    rfl

theorem cell21_1532364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_1532364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532364 prefixEnd_1532364 := by exact prefixLift 1532364
  have htrace : WordTrace (prefixWord ++ tailWord_1532364) baseStart_1532364 baseEnd_1532364 := by
    simpa [prefixWord, tailWord_1532364, baseEnd_1532364] using wordTrace_append hprefix tailTrace_1532364
  have hstable : (prefixWord ++ tailWord_1532364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532364).length < 2 ^ (prefixWord ++ tailWord_1532364).sum := by decide
  have hdescent : baseEnd_1532364 < baseStart_1532364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532392 : List Nat := [2, 1, 4, 1, 1, 4, 1, 7]
def baseStart_1532392 : Nat := 118140960795 + 1532392 * 2 ^ 59
def prefixEnd_1532392 : Nat := 4983230072969 + 3 ^ 40 * 1532392 * 2
def baseEnd_1532392 : Nat := 116570910682173887844839

theorem tailTrace_1532392 : CollatzResearch.WordTrace tailWord_1532392 prefixEnd_1532392 116570910682173887844839 := by
  unfold tailWord_1532392
  simp only [CollatzResearch.WordTrace]
  refine ⟨27945463932206485281387715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37260618576275313708516953 27945463932206485281387715)
  ·
    refine ⟨41918195898309727922081573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27945463932206485281387715 41918195898309727922081573)
    ·
      refine ⟨7859661730933073985390295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41918195898309727922081573 7859661730933073985390295)
      ·
        refine ⟨11789492596399610978085443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7859661730933073985390295 11789492596399610978085443)
        ·
          refine ⟨17684238894599416467128165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11789492596399610978085443 17684238894599416467128165)
          ·
            refine ⟨3315794792737390587586531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17684238894599416467128165 3315794792737390587586531)
            ·
              refine ⟨4973692189106085881379797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3315794792737390587586531 4973692189106085881379797)
              ·
                refine ⟨116570910682173887844839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4973692189106085881379797 116570910682173887844839)
                ·
                  rfl

theorem cell21_1532392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 7].length) (baseStart_1532392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532392 prefixEnd_1532392 := by exact prefixLift 1532392
  have htrace : WordTrace (prefixWord ++ tailWord_1532392) baseStart_1532392 baseEnd_1532392 := by
    simpa [prefixWord, tailWord_1532392, baseEnd_1532392] using wordTrace_append hprefix tailTrace_1532392
  have hstable : (prefixWord ++ tailWord_1532392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532392).length < 2 ^ (prefixWord ++ tailWord_1532392).sum := by decide
  have hdescent : baseEnd_1532392 < baseStart_1532392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532429 : List Nat := [1, 7, 1, 1, 1, 1, 4, 1, 4]
def baseStart_1532429 : Nat := 118140960795 + 1532429 * 2 ^ 59
def prefixEnd_1532429 : Nat := 4983230072969 + 3 ^ 40 * 1532429 * 2
def baseEnd_1532429 : Nat := 349721175950617821417775

theorem tailTrace_1532429 : CollatzResearch.WordTrace tailWord_1532429 prefixEnd_1532429 349721175950617821417775 := by
  unfold tailWord_1532429
  simp only [CollatzResearch.WordTrace]
  refine ⟨55892277365278925881872341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37261518243519283921248227 55892277365278925881872341)
  ·
    refine ⟨1309975250748724825356383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 55892277365278925881872341 1309975250748724825356383)
    ·
      refine ⟨1964962876123087238034575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1309975250748724825356383 1964962876123087238034575)
      ·
        refine ⟨2947444314184630857051863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1964962876123087238034575 2947444314184630857051863)
        ·
          refine ⟨4421166471276946285577795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2947444314184630857051863 4421166471276946285577795)
          ·
            refine ⟨6631749706915419428366693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4421166471276946285577795 6631749706915419428366693)
            ·
              refine ⟨1243453070046641142818755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6631749706915419428366693 1243453070046641142818755)
              ·
                refine ⟨1865179605069961714228133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1243453070046641142818755 1865179605069961714228133)
                ·
                  refine ⟨349721175950617821417775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1865179605069961714228133 349721175950617821417775)
                  ·
                    rfl

theorem cell21_1532429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_1532429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532429 prefixEnd_1532429 := by exact prefixLift 1532429
  have htrace : WordTrace (prefixWord ++ tailWord_1532429) baseStart_1532429 baseEnd_1532429 := by
    simpa [prefixWord, tailWord_1532429, baseEnd_1532429] using wordTrace_append hprefix tailTrace_1532429
  have hstable : (prefixWord ++ tailWord_1532429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532429).length < 2 ^ (prefixWord ++ tailWord_1532429).sum := by decide
  have hdescent : baseEnd_1532429 < baseStart_1532429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532516 : List Nat := [2, 3, 1, 1, 2, 2, 4, 3, 3]
def baseStart_1532516 : Nat := 118140960795 + 1532516 * 2 ^ 59
def prefixEnd_1532516 : Nat := 4983230072969 + 3 ^ 40 * 1532516 * 2
def baseEnd_1532516 : Nat := 349741030535925003467597

theorem tailTrace_1532516 : CollatzResearch.WordTrace tailWord_1532516 prefixEnd_1532516 349741030535925003467597 := by
  unfold tailWord_1532516
  simp only [CollatzResearch.WordTrace]
  refine ⟨27947725257981869870144701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37263633677309159826859601 27947725257981869870144701)
  ·
    refine ⟨10480396971743201201304263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27947725257981869870144701 10480396971743201201304263)
    ·
      refine ⟨15720595457614801801956395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10480396971743201201304263 15720595457614801801956395)
      ·
        refine ⟨23580893186422202702934593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15720595457614801801956395 23580893186422202702934593)
        ·
          refine ⟨17685669889816652027200945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23580893186422202702934593 17685669889816652027200945)
          ·
            refine ⟨13264252417362489020400709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17685669889816652027200945 13264252417362489020400709)
            ·
              refine ⟨2487047328255466691325133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13264252417362489020400709 2487047328255466691325133)
              ·
                refine ⟨932642748095800009246925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2487047328255466691325133 932642748095800009246925)
                ·
                  refine ⟨349741030535925003467597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 932642748095800009246925 349741030535925003467597)
                  ·
                    rfl

theorem cell21_1532516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_1532516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532516 prefixEnd_1532516 := by exact prefixLift 1532516
  have htrace : WordTrace (prefixWord ++ tailWord_1532516) baseStart_1532516 baseEnd_1532516 := by
    simpa [prefixWord, tailWord_1532516, baseEnd_1532516] using wordTrace_append hprefix tailTrace_1532516
  have hstable : (prefixWord ++ tailWord_1532516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532516).length < 2 ^ (prefixWord ++ tailWord_1532516).sum := by decide
  have hdescent : baseEnd_1532516 < baseStart_1532516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532530 : List Nat := [3, 2, 1, 2, 4, 1, 1, 1, 6]
def baseStart_1532530 : Nat := 118140960795 + 1532530 * 2 ^ 59
def prefixEnd_1532530 : Nat := 4983230072969 + 3 ^ 40 * 1532530 * 2
def baseEnd_1532530 : Nat := 349744225526664090234235

theorem tailTrace_1532530 : CollatzResearch.WordTrace tailWord_1532530 prefixEnd_1532530 349744225526664090234235 := by
  unfold tailWord_1532530
  simp only [CollatzResearch.WordTrace]
  refine ⟨13973990284478255032824761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37263974091942013420866029 13973990284478255032824761)
  ·
    refine ⟨10480492713358691274618571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13973990284478255032824761 10480492713358691274618571)
    ·
      refine ⟨15720739070038036911927857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10480492713358691274618571 15720739070038036911927857)
      ·
        refine ⟨11790554302528527683945893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15720739070038036911927857 11790554302528527683945893)
        ·
          refine ⟨2210728931724098940739855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11790554302528527683945893 2210728931724098940739855)
          ·
            refine ⟨3316093397586148411109783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2210728931724098940739855 3316093397586148411109783)
            ·
              refine ⟨4974140096379222616664675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3316093397586148411109783 4974140096379222616664675)
              ·
                refine ⟨7461210144568833924997013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4974140096379222616664675 7461210144568833924997013)
                ·
                  refine ⟨349744225526664090234235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7461210144568833924997013 349744225526664090234235)
                  ·
                    rfl

theorem cell21_1532530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_1532530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532530 prefixEnd_1532530 := by exact prefixLift 1532530
  have htrace : WordTrace (prefixWord ++ tailWord_1532530) baseStart_1532530 baseEnd_1532530 := by
    simpa [prefixWord, tailWord_1532530, baseEnd_1532530] using wordTrace_append hprefix tailTrace_1532530
  have hstable : (prefixWord ++ tailWord_1532530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532530).length < 2 ^ (prefixWord ++ tailWord_1532530).sum := by decide
  have hdescent : baseEnd_1532530 < baseStart_1532530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532598 : List Nat := [5, 1, 3, 1, 3, 1, 2, 1, 4]
def baseStart_1532598 : Nat := 118140960795 + 1532598 * 2 ^ 59
def prefixEnd_1532598 : Nat := 4983230072969 + 3 ^ 40 * 1532598 * 2
def baseEnd_1532598 : Nat := 349759744053111083100763

theorem tailTrace_1532598 : CollatzResearch.WordTrace tailWord_1532598 prefixEnd_1532598 349759744053111083100763 := by
  unfold tailWord_1532598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3493652581354166734048403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37265627534444445163182965 3493652581354166734048403)
  ·
    refine ⟨5240478872031250101072605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3493652581354166734048403 5240478872031250101072605)
    ·
      refine ⟨1965179577011718787902227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5240478872031250101072605 1965179577011718787902227)
      ·
        refine ⟨2947769365517578181853341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1965179577011718787902227 2947769365517578181853341)
        ·
          refine ⟨1105413512069091818195003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2947769365517578181853341 1105413512069091818195003)
          ·
            refine ⟨1658120268103637727292505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1105413512069091818195003 1658120268103637727292505)
            ·
              refine ⟨1243590201077728295469379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1658120268103637727292505 1243590201077728295469379)
              ·
                refine ⟨1865385301616592443204069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1243590201077728295469379 1865385301616592443204069)
                ·
                  refine ⟨349759744053111083100763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1865385301616592443204069 349759744053111083100763)
                  ·
                    rfl

theorem cell21_1532598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_1532598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532598 prefixEnd_1532598 := by exact prefixLift 1532598
  have htrace : WordTrace (prefixWord ++ tailWord_1532598) baseStart_1532598 baseEnd_1532598 := by
    simpa [prefixWord, tailWord_1532598, baseEnd_1532598] using wordTrace_append hprefix tailTrace_1532598
  have hstable : (prefixWord ++ tailWord_1532598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532598).length < 2 ^ (prefixWord ++ tailWord_1532598).sum := by decide
  have hdescent : baseEnd_1532598 < baseStart_1532598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532606 : List Nat := [4, 2, 1, 1, 2, 1, 3, 3, 4]
def baseStart_1532606 : Nat := 118140960795 + 1532606 * 2 ^ 59
def prefixEnd_1532606 : Nat := 4983230072969 + 3 ^ 40 * 1532606 * 2
def baseEnd_1532606 : Nat := 349761569762104846967413

theorem tailTrace_1532606 : CollatzResearch.WordTrace tailWord_1532606 prefixEnd_1532606 349761569762104846967413 := by
  unfold tailWord_1532606
  simp only [CollatzResearch.WordTrace]
  refine ⟨6987341635704710638883209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37265822057091790074043781 6987341635704710638883209)
  ·
    refine ⟨5240506226778532979162407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6987341635704710638883209 5240506226778532979162407)
    ·
      refine ⟨7860759340167799468743611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5240506226778532979162407 7860759340167799468743611)
      ·
        refine ⟨11791139010251699203115417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7860759340167799468743611 11791139010251699203115417)
        ·
          refine ⟨8843354257688774402336563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11791139010251699203115417 8843354257688774402336563)
          ·
            refine ⟨13265031386533161603504845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8843354257688774402336563 13265031386533161603504845)
            ·
              refine ⟨4974386769949935601314317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13265031386533161603504845 4974386769949935601314317)
              ·
                refine ⟨1865395038731225850492869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4974386769949935601314317 1865395038731225850492869)
                ·
                  refine ⟨349761569762104846967413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1865395038731225850492869 349761569762104846967413)
                  ·
                    rfl

theorem cell21_1532606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_1532606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532606 prefixEnd_1532606 := by exact prefixLift 1532606
  have htrace : WordTrace (prefixWord ++ tailWord_1532606) baseStart_1532606 baseEnd_1532606 := by
    simpa [prefixWord, tailWord_1532606, baseEnd_1532606] using wordTrace_append hprefix tailTrace_1532606
  have hstable : (prefixWord ++ tailWord_1532606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532606).length < 2 ^ (prefixWord ++ tailWord_1532606).sum := by decide
  have hdescent : baseEnd_1532606 < baseStart_1532606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532620 : List Nat := [2, 2, 1, 5, 1, 1, 2, 7]
def baseStart_1532620 : Nat := 118140960795 + 1532620 * 2 ^ 59
def prefixEnd_1532620 : Nat := 4983230072969 + 3 ^ 40 * 1532620 * 2
def baseEnd_1532620 : Nat := 116588254917614644578017

theorem tailTrace_1532620 : CollatzResearch.WordTrace tailWord_1532620 prefixEnd_1532620 116588254917614644578017 := by
  unfold tailWord_1532620
  simp only [CollatzResearch.WordTrace]
  refine ⟨27949621853793482751037657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37266162471724643668050209 27949621853793482751037657)
  ·
    refine ⟨20962216390345112063278243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27949621853793482751037657 20962216390345112063278243)
    ·
      refine ⟨31443324585517668094917365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20962216390345112063278243 31443324585517668094917365)
      ·
        refine ⟨2947811679892281383898503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31443324585517668094917365 2947811679892281383898503)
        ·
          refine ⟨4421717519838422075847755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2947811679892281383898503 4421717519838422075847755)
          ·
            refine ⟨6632576279757633113771633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4421717519838422075847755 6632576279757633113771633)
            ·
              refine ⟨4974432209818224835328725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6632576279757633113771633 4974432209818224835328725)
              ·
                refine ⟨116588254917614644578017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4974432209818224835328725 116588254917614644578017)
                ·
                  rfl

theorem cell21_1532620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 7].length) (baseStart_1532620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532620 prefixEnd_1532620 := by exact prefixLift 1532620
  have htrace : WordTrace (prefixWord ++ tailWord_1532620) baseStart_1532620 baseEnd_1532620 := by
    simpa [prefixWord, tailWord_1532620, baseEnd_1532620] using wordTrace_append hprefix tailTrace_1532620
  have hstable : (prefixWord ++ tailWord_1532620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532620).length < 2 ^ (prefixWord ++ tailWord_1532620).sum := by decide
  have hdescent : baseEnd_1532620 < baseStart_1532620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532730 : List Nat := [3, 1, 1, 1, 7, 1, 2, 5]
def baseStart_1532730 : Nat := 118140960795 + 1532730 * 2 ^ 59
def prefixEnd_1532730 : Nat := 4983230072969 + 3 ^ 40 * 1532730 * 2
def baseEnd_1532730 : Nat := 116596622750502728966831

theorem tailTrace_1532730 : CollatzResearch.WordTrace tailWord_1532730 prefixEnd_1532730 116596622750502728966831 := by
  unfold tailWord_1532730
  simp only [CollatzResearch.WordTrace]
  refine ⟨13975813934297113572144911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37268837158125636192386429 13975813934297113572144911)
  ·
    refine ⟨20963720901445670358217367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13975813934297113572144911 20963720901445670358217367)
    ·
      refine ⟨31445581352168505537326051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20963720901445670358217367 31445581352168505537326051)
      ·
        refine ⟨47168372028252758305989077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31445581352168505537326051 47168372028252758305989077)
        ·
          refine ⟨1105508719412174022796619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 47168372028252758305989077 1105508719412174022796619)
          ·
            refine ⟨1658263079118261034194929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1105508719412174022796619 1658263079118261034194929)
            ·
              refine ⟨1243697309338695775646197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1658263079118261034194929 1243697309338695775646197)
              ·
                refine ⟨116596622750502728966831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1243697309338695775646197 116596622750502728966831)
                ·
                  rfl

theorem cell21_1532730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 5].length) (baseStart_1532730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532730 prefixEnd_1532730 := by exact prefixLift 1532730
  have htrace : WordTrace (prefixWord ++ tailWord_1532730) baseStart_1532730 baseEnd_1532730 := by
    simpa [prefixWord, tailWord_1532730, baseEnd_1532730] using wordTrace_append hprefix tailTrace_1532730
  have hstable : (prefixWord ++ tailWord_1532730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532730).length < 2 ^ (prefixWord ++ tailWord_1532730).sum := by decide
  have hdescent : baseEnd_1532730 < baseStart_1532730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532772 : List Nat := [2, 3, 1, 1, 4, 2, 2, 6]
def baseStart_1532772 : Nat := 118140960795 + 1532772 * 2 ^ 59
def prefixEnd_1532772 : Nat := 4983230072969 + 3 ^ 40 * 1532772 * 2
def baseEnd_1532772 : Nat := 116599817741241815733469

theorem tailTrace_1532772 : CollatzResearch.WordTrace tailWord_1532772 prefixEnd_1532772 116599817741241815733469 := by
  unfold tailWord_1532772
  simp only [CollatzResearch.WordTrace]
  refine ⟨27952393801518147730804285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37269858402024196974405713 27952393801518147730804285)
  ·
    refine ⟨10482147675569305399051607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27952393801518147730804285 10482147675569305399051607)
    ·
      refine ⟨15723221513353958098577411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10482147675569305399051607 15723221513353958098577411)
      ·
        refine ⟨23584832270030937147866117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15723221513353958098577411 23584832270030937147866117)
        ·
          refine ⟨4422156050630800715224897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23584832270030937147866117 4422156050630800715224897)
          ·
            refine ⟨3316617037973100536418673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4422156050630800715224897 3316617037973100536418673)
            ·
              refine ⟨2487462778479825402314005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3316617037973100536418673 2487462778479825402314005)
              ·
                refine ⟨116599817741241815733469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2487462778479825402314005 116599817741241815733469)
                ·
                  rfl

theorem cell21_1532772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 6].length) (baseStart_1532772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532772 prefixEnd_1532772 := by exact prefixLift 1532772
  have htrace : WordTrace (prefixWord ++ tailWord_1532772) baseStart_1532772 baseEnd_1532772 := by
    simpa [prefixWord, tailWord_1532772, baseEnd_1532772] using wordTrace_append hprefix tailTrace_1532772
  have hstable : (prefixWord ++ tailWord_1532772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532772).length < 2 ^ (prefixWord ++ tailWord_1532772).sum := by decide
  have hdescent : baseEnd_1532772 < baseStart_1532772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532775 : List Nat := [1, 1, 5, 1, 2, 4, 2, 1, 4]
def baseStart_1532775 : Nat := 118140960795 + 1532775 * 2 ^ 59
def prefixEnd_1532775 : Nat := 4983230072969 + 3 ^ 40 * 1532775 * 2
def baseEnd_1532775 : Nat := 349800137864598108650401

theorem tailTrace_1532775 : CollatzResearch.WordTrace tailWord_1532775 prefixEnd_1532775 349800137864598108650401 := by
  unfold tailWord_1532775
  simp only [CollatzResearch.WordTrace]
  refine ⟨55904897022025426973967779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37269931348016951315978519 55904897022025426973967779)
  ·
    refine ⟨83857345533038140460951669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55904897022025426973967779 83857345533038140460951669)
    ·
      refine ⟨7861626143722325668214219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83857345533038140460951669 7861626143722325668214219)
      ·
        refine ⟨11792439215583488502321329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7861626143722325668214219 11792439215583488502321329)
        ·
          refine ⟨8844329411687616376740997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11792439215583488502321329 8844329411687616376740997)
          ·
            refine ⟨1658311764691428070638937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8844329411687616376740997 1658311764691428070638937)
            ·
              refine ⟨1243733823518571052979203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1658311764691428070638937 1243733823518571052979203)
              ·
                refine ⟨1865600735277856579468805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1243733823518571052979203 1865600735277856579468805)
                ·
                  refine ⟨349800137864598108650401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1865600735277856579468805 349800137864598108650401)
                  ·
                    rfl

theorem cell21_1532775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 4].length) (baseStart_1532775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532775 prefixEnd_1532775 := by exact prefixLift 1532775
  have htrace : WordTrace (prefixWord ++ tailWord_1532775) baseStart_1532775 baseEnd_1532775 := by
    simpa [prefixWord, tailWord_1532775, baseEnd_1532775] using wordTrace_append hprefix tailTrace_1532775
  have hstable : (prefixWord ++ tailWord_1532775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532775).length < 2 ^ (prefixWord ++ tailWord_1532775).sum := by decide
  have hdescent : baseEnd_1532775 < baseStart_1532775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532786 : List Nat := [3, 2, 1, 2, 1, 1, 2, 4, 5]
def baseStart_1532786 : Nat := 118140960795 + 1532786 * 2 ^ 59
def prefixEnd_1532786 : Nat := 4983230072969 + 3 ^ 40 * 1532786 * 2
def baseEnd_1532786 : Nat := 349802648214464533967045

theorem tailTrace_1532786 : CollatzResearch.WordTrace tailWord_1532786 prefixEnd_1532786 349802648214464533967045 := by
  unfold tailWord_1532786
  simp only [CollatzResearch.WordTrace]
  refine ⟨13976324556246393963154553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37270198816657050568412141 13976324556246393963154553)
  ·
    refine ⟨10482243417184795472365915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13976324556246393963154553 10482243417184795472365915)
    ·
      refine ⟨15723365125777193208548873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10482243417184795472365915 15723365125777193208548873)
      ·
        refine ⟨11792523844332894906411655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15723365125777193208548873 11792523844332894906411655)
        ·
          refine ⟨17688785766499342359617483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11792523844332894906411655 17688785766499342359617483)
          ·
            refine ⟨26533178649749013539426225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17688785766499342359617483 26533178649749013539426225)
            ·
              refine ⟨19899883987311760154569669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26533178649749013539426225 19899883987311760154569669)
              ·
                refine ⟨3731228247620955028981813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19899883987311760154569669 3731228247620955028981813)
                ·
                  refine ⟨349802648214464533967045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3731228247620955028981813 349802648214464533967045)
                  ·
                    rfl

theorem cell21_1532786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_1532786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532786 prefixEnd_1532786 := by exact prefixLift 1532786
  have htrace : WordTrace (prefixWord ++ tailWord_1532786) baseStart_1532786 baseEnd_1532786 := by
    simpa [prefixWord, tailWord_1532786, baseEnd_1532786] using wordTrace_append hprefix tailTrace_1532786
  have hstable : (prefixWord ++ tailWord_1532786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532786).length < 2 ^ (prefixWord ++ tailWord_1532786).sum := by decide
  have hdescent : baseEnd_1532786 < baseStart_1532786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532800 : List Nat := [2, 1, 1, 2, 1, 2, 2, 4, 6]
def baseStart_1532800 : Nat := 118140960795 + 1532800 * 2 ^ 59
def prefixEnd_1532800 : Nat := 4983230072969 + 3 ^ 40 * 1532800 * 2
def baseEnd_1532800 : Nat := 349805843205203620733683

theorem tailTrace_1532800 : CollatzResearch.WordTrace tailWord_1532800 prefixEnd_1532800 349805843205203620733683 := by
  unfold tailWord_1532800
  simp only [CollatzResearch.WordTrace]
  refine ⟨27952904423467428121813927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37270539231289904162418569 27952904423467428121813927)
  ·
    refine ⟨41929356635201142182720891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27952904423467428121813927 41929356635201142182720891)
    ·
      refine ⟨62894034952801713274081337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41929356635201142182720891 62894034952801713274081337)
      ·
        refine ⟨47170526214601284955561003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62894034952801713274081337 47170526214601284955561003)
        ·
          refine ⟨70755789321901927433341505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47170526214601284955561003 70755789321901927433341505)
          ·
            refine ⟨53066841991426445575006129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70755789321901927433341505 53066841991426445575006129)
            ·
              refine ⟨39800131493569834181254597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53066841991426445575006129 39800131493569834181254597)
              ·
                refine ⟨7462524655044343908985237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39800131493569834181254597 7462524655044343908985237)
                ·
                  refine ⟨349805843205203620733683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7462524655044343908985237 349805843205203620733683)
                  ·
                    rfl

theorem cell21_1532800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 6].length) (baseStart_1532800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532800 prefixEnd_1532800 := by exact prefixLift 1532800
  have htrace : WordTrace (prefixWord ++ tailWord_1532800) baseStart_1532800 baseEnd_1532800 := by
    simpa [prefixWord, tailWord_1532800, baseEnd_1532800] using wordTrace_append hprefix tailTrace_1532800
  have hstable : (prefixWord ++ tailWord_1532800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532800).length < 2 ^ (prefixWord ++ tailWord_1532800).sum := by decide
  have hdescent : baseEnd_1532800 < baseStart_1532800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532803 : List Nat := [1, 1, 1, 3, 4, 1, 2, 5, 3]
def baseStart_1532803 : Nat := 118140960795 + 1532803 * 2 ^ 59
def prefixEnd_1532803 : Nat := 4983230072969 + 3 ^ 40 * 1532803 * 2
def baseEnd_1532803 : Nat := 349806527846076282183677

theorem tailTrace_1532803 : CollatzResearch.WordTrace tailWord_1532803 prefixEnd_1532803 349806527846076282183677 := by
  unfold tailWord_1532803
  simp only [CollatzResearch.WordTrace]
  refine ⟨55905918265923987755987063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37270612177282658503991375 55905918265923987755987063)
  ·
    refine ⟨83858877398885981633980595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55905918265923987755987063 83858877398885981633980595)
    ·
      refine ⟨125788316098328972450970893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83858877398885981633980595 125788316098328972450970893)
      ·
        refine ⟨47170618536873364669114085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125788316098328972450970893 47170618536873364669114085)
        ·
          refine ⟨8844490975663755875458891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47170618536873364669114085 8844490975663755875458891)
          ·
            refine ⟨13266736463495633813188337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8844490975663755875458891 13266736463495633813188337)
            ·
              refine ⟨9950052347621725359891253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13266736463495633813188337 9950052347621725359891253)
              ·
                refine ⟨932817407589536752489805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9950052347621725359891253 932817407589536752489805)
                ·
                  refine ⟨349806527846076282183677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 932817407589536752489805 349806527846076282183677)
                  ·
                    rfl

theorem cell21_1532803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5, 3].length) (baseStart_1532803 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532803 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532803 prefixEnd_1532803 := by exact prefixLift 1532803
  have htrace : WordTrace (prefixWord ++ tailWord_1532803) baseStart_1532803 baseEnd_1532803 := by
    simpa [prefixWord, tailWord_1532803, baseEnd_1532803] using wordTrace_append hprefix tailTrace_1532803
  have hstable : (prefixWord ++ tailWord_1532803).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532803).length < 2 ^ (prefixWord ++ tailWord_1532803).sum := by decide
  have hdescent : baseEnd_1532803 < baseStart_1532803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532820 : List Nat := [2, 4, 2, 1, 1, 1, 3, 4, 3]
def baseStart_1532820 : Nat := 118140960795 + 1532820 * 2 ^ 59
def prefixEnd_1532820 : Nat := 4983230072969 + 3 ^ 40 * 1532820 * 2
def baseEnd_1532820 : Nat := 349810407477688030400309

theorem tailTrace_1532820 : CollatzResearch.WordTrace tailWord_1532820 prefixEnd_1532820 349810407477688030400309 := by
  unfold tailWord_1532820
  simp only [CollatzResearch.WordTrace]
  refine ⟨27953269153431199829677957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37271025537908266439570609 27953269153431199829677957)
  ·
    refine ⟨5241237966268349968064617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27953269153431199829677957 5241237966268349968064617)
    ·
      refine ⟨3930928474701262476048463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5241237966268349968064617 3930928474701262476048463)
      ·
        refine ⟨5896392712051893714072695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3930928474701262476048463 5896392712051893714072695)
        ·
          refine ⟨8844589068077840571109043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5896392712051893714072695 8844589068077840571109043)
          ·
            refine ⟨13266883602116760856663565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8844589068077840571109043 13266883602116760856663565)
            ·
              refine ⟨4975081350793785321248837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13266883602116760856663565 4975081350793785321248837)
              ·
                refine ⟨932827753273834747734157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4975081350793785321248837 932827753273834747734157)
                ·
                  refine ⟨349810407477688030400309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 932827753273834747734157 349810407477688030400309)
                  ·
                    rfl

theorem cell21_1532820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_1532820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532820 prefixEnd_1532820 := by exact prefixLift 1532820
  have htrace : WordTrace (prefixWord ++ tailWord_1532820) baseStart_1532820 baseEnd_1532820 := by
    simpa [prefixWord, tailWord_1532820, baseEnd_1532820] using wordTrace_append hprefix tailTrace_1532820
  have hstable : (prefixWord ++ tailWord_1532820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532820).length < 2 ^ (prefixWord ++ tailWord_1532820).sum := by decide
  have hdescent : baseEnd_1532820 < baseStart_1532820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532834 : List Nat := [3, 3, 1, 2, 2, 1, 2, 3, 4]
def baseStart_1532834 : Nat := 118140960795 + 1532834 * 2 ^ 59
def prefixEnd_1532834 : Nat := 4983230072969 + 3 ^ 40 * 1532834 * 2
def baseEnd_1532834 : Nat := 349813602468427117166947

theorem tailTrace_1532834 : CollatzResearch.WordTrace tailWord_1532834 prefixEnd_1532834 349813602468427117166947 := by
  unfold tailWord_1532834
  simp only [CollatzResearch.WordTrace]
  refine ⟨13976762232202920012591389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37271365952541120033577037 13976762232202920012591389)
  ·
    refine ⟨5241285837076095004721771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13976762232202920012591389 5241285837076095004721771)
    ·
      refine ⟨7861928755614142507082657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5241285837076095004721771 7861928755614142507082657)
      ·
        refine ⟨5896446566710606880311993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7861928755614142507082657 5896446566710606880311993)
        ·
          refine ⟨4422334925032955160233995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5896446566710606880311993 4422334925032955160233995)
          ·
            refine ⟨6633502387549432740350993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4422334925032955160233995 6633502387549432740350993)
            ·
              refine ⟨4975126790662074555263245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6633502387549432740350993 4975126790662074555263245)
              ·
                refine ⟨1865672546498277958223717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4975126790662074555263245 1865672546498277958223717)
                ·
                  refine ⟨349813602468427117166947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1865672546498277958223717 349813602468427117166947)
                  ·
                    rfl

theorem cell21_1532834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_1532834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532834 prefixEnd_1532834 := by exact prefixLift 1532834
  have htrace : WordTrace (prefixWord ++ tailWord_1532834) baseStart_1532834 baseEnd_1532834 := by
    simpa [prefixWord, tailWord_1532834, baseEnd_1532834] using wordTrace_append hprefix tailTrace_1532834
  have hstable : (prefixWord ++ tailWord_1532834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532834).length < 2 ^ (prefixWord ++ tailWord_1532834).sum := by decide
  have hdescent : baseEnd_1532834 < baseStart_1532834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532862 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 7]
def baseStart_1532862 : Nat := 118140960795 + 1532862 * 2 ^ 59
def prefixEnd_1532862 : Nat := 4983230072969 + 3 ^ 40 * 1532862 * 2
def baseEnd_1532862 : Nat := 349819992449905290700223

theorem tailTrace_1532862 : CollatzResearch.WordTrace tailWord_1532862 prefixEnd_1532862 349819992449905290700223 := by
  unfold tailWord_1532862
  simp only [CollatzResearch.WordTrace]
  refine ⟨6988508771588780104048105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37272046781806827221589893 6988508771588780104048105)
  ·
    refine ⟨5241381578691585078036079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6988508771588780104048105 5241381578691585078036079)
    ·
      refine ⟨7862072368037377617054119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5241381578691585078036079 7862072368037377617054119)
      ·
        refine ⟨11793108552056066425581179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7862072368037377617054119 11793108552056066425581179)
        ·
          refine ⟨17689662828084099638371769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11793108552056066425581179 17689662828084099638371769)
          ·
            refine ⟨13267247121063074728778827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17689662828084099638371769 13267247121063074728778827)
            ·
              refine ⟨19900870681594612093168241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13267247121063074728778827 19900870681594612093168241)
              ·
                refine ⟨14925653011195959069876181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19900870681594612093168241 14925653011195959069876181)
                ·
                  refine ⟨349819992449905290700223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14925653011195959069876181 349819992449905290700223)
                  ·
                    rfl

theorem cell21_1532862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_1532862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532862 prefixEnd_1532862 := by exact prefixLift 1532862
  have htrace : WordTrace (prefixWord ++ tailWord_1532862) baseStart_1532862 baseEnd_1532862 := by
    simpa [prefixWord, tailWord_1532862, baseEnd_1532862] using wordTrace_append hprefix tailTrace_1532862
  have hstable : (prefixWord ++ tailWord_1532862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532862).length < 2 ^ (prefixWord ++ tailWord_1532862).sum := by decide
  have hdescent : baseEnd_1532862 < baseStart_1532862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532868 : List Nat := [2, 3, 3, 3, 1, 2, 1, 2, 4]
def baseStart_1532868 : Nat := 118140960795 + 1532868 * 2 ^ 59
def prefixEnd_1532868 : Nat := 4983230072969 + 3 ^ 40 * 1532868 * 2
def baseEnd_1532868 : Nat := 349821361731650613600211

theorem tailTrace_1532868 : CollatzResearch.WordTrace tailWord_1532868 prefixEnd_1532868 349821361731650613600211 := by
  unfold tailWord_1532868
  simp only [CollatzResearch.WordTrace]
  refine ⟨27954144505344251928551629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37272192673792335904735505 27954144505344251928551629)
  ·
    refine ⟨10482804189504094473206861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27954144505344251928551629 10482804189504094473206861)
    ·
      refine ⟨3931051571064035427452573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10482804189504094473206861 3931051571064035427452573)
      ·
        refine ⟨1474144339149013285294715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3931051571064035427452573 1474144339149013285294715)
        ·
          refine ⟨2211216508723519927942073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1474144339149013285294715 2211216508723519927942073)
          ·
            refine ⟨1658412381542639945956555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2211216508723519927942073 1658412381542639945956555)
            ·
              refine ⟨2487618572313959918934833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1658412381542639945956555 2487618572313959918934833)
              ·
                refine ⟨1865713929235469939201125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2487618572313959918934833 1865713929235469939201125)
                ·
                  refine ⟨349821361731650613600211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1865713929235469939201125 349821361731650613600211)
                  ·
                    rfl

theorem cell21_1532868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_1532868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532868 prefixEnd_1532868 := by exact prefixLift 1532868
  have htrace : WordTrace (prefixWord ++ tailWord_1532868) baseStart_1532868 baseEnd_1532868 := by
    simpa [prefixWord, tailWord_1532868, baseEnd_1532868] using wordTrace_append hprefix tailTrace_1532868
  have hstable : (prefixWord ++ tailWord_1532868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532868).length < 2 ^ (prefixWord ++ tailWord_1532868).sum := by decide
  have hdescent : baseEnd_1532868 < baseStart_1532868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532879 : List Nat := [1, 1, 2, 1, 1, 6, 2, 4, 3]
def baseStart_1532879 : Nat := 118140960795 + 1532879 * 2 ^ 59
def prefixEnd_1532879 : Nat := 4983230072969 + 3 ^ 40 * 1532879 * 2
def baseEnd_1532879 : Nat := 349823872081517038916855

theorem tailTrace_1532879 : CollatzResearch.WordTrace tailWord_1532879 prefixEnd_1532879 349823872081517038916855 := by
  unfold tailWord_1532879
  simp only [CollatzResearch.WordTrace]
  refine ⟨55908690213648652735753691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37272460142432435157169127 55908690213648652735753691)
  ·
    refine ⟨83863035320472979103630537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55908690213648652735753691 83863035320472979103630537)
    ·
      refine ⟨62897276490354734327722903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83863035320472979103630537 62897276490354734327722903)
      ·
        refine ⟨94345914735532101491584355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62897276490354734327722903 94345914735532101491584355)
        ·
          refine ⟨141518872103298152237376533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94345914735532101491584355 141518872103298152237376533)
          ·
            refine ⟨6633697129842100886127025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 141518872103298152237376533 6633697129842100886127025)
            ·
              refine ⟨4975272847381575664595269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6633697129842100886127025 4975272847381575664595269)
              ·
                refine ⟨932863658884045437111613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4975272847381575664595269 932863658884045437111613)
                ·
                  refine ⟨349823872081517038916855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 932863658884045437111613 349823872081517038916855)
                  ·
                    rfl

theorem cell21_1532879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4, 3].length) (baseStart_1532879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532879 prefixEnd_1532879 := by exact prefixLift 1532879
  have htrace : WordTrace (prefixWord ++ tailWord_1532879) baseStart_1532879 baseEnd_1532879 := by
    simpa [prefixWord, tailWord_1532879, baseEnd_1532879] using wordTrace_append hprefix tailTrace_1532879
  have hstable : (prefixWord ++ tailWord_1532879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532879).length < 2 ^ (prefixWord ++ tailWord_1532879).sum := by decide
  have hdescent : baseEnd_1532879 < baseStart_1532879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532916 : List Nat := [2, 6, 2, 1, 2, 1, 7]
def baseStart_1532916 : Nat := 118140960795 + 1532916 * 2 ^ 59
def prefixEnd_1532916 : Nat := 4983230072969 + 3 ^ 40 * 1532916 * 2
def baseEnd_1532916 : Nat := 38870257331734799644457

theorem tailTrace_1532916 : CollatzResearch.WordTrace tailWord_1532916 prefixEnd_1532916 38870257331734799644457 := by
  unfold tailWord_1532916
  simp only [CollatzResearch.WordTrace]
  refine ⟨27955019857257304027425301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37273359809676405369900401 27955019857257304027425301)
  ·
    refine ⟨1310391555808936126285561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27955019857257304027425301 1310391555808936126285561)
    ·
      refine ⟨982793666856702094714171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1310391555808936126285561 982793666856702094714171)
      ·
        refine ⟨1474190500285053142071257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 982793666856702094714171 1474190500285053142071257)
        ·
          refine ⟨1105642875213789856553443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1474190500285053142071257 1105642875213789856553443)
          ·
            refine ⟨1658464312820684784830165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1105642875213789856553443 1658464312820684784830165)
            ·
              refine ⟨38870257331734799644457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1658464312820684784830165 38870257331734799644457)
              ·
                rfl

theorem cell21_1532916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 7].length) (baseStart_1532916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532916 prefixEnd_1532916 := by exact prefixLift 1532916
  have htrace : WordTrace (prefixWord ++ tailWord_1532916) baseStart_1532916 baseEnd_1532916 := by
    simpa [prefixWord, tailWord_1532916, baseEnd_1532916] using wordTrace_append hprefix tailTrace_1532916
  have hstable : (prefixWord ++ tailWord_1532916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532916).length < 2 ^ (prefixWord ++ tailWord_1532916).sum := by decide
  have hdescent : baseEnd_1532916 < baseStart_1532916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532930 : List Nat := [3, 4, 1, 3, 2, 1, 1, 1, 5]
def baseStart_1532930 : Nat := 118140960795 + 1532930 * 2 ^ 59
def prefixEnd_1532930 : Nat := 4983230072969 + 3 ^ 40 * 1532930 * 2
def baseEnd_1532930 : Nat := 349835510976352283566751

theorem tailTrace_1532930 : CollatzResearch.WordTrace tailWord_1532930 prefixEnd_1532930 349835510976352283566751 := by
  unfold tailWord_1532930
  simp only [CollatzResearch.WordTrace]
  refine ⟨13977637584115972111465061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37273700224309258963906829 13977637584115972111465061)
  ·
    refine ⟨2620807047021744770899699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13977637584115972111465061 2620807047021744770899699)
    ·
      refine ⟨3931210570532617156349549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2620807047021744770899699 3931210570532617156349549)
      ·
        refine ⟨1474203963949731433631081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3931210570532617156349549 1474203963949731433631081)
        ·
          refine ⟨1105652972962298575223311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1474203963949731433631081 1105652972962298575223311)
          ·
            refine ⟨1658479459443447862834967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1105652972962298575223311 1658479459443447862834967)
            ·
              refine ⟨2487719189165171794252451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1658479459443447862834967 2487719189165171794252451)
              ·
                refine ⟨3731578783747757691378677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2487719189165171794252451 3731578783747757691378677)
                ·
                  refine ⟨349835510976352283566751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3731578783747757691378677 349835510976352283566751)
                  ·
                    rfl

theorem cell21_1532930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_1532930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532930 prefixEnd_1532930 := by exact prefixLift 1532930
  have htrace : WordTrace (prefixWord ++ tailWord_1532930) baseStart_1532930 baseEnd_1532930 := by
    simpa [prefixWord, tailWord_1532930, baseEnd_1532930] using wordTrace_append hprefix tailTrace_1532930
  have hstable : (prefixWord ++ tailWord_1532930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532930).length < 2 ^ (prefixWord ++ tailWord_1532930).sum := by decide
  have hdescent : baseEnd_1532930 < baseStart_1532930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532989 : List Nat := [1, 4, 1, 3, 1, 4, 2, 2, 3]
def baseStart_1532989 : Nat := 118140960795 + 1532989 * 2 ^ 59
def prefixEnd_1532989 : Nat := 4983230072969 + 3 ^ 40 * 1532989 * 2
def baseEnd_1532989 : Nat := 349848975580181292083297

theorem tailTrace_1532989 : CollatzResearch.WordTrace tailWord_1532989 prefixEnd_1532989 349848975580181292083297 := by
  unfold tailWord_1532989
  simp only [CollatzResearch.WordTrace]
  refine ⟨55912702243250141522258021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37275134828833427681505347 55912702243250141522258021)
  ·
    refine ⟨10483631670609401535423379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55912702243250141522258021 10483631670609401535423379)
    ·
      refine ⟨15725447505914102303135069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10483631670609401535423379 15725447505914102303135069)
      ·
        refine ⟨5897042814717788363675651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15725447505914102303135069 5897042814717788363675651)
        ·
          refine ⟨8845564222076682545513477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5897042814717788363675651 8845564222076682545513477)
          ·
            refine ⟨1658543291639377977283777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8845564222076682545513477 1658543291639377977283777)
            ·
              refine ⟨1243907468729533482962833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1658543291639377977283777 1243907468729533482962833)
              ·
                refine ⟨932930601547150112222125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1243907468729533482962833 932930601547150112222125)
                ·
                  refine ⟨349848975580181292083297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 932930601547150112222125 349848975580181292083297)
                  ·
                    rfl

theorem cell21_1532989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_1532989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1532989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1532989 prefixEnd_1532989 := by exact prefixLift 1532989
  have htrace : WordTrace (prefixWord ++ tailWord_1532989) baseStart_1532989 baseEnd_1532989 := by
    simpa [prefixWord, tailWord_1532989, baseEnd_1532989] using wordTrace_append hprefix tailTrace_1532989
  have hstable : (prefixWord ++ tailWord_1532989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532989).length < 2 ^ (prefixWord ++ tailWord_1532989).sum := by decide
  have hdescent : baseEnd_1532989 < baseStart_1532989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533028 : List Nat := [2, 3, 1, 1, 2, 1, 1, 4, 6]
def baseStart_1533028 : Nat := 118140960795 + 1533028 * 2 ^ 59
def prefixEnd_1533028 : Nat := 4983230072969 + 3 ^ 40 * 1533028 * 2
def baseEnd_1533028 : Nat := 349857875911525890933217

theorem tailTrace_1533028 : CollatzResearch.WordTrace tailWord_1533028 prefixEnd_1533028 349857875911525890933217 := by
  unfold tailWord_1533028
  simp only [CollatzResearch.WordTrace]
  refine ⟨27957062345054425591463869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37276083126739234121951825 27957062345054425591463869)
  ·
    refine ⟨10483898379395409596798951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27957062345054425591463869 10483898379395409596798951)
    ·
      refine ⟨15725847569093114395198427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10483898379395409596798951 15725847569093114395198427)
      ·
        refine ⟨23588771353639671592797641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15725847569093114395198427 23588771353639671592797641)
        ·
          refine ⟨17691578515229753694598231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23588771353639671592797641 17691578515229753694598231)
          ·
            refine ⟨26537367772844630541897347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17691578515229753694598231 26537367772844630541897347)
            ·
              refine ⟨39806051659266945812846021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26537367772844630541897347 39806051659266945812846021)
              ·
                refine ⟨7463634686112552339908629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39806051659266945812846021 7463634686112552339908629)
                ·
                  refine ⟨349857875911525890933217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7463634686112552339908629 349857875911525890933217)
                  ·
                    rfl

theorem cell21_1533028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_1533028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1533028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1533028 prefixEnd_1533028 := by exact prefixLift 1533028
  have htrace : WordTrace (prefixWord ++ tailWord_1533028) baseStart_1533028 baseEnd_1533028 := by
    simpa [prefixWord, tailWord_1533028, baseEnd_1533028] using wordTrace_append hprefix tailTrace_1533028
  have hstable : (prefixWord ++ tailWord_1533028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533028).length < 2 ^ (prefixWord ++ tailWord_1533028).sum := by decide
  have hdescent : baseEnd_1533028 < baseStart_1533028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533031 : List Nat := [1, 1, 5, 1, 1, 3, 1, 5, 3]
def baseStart_1533031 : Nat := 118140960795 + 1533031 * 2 ^ 59
def prefixEnd_1533031 : Nat := 4983230072969 + 3 ^ 40 * 1533031 * 2
def baseEnd_1533031 : Nat := 349858560552398552383211

theorem tailTrace_1533031 : CollatzResearch.WordTrace tailWord_1533031 prefixEnd_1533031 349858560552398552383211 := by
  unfold tailWord_1533031
  simp only [CollatzResearch.WordTrace]
  refine ⟨55914234109097982695286947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37276156072731988463524631 55914234109097982695286947)
  ·
    refine ⟨83871351163646974042930421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55914234109097982695286947 83871351163646974042930421)
    ·
      refine ⟨7862939171591903816524727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83871351163646974042930421 7862939171591903816524727)
      ·
        refine ⟨11794408757387855724787091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7862939171591903816524727 11794408757387855724787091)
        ·
          refine ⟨17691613136081783587180637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11794408757387855724787091 17691613136081783587180637)
          ·
            refine ⟨6634354926030668845192739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17691613136081783587180637 6634354926030668845192739)
            ·
              refine ⟨9951532389046003267789109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6634354926030668845192739 9951532389046003267789109)
              ·
                refine ⟨932956161473062806355229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9951532389046003267789109 932956161473062806355229)
                ·
                  refine ⟨349858560552398552383211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 932956161473062806355229 349858560552398552383211)
                  ·
                    rfl

theorem cell21_1533031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5, 3].length) (baseStart_1533031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1533031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1533031 prefixEnd_1533031 := by exact prefixLift 1533031
  have htrace : WordTrace (prefixWord ++ tailWord_1533031) baseStart_1533031 baseEnd_1533031 := by
    simpa [prefixWord, tailWord_1533031, baseEnd_1533031] using wordTrace_append hprefix tailTrace_1533031
  have hstable : (prefixWord ++ tailWord_1533031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533031).length < 2 ^ (prefixWord ++ tailWord_1533031).sum := by decide
  have hdescent : baseEnd_1533031 < baseStart_1533031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533110 : List Nat := [5, 1, 3, 2, 1, 1, 2, 6]
def baseStart_1533110 : Nat := 118140960795 + 1533110 * 2 ^ 59
def prefixEnd_1533110 : Nat := 4983230072969 + 3 ^ 40 * 1533110 * 2
def baseEnd_1533110 : Nat := 116625529809570656855461

theorem tailTrace_1533110 : CollatzResearch.WordTrace tailWord_1533110 prefixEnd_1533110 116625529809570656855461 := by
  unfold tailWord_1533110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3494819717238236199213299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37278076983874519458275189 3494819717238236199213299)
  ·
    refine ⟨5242229575857354298819949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3494819717238236199213299 5242229575857354298819949)
    ·
      refine ⟨1965836090946507862057481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5242229575857354298819949 1965836090946507862057481)
      ·
        refine ⟨1474377068209880896543111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1965836090946507862057481 1474377068209880896543111)
        ·
          refine ⟨2211565602314821344814667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1474377068209880896543111 2211565602314821344814667)
          ·
            refine ⟨3317348403472232017222001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2211565602314821344814667 3317348403472232017222001)
            ·
              refine ⟨2488011302604174012916501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3317348403472232017222001 2488011302604174012916501)
              ·
                refine ⟨116625529809570656855461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2488011302604174012916501 116625529809570656855461)
                ·
                  rfl

theorem cell21_1533110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_1533110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1533110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1533110 prefixEnd_1533110 := by exact prefixLift 1533110
  have htrace : WordTrace (prefixWord ++ tailWord_1533110) baseStart_1533110 baseEnd_1533110 := by
    simpa [prefixWord, tailWord_1533110, baseEnd_1533110] using wordTrace_append hprefix tailTrace_1533110
  have hstable : (prefixWord ++ tailWord_1533110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533110).length < 2 ^ (prefixWord ++ tailWord_1533110).sum := by decide
  have hdescent : baseEnd_1533110 < baseStart_1533110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533290 : List Nat := [3, 1, 3, 3, 2, 1, 1, 3, 4]
def baseStart_1533290 : Nat := 118140960795 + 1533290 * 2 ^ 59
def prefixEnd_1533290 : Nat := 4983230072969 + 3 ^ 40 * 1533290 * 2
def baseEnd_1533290 : Nat := 349917667881071657566015

theorem tailTrace_1533290 : CollatzResearch.WordTrace tailWord_1533290 prefixEnd_1533290 349917667881071657566015 := by
  unfold tailWord_1533290
  simp only [CollatzResearch.WordTrace]
  refine ⟨13980920153789917482241331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37282453743439779952643549 13980920153789917482241331)
  ·
    refine ⟨20971380230684876223361997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13980920153789917482241331 20971380230684876223361997)
    ·
      refine ⟨7864267586506828583760749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20971380230684876223361997 7864267586506828583760749)
      ·
        refine ⟨2949100344940060718910281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7864267586506828583760749 2949100344940060718910281)
        ·
          refine ⟨2211825258705045539182711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2949100344940060718910281 2211825258705045539182711)
          ·
            refine ⟨3317737888057568308774067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2211825258705045539182711 3317737888057568308774067)
            ·
              refine ⟨4976606832086352463161101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3317737888057568308774067 4976606832086352463161101)
              ·
                refine ⟨1866227562032382173685413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4976606832086352463161101 1866227562032382173685413)
                ·
                  refine ⟨349917667881071657566015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1866227562032382173685413 349917667881071657566015)
                  ·
                    rfl

theorem cell21_1533290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_1533290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1533290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1533290 prefixEnd_1533290 := by exact prefixLift 1533290
  have htrace : WordTrace (prefixWord ++ tailWord_1533290) baseStart_1533290 baseEnd_1533290 := by
    simpa [prefixWord, tailWord_1533290, baseEnd_1533290] using wordTrace_append hprefix tailTrace_1533290
  have hstable : (prefixWord ++ tailWord_1533290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533290).length < 2 ^ (prefixWord ++ tailWord_1533290).sum := by decide
  have hdescent : baseEnd_1533290 < baseStart_1533290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533532 : List Nat := [2, 2, 4, 1, 2, 2, 3, 5]
def baseStart_1533532 : Nat := 118140960795 + 1533532 * 2 ^ 59
def prefixEnd_1533532 : Nat := 4983230072969 + 3 ^ 40 * 1533532 * 2
def baseEnd_1533532 : Nat := 116657631859377671510729

theorem tailTrace_1533532 : CollatzResearch.WordTrace tailWord_1533532 prefixEnd_1533532 116657631859377671510729 := by
  unfold tailWord_1533532
  simp only [CollatzResearch.WordTrace]
  refine ⟨27966253540141472629637425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37288338053521963506183233 27966253540141472629637425)
  ·
    refine ⟨20974690155106104472228069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27966253540141472629637425 20974690155106104472228069)
    ·
      refine ⟨3932754404082394588542763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20974690155106104472228069 3932754404082394588542763)
      ·
        refine ⟨5899131606123591882814145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3932754404082394588542763 5899131606123591882814145)
        ·
          refine ⟨4424348704592693912110609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5899131606123591882814145 4424348704592693912110609)
          ·
            refine ⟨3318261528444520434082957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4424348704592693912110609 3318261528444520434082957)
            ·
              refine ⟨1244348073166695162781109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3318261528444520434082957 1244348073166695162781109)
              ·
                refine ⟨116657631859377671510729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1244348073166695162781109 116657631859377671510729)
                ·
                  rfl

theorem cell21_1533532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 5].length) (baseStart_1533532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1533532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1533532 prefixEnd_1533532 := by exact prefixLift 1533532
  have htrace : WordTrace (prefixWord ++ tailWord_1533532) baseStart_1533532 baseEnd_1533532 := by
    simpa [prefixWord, tailWord_1533532, baseEnd_1533532] using wordTrace_append hprefix tailTrace_1533532
  have hstable : (prefixWord ++ tailWord_1533532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533532).length < 2 ^ (prefixWord ++ tailWord_1533532).sum := by decide
  have hdescent : baseEnd_1533532 < baseStart_1533532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533591 : List Nat := [1, 1, 3, 3, 2, 2, 4, 5]
def baseStart_1533591 : Nat := 118140960795 + 1533591 * 2 ^ 59
def prefixEnd_1533591 : Nat := 4983230072969 + 3 ^ 40 * 1533591 * 2
def baseEnd_1533591 : Nat := 116662120060654007682911

theorem tailTrace_1533591 : CollatzResearch.WordTrace tailWord_1533591 prefixEnd_1533591 116662120060654007682911 := by
  unfold tailWord_1533591
  simp only [CollatzResearch.WordTrace]
  refine ⟨55934658987069198335672627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37289772658046132223781751 55934658987069198335672627)
  ·
    refine ⟨83901988480603797503508941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55934658987069198335672627 83901988480603797503508941)
    ·
      refine ⟨31463245680226424063815853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83901988480603797503508941 31463245680226424063815853)
      ·
        refine ⟨11798717130084909023930945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31463245680226424063815853 11798717130084909023930945)
        ·
          refine ⟨8849037847563681767948209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11798717130084909023930945 8849037847563681767948209)
          ·
            refine ⟨6636778385672761325961157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8849037847563681767948209 6636778385672761325961157)
            ·
              refine ⟨1244395947313642748617717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6636778385672761325961157 1244395947313642748617717)
              ·
                refine ⟨116662120060654007682911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1244395947313642748617717 116662120060654007682911)
                ·
                  rfl

theorem cell21_1533591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 5].length) (baseStart_1533591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1533591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1533591 prefixEnd_1533591 := by exact prefixLift 1533591
  have htrace : WordTrace (prefixWord ++ tailWord_1533591) baseStart_1533591 baseEnd_1533591 := by
    simpa [prefixWord, tailWord_1533591, baseEnd_1533591] using wordTrace_append hprefix tailTrace_1533591
  have hstable : (prefixWord ++ tailWord_1533591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533591).length < 2 ^ (prefixWord ++ tailWord_1533591).sum := by decide
  have hdescent : baseEnd_1533591 < baseStart_1533591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533619 : List Nat := [1, 1, 1, 2, 3, 3, 1, 3, 6]
def baseStart_1533619 : Nat := 118140960795 + 1533619 * 2 ^ 59
def prefixEnd_1533619 : Nat := 4983230072969 + 3 ^ 40 * 1533619 * 2
def baseEnd_1533619 : Nat := 349992750163440196582009

theorem tailTrace_1533619 : CollatzResearch.WordTrace tailWord_1533619 prefixEnd_1533619 349992750163440196582009 := by
  unfold tailWord_1533619
  simp only [CollatzResearch.WordTrace]
  refine ⟨55935680230967759117691911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37290453487311839411794607 55935680230967759117691911)
  ·
    refine ⟨83903520346451638676537867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55935680230967759117691911 83903520346451638676537867)
    ·
      refine ⟨125855280519677458014806801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83903520346451638676537867 125855280519677458014806801)
      ·
        refine ⟨94391460389758093511105101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125855280519677458014806801 94391460389758093511105101)
        ·
          refine ⟨35396797646159285066664413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94391460389758093511105101 35396797646159285066664413)
          ·
            refine ⟨13273799117309731899999155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35396797646159285066664413 13273799117309731899999155)
            ·
              refine ⟨19910698675964597849998733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13273799117309731899999155 19910698675964597849998733)
              ·
                refine ⟨7466512003486724193749525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19910698675964597849998733 7466512003486724193749525)
                ·
                  refine ⟨349992750163440196582009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7466512003486724193749525 349992750163440196582009)
                  ·
                    rfl

theorem cell21_1533619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 6].length) (baseStart_1533619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1533619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1533619 prefixEnd_1533619 := by exact prefixLift 1533619
  have htrace : WordTrace (prefixWord ++ tailWord_1533619) baseStart_1533619 baseEnd_1533619 := by
    simpa [prefixWord, tailWord_1533619, baseEnd_1533619] using wordTrace_append hprefix tailTrace_1533619
  have hstable : (prefixWord ++ tailWord_1533619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533619).length < 2 ^ (prefixWord ++ tailWord_1533619).sum := by decide
  have hdescent : baseEnd_1533619 < baseStart_1533619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533667 : List Nat := [1, 1, 1, 7, 3, 8]
def baseStart_1533667 : Nat := 118140960795 + 1533667 * 2 ^ 59
def prefixEnd_1533667 : Nat := 4983230072969 + 3 ^ 40 * 1533667 * 2
def baseEnd_1533667 : Nat := 12963100163607510362293

theorem tailTrace_1533667 : CollatzResearch.WordTrace tailWord_1533667 prefixEnd_1533667 12963100163607510362293 := by
  unfold tailWord_1533667
  simp only [CollatzResearch.WordTrace]
  refine ⟨55937430934793863315439255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37291620623195908876959503 55937430934793863315439255)
  ·
    refine ⟨83906146402190794973158883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55937430934793863315439255 83906146402190794973158883)
    ·
      refine ⟨125859219603286192459738325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83906146402190794973158883 125859219603286192459738325)
      ·
        refine ⟨2949825459452020135775117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 125859219603286192459738325 2949825459452020135775117)
        ·
          refine ⟨1106184547294507550915669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2949825459452020135775117 1106184547294507550915669)
          ·
            refine ⟨12963100163607510362293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1106184547294507550915669 12963100163607510362293)
            ·
              rfl

theorem cell21_1533667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 8].length) (baseStart_1533667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1533667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1533667 prefixEnd_1533667 := by exact prefixLift 1533667
  have htrace : WordTrace (prefixWord ++ tailWord_1533667) baseStart_1533667 baseEnd_1533667 := by
    simpa [prefixWord, tailWord_1533667, baseEnd_1533667] using wordTrace_append hprefix tailTrace_1533667
  have hstable : (prefixWord ++ tailWord_1533667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533667).length < 2 ^ (prefixWord ++ tailWord_1533667).sum := by decide
  have hdescent : baseEnd_1533667 < baseStart_1533667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533698 : List Nat := [3, 4, 1, 1, 1, 1, 3, 2, 5]
def baseStart_1533698 : Nat := 118140960795 + 1533698 * 2 ^ 59
def prefixEnd_1533698 : Nat := 4983230072969 + 3 ^ 40 * 1533698 * 2
def baseEnd_1533698 : Nat := 350010779039753614765181

theorem tailTrace_1533698 : CollatzResearch.WordTrace tailWord_1533698 prefixEnd_1533698 350010779039753614765181 := by
  unfold tailWord_1533698
  simp only [CollatzResearch.WordTrace]
  refine ⟨13984640399420388902454437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37292374398454370406545165 13984640399420388902454437)
  ·
    refine ⟨2622120074891322919210207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13984640399420388902454437 2622120074891322919210207)
    ·
      refine ⟨3933180112336984378815311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2622120074891322919210207 3933180112336984378815311)
      ·
        refine ⟨5899770168505476568222967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3933180112336984378815311 5899770168505476568222967)
        ·
          refine ⟨8849655252758214852334451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5899770168505476568222967 8849655252758214852334451)
          ·
            refine ⟨13274482879137322278501677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8849655252758214852334451 13274482879137322278501677)
            ·
              refine ⟨4977931079676495854438129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13274482879137322278501677 4977931079676495854438129)
              ·
                refine ⟨3733448309757371890828597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4977931079676495854438129 3733448309757371890828597)
                ·
                  refine ⟨350010779039753614765181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3733448309757371890828597 350010779039753614765181)
                  ·
                    rfl

theorem cell21_1533698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_1533698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1533698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1533698 prefixEnd_1533698 := by exact prefixLift 1533698
  have htrace : WordTrace (prefixWord ++ tailWord_1533698) baseStart_1533698 baseEnd_1533698 := by
    simpa [prefixWord, tailWord_1533698, baseEnd_1533698] using wordTrace_append hprefix tailTrace_1533698
  have hstable : (prefixWord ++ tailWord_1533698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533698).length < 2 ^ (prefixWord ++ tailWord_1533698).sum := by decide
  have hdescent : baseEnd_1533698 < baseStart_1533698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533729 : List Nat := [1, 2, 3, 2, 1, 5, 1, 2, 4]
def baseStart_1533729 : Nat := 118140960795 + 1533729 * 2 ^ 59
def prefixEnd_1533729 : Nat := 4983230072969 + 3 ^ 40 * 1533729 * 2
def baseEnd_1533729 : Nat := 350017853662104449748451

theorem tailTrace_1533729 : CollatzResearch.WordTrace tailWord_1533729 prefixEnd_1533729 350017853662104449748451 := by
  unfold tailWord_1533729
  simp only [CollatzResearch.WordTrace]
  refine ⟨55939692260569247904196241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37293128173712831936130827 55939692260569247904196241)
  ·
    refine ⟨41954769195426935928147181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55939692260569247904196241 41954769195426935928147181)
    ·
      refine ⟨15733038448285100973055193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41954769195426935928147181 15733038448285100973055193)
      ·
        refine ⟨11799778836213825729791395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15733038448285100973055193 11799778836213825729791395)
        ·
          refine ⟨17699668254320738594687093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11799778836213825729791395 17699668254320738594687093)
          ·
            refine ⟨1659343898842569243251915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17699668254320738594687093 1659343898842569243251915)
            ·
              refine ⟨2489015848263853864877873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1659343898842569243251915 2489015848263853864877873)
              ·
                refine ⟨1866761886197890398658405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2489015848263853864877873 1866761886197890398658405)
                ·
                  refine ⟨350017853662104449748451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1866761886197890398658405 350017853662104449748451)
                  ·
                    rfl

theorem cell21_1533729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 4].length) (baseStart_1533729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1533729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1533729 prefixEnd_1533729 := by exact prefixLift 1533729
  have htrace : WordTrace (prefixWord ++ tailWord_1533729) baseStart_1533729 baseEnd_1533729 := by
    simpa [prefixWord, tailWord_1533729, baseEnd_1533729] using wordTrace_append hprefix tailTrace_1533729
  have hstable : (prefixWord ++ tailWord_1533729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533729).length < 2 ^ (prefixWord ++ tailWord_1533729).sum := by decide
  have hdescent : baseEnd_1533729 < baseStart_1533729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533791 : List Nat := [1, 1, 2, 3, 1, 5, 3, 2, 3]
def baseStart_1533791 : Nat := 118140960795 + 1533791 * 2 ^ 59
def prefixEnd_1533791 : Nat := 4983230072969 + 3 ^ 40 * 1533791 * 2
def baseEnd_1533791 : Nat := 350032002906806119714991

theorem tailTrace_1533791 : CollatzResearch.WordTrace tailWord_1533791 prefixEnd_1533791 350032002906806119714991 := by
  unfold tailWord_1533791
  simp only [CollatzResearch.WordTrace]
  refine ⟨55941953586344632492953227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37294635724229754995302151 55941953586344632492953227)
  ·
    refine ⟨83912930379516948739429841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55941953586344632492953227 83912930379516948739429841)
    ·
      refine ⟨62934697784637711554572381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83912930379516948739429841 62934697784637711554572381)
      ·
        refine ⟨23600511669239141832964643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62934697784637711554572381 23600511669239141832964643)
        ·
          refine ⟨35400767503858712749446965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23600511669239141832964643 35400767503858712749446965)
          ·
            refine ⟨3318821953486754320260653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35400767503858712749446965 3318821953486754320260653)
            ·
              refine ⟨1244558232557532870097745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3318821953486754320260653 1244558232557532870097745)
              ·
                refine ⟨933418674418149652573309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1244558232557532870097745 933418674418149652573309)
                ·
                  refine ⟨350032002906806119714991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 933418674418149652573309 350032002906806119714991)
                  ·
                    rfl

theorem cell21_1533791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2, 3].length) (baseStart_1533791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1533791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1533791 prefixEnd_1533791 := by exact prefixLift 1533791
  have htrace : WordTrace (prefixWord ++ tailWord_1533791) baseStart_1533791 baseEnd_1533791 := by
    simpa [prefixWord, tailWord_1533791, baseEnd_1533791] using wordTrace_append hprefix tailTrace_1533791
  have hstable : (prefixWord ++ tailWord_1533791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533791).length < 2 ^ (prefixWord ++ tailWord_1533791).sum := by decide
  have hdescent : baseEnd_1533791 < baseStart_1533791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533805 : List Nat := [1, 5, 1, 1, 1, 1, 6, 1, 4]
def baseStart_1533805 : Nat := 118140960795 + 1533805 * 2 ^ 59
def prefixEnd_1533805 : Nat := 4983230072969 + 3 ^ 40 * 1533805 * 2
def baseEnd_1533805 : Nat := 350035197897545206481629

theorem tailTrace_1533805 : CollatzResearch.WordTrace tailWord_1533805 prefixEnd_1533805 350035197897545206481629 := by
  unfold tailWord_1533805
  simp only [CollatzResearch.WordTrace]
  refine ⟨55942464208293912883962869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37294976138862608589308579 55942464208293912883962869)
  ·
    refine ⟨5244606019527554332871519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55942464208293912883962869 5244606019527554332871519)
    ·
      refine ⟨7866909029291331499307279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5244606019527554332871519 7866909029291331499307279)
      ·
        refine ⟨11800363543936997248960919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7866909029291331499307279 11800363543936997248960919)
        ·
          refine ⟨17700545315905495873441379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11800363543936997248960919 17700545315905495873441379)
          ·
            refine ⟨26550817973858243810162069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17700545315905495873441379 26550817973858243810162069)
            ·
              refine ⟨1244569592524605178601347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26550817973858243810162069 1244569592524605178601347)
              ·
                refine ⟨1866854388786907767902021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1244569592524605178601347 1866854388786907767902021)
                ·
                  refine ⟨350035197897545206481629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1866854388786907767902021 350035197897545206481629)
                  ·
                    rfl

theorem cell21_1533805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_1533805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1533805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1533805 prefixEnd_1533805 := by exact prefixLift 1533805
  have htrace : WordTrace (prefixWord ++ tailWord_1533805) baseStart_1533805 baseEnd_1533805 := by
    simpa [prefixWord, tailWord_1533805, baseEnd_1533805] using wordTrace_append hprefix tailTrace_1533805
  have hstable : (prefixWord ++ tailWord_1533805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533805).length < 2 ^ (prefixWord ++ tailWord_1533805).sum := by decide
  have hdescent : baseEnd_1533805 < baseStart_1533805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533870 : List Nat := [4, 1, 5, 1, 1, 1, 3, 5]
def baseStart_1533870 : Nat := 118140960795 + 1533870 * 2 ^ 59
def prefixEnd_1533870 : Nat := 4983230072969 + 3 ^ 40 * 1533870 * 2
def baseEnd_1533870 : Nat := 116683343927706512632721

theorem tailTrace_1533870 : CollatzResearch.WordTrace tailWord_1533870 prefixEnd_1533870 116683343927706512632721 := by
  unfold tailWord_1533870
  simp only [CollatzResearch.WordTrace]
  refine ⟨6993104369132303623134883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37296556635372285990052709 6993104369132303623134883)
  ·
    refine ⟨10489656553698455434702325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6993104369132303623134883 10489656553698455434702325)
    ·
      refine ⟨983405301909230197003343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10489656553698455434702325 983405301909230197003343)
      ·
        refine ⟨1475107952863845295505015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 983405301909230197003343 1475107952863845295505015)
        ·
          refine ⟨2212661929295767943257523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1475107952863845295505015 2212661929295767943257523)
          ·
            refine ⟨3318992893943651914886285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2212661929295767943257523 3318992893943651914886285)
            ·
              refine ⟨1244622335228869468082357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3318992893943651914886285 1244622335228869468082357)
              ·
                refine ⟨116683343927706512632721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1244622335228869468082357 116683343927706512632721)
                ·
                  rfl

theorem cell21_1533870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_1533870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1533870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1533870 prefixEnd_1533870 := by exact prefixLift 1533870
  have htrace : WordTrace (prefixWord ++ tailWord_1533870) baseStart_1533870 baseEnd_1533870 := by
    simpa [prefixWord, tailWord_1533870, baseEnd_1533870] using wordTrace_append hprefix tailTrace_1533870
  have hstable : (prefixWord ++ tailWord_1533870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533870).length < 2 ^ (prefixWord ++ tailWord_1533870).sum := by decide
  have hdescent : baseEnd_1533870 < baseStart_1533870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533884 : List Nat := [2, 2, 2, 5, 1, 1, 2, 3, 3]
def baseStart_1533884 : Nat := 118140960795 + 1533884 * 2 ^ 59
def prefixEnd_1533884 : Nat := 4983230072969 + 3 ^ 40 * 1533884 * 2
def baseEnd_1533884 : Nat := 350053226773858624664801

theorem tailTrace_1533884 : CollatzResearch.WordTrace tailWord_1533884 prefixEnd_1533884 350053226773858624664801 := by
  unfold tailWord_1533884
  simp only [CollatzResearch.WordTrace]
  refine ⟨27972672787503854688044353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37296897050005139584059137 27972672787503854688044353)
  ·
    refine ⟨20979504590627891016033265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27972672787503854688044353 20979504590627891016033265)
    ·
      refine ⟨15734628442970918262024949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20979504590627891016033265 15734628442970918262024949)
      ·
        refine ⟨1475121416528523587064839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15734628442970918262024949 1475121416528523587064839)
        ·
          refine ⟨2212682124792785380597259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1475121416528523587064839 2212682124792785380597259)
          ·
            refine ⟨3319023187189178070895889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2212682124792785380597259 3319023187189178070895889)
            ·
              refine ⟨2489267390391883553171917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3319023187189178070895889 2489267390391883553171917)
              ·
                refine ⟨933475271396956332439469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2489267390391883553171917 933475271396956332439469)
                ·
                  refine ⟨350053226773858624664801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 933475271396956332439469 350053226773858624664801)
                  ·
                    rfl

theorem cell21_1533884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3, 3].length) (baseStart_1533884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1533884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1533884 prefixEnd_1533884 := by exact prefixLift 1533884
  have htrace : WordTrace (prefixWord ++ tailWord_1533884) baseStart_1533884 baseEnd_1533884 := by
    simpa [prefixWord, tailWord_1533884, baseEnd_1533884] using wordTrace_append hprefix tailTrace_1533884
  have hstable : (prefixWord ++ tailWord_1533884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533884).length < 2 ^ (prefixWord ++ tailWord_1533884).sum := by decide
  have hdescent : baseEnd_1533884 < baseStart_1533884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533909 : List Nat := [1, 3, 2, 3, 2, 1, 1, 3, 5]
def baseStart_1533909 : Nat := 118140960795 + 1533909 * 2 ^ 59
def prefixEnd_1533909 : Nat := 4983230072969 + 3 ^ 40 * 1533909 * 2
def baseEnd_1533909 : Nat := 350058932114464136748083

theorem tailTrace_1533909 : CollatzResearch.WordTrace tailWord_1533909 prefixEnd_1533909 350058932114464136748083 := by
  unfold tailWord_1533909
  simp only [CollatzResearch.WordTrace]
  refine ⟨55946257399917138645748781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37297504933278092430499187 55946257399917138645748781)
  ·
    refine ⟨20979846524968926992155793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55946257399917138645748781 20979846524968926992155793)
    ·
      refine ⟨15734884893726695244116845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20979846524968926992155793 15734884893726695244116845)
      ·
        refine ⟨5900581835147510716543817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15734884893726695244116845 5900581835147510716543817)
        ·
          refine ⟨4425436376360633037407863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5900581835147510716543817 4425436376360633037407863)
          ·
            refine ⟨6638154564540949556111795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4425436376360633037407863 6638154564540949556111795)
            ·
              refine ⟨9957231846811424334167693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6638154564540949556111795 9957231846811424334167693)
              ·
                refine ⟨3733961942554284125312885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9957231846811424334167693 3733961942554284125312885)
                ·
                  refine ⟨350058932114464136748083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3733961942554284125312885 350058932114464136748083)
                  ·
                    rfl

theorem cell21_1533909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_1533909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1533909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1533909 prefixEnd_1533909 := by exact prefixLift 1533909
  have htrace : WordTrace (prefixWord ++ tailWord_1533909) baseStart_1533909 baseEnd_1533909 := by
    simpa [prefixWord, tailWord_1533909, baseEnd_1533909] using wordTrace_append hprefix tailTrace_1533909
  have hstable : (prefixWord ++ tailWord_1533909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533909).length < 2 ^ (prefixWord ++ tailWord_1533909).sum := by decide
  have hdescent : baseEnd_1533909 < baseStart_1533909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534016 : List Nat := [2, 1, 1, 2, 2, 5, 2, 2, 4]
def baseStart_1534016 : Nat := 118140960795 + 1534016 * 2 ^ 59
def prefixEnd_1534016 : Nat := 4983230072969 + 3 ^ 40 * 1534016 * 2
def baseEnd_1534016 : Nat := 350083350972255728464531

theorem tailTrace_1534016 : CollatzResearch.WordTrace tailWord_1534016 prefixEnd_1534016 350083350972255728464531 := by
  unfold tailWord_1534016
  simp only [CollatzResearch.WordTrace]
  refine ⟨27975080005264747959946951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37300106673686330613262601 27975080005264747959946951)
  ·
    refine ⟨41962620007897121939920427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27975080005264747959946951 41962620007897121939920427)
    ·
      refine ⟨62943930011845682909880641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41962620007897121939920427 62943930011845682909880641)
      ·
        refine ⟨47207947508884262182410481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62943930011845682909880641 47207947508884262182410481)
        ·
          refine ⟨35405960631663196636807861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47207947508884262182410481 35405960631663196636807861)
          ·
            refine ⟨3319308809218424684700737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35405960631663196636807861 3319308809218424684700737)
            ·
              refine ⟨2489481606913818513525553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3319308809218424684700737 2489481606913818513525553)
              ·
                refine ⟨1867111205185363885144165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2489481606913818513525553 1867111205185363885144165)
                ·
                  refine ⟨350083350972255728464531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1867111205185363885144165 350083350972255728464531)
                  ·
                    rfl

theorem cell21_1534016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 4].length) (baseStart_1534016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1534016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1534016 prefixEnd_1534016 := by exact prefixLift 1534016
  have htrace : WordTrace (prefixWord ++ tailWord_1534016) baseStart_1534016 baseEnd_1534016 := by
    simpa [prefixWord, tailWord_1534016, baseEnd_1534016] using wordTrace_append hprefix tailTrace_1534016
  have hstable : (prefixWord ++ tailWord_1534016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534016).length < 2 ^ (prefixWord ++ tailWord_1534016).sum := by decide
  have hdescent : baseEnd_1534016 < baseStart_1534016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534030 : List Nat := [4, 1, 1, 1, 1, 4, 3, 6]
def baseStart_1534030 : Nat := 118140960795 + 1534030 * 2 ^ 59
def prefixEnd_1534030 : Nat := 4983230072969 + 3 ^ 40 * 1534030 * 2
def baseEnd_1534030 : Nat := 116695515320998271743723

theorem tailTrace_1534030 : CollatzResearch.WordTrace tailWord_1534030 prefixEnd_1534030 116695515320998271743723 := by
  unfold tailWord_1534030
  simp only [CollatzResearch.WordTrace]
  refine ⟨6993833829059847038862943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37300447088319184207269029 6993833829059847038862943)
  ·
    refine ⟨10490750743589770558294415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6993833829059847038862943 10490750743589770558294415)
    ·
      refine ⟨15736126115384655837441623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10490750743589770558294415 15736126115384655837441623)
      ·
        refine ⟨23604189173076983756162435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15736126115384655837441623 23604189173076983756162435)
        ·
          refine ⟨35406283759615475634243653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23604189173076983756162435 35406283759615475634243653)
          ·
            refine ⟨6638678204927901681420685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35406283759615475634243653 6638678204927901681420685)
            ·
              refine ⟨2489504326847963130532757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6638678204927901681420685 2489504326847963130532757)
              ·
                refine ⟨116695515320998271743723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2489504326847963130532757 116695515320998271743723)
                ·
                  rfl

theorem cell21_1534030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_1534030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1534030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1534030 prefixEnd_1534030 := by exact prefixLift 1534030
  have htrace : WordTrace (prefixWord ++ tailWord_1534030) baseStart_1534030 baseEnd_1534030 := by
    simpa [prefixWord, tailWord_1534030, baseEnd_1534030] using wordTrace_append hprefix tailTrace_1534030
  have hstable : (prefixWord ++ tailWord_1534030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534030).length < 2 ^ (prefixWord ++ tailWord_1534030).sum := by decide
  have hdescent : baseEnd_1534030 < baseStart_1534030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534089 : List Nat := [1, 2, 1, 1, 4, 2, 2, 8]
def baseStart_1534089 : Nat := 118140960795 + 1534089 * 2 ^ 59
def prefixEnd_1534089 : Nat := 4983230072969 + 3 ^ 40 * 1534089 * 2
def baseEnd_1534089 : Nat := 116700003522274607915905

theorem tailTrace_1534089 : CollatzResearch.WordTrace tailWord_1534089 prefixEnd_1534089 116700003522274607915905 := by
  unfold tailWord_1534089
  simp only [CollatzResearch.WordTrace]
  refine ⟨55952822539265029387301321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37301881692843352924867547 55952822539265029387301321)
  ·
    refine ⟨41964616904448772040475991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55952822539265029387301321 41964616904448772040475991)
    ·
      refine ⟨62946925356673158060713987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41964616904448772040475991 62946925356673158060713987)
      ·
        refine ⟨94420388035009737091070981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62946925356673158060713987 94420388035009737091070981)
        ·
          refine ⟨17703822756564325704575809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94420388035009737091070981 17703822756564325704575809)
          ·
            refine ⟨13277867067423244278431857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17703822756564325704575809 13277867067423244278431857)
            ·
              refine ⟨9958400300567433208823893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13277867067423244278431857 9958400300567433208823893)
              ·
                refine ⟨116700003522274607915905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9958400300567433208823893 116700003522274607915905)
                ·
                  rfl

theorem cell21_1534089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 8].length) (baseStart_1534089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1534089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1534089 prefixEnd_1534089 := by exact prefixLift 1534089
  have htrace : WordTrace (prefixWord ++ tailWord_1534089) baseStart_1534089 baseEnd_1534089 := by
    simpa [prefixWord, tailWord_1534089, baseEnd_1534089] using wordTrace_append hprefix tailTrace_1534089
  have hstable : (prefixWord ++ tailWord_1534089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534089).length < 2 ^ (prefixWord ++ tailWord_1534089).sum := by decide
  have hdescent : baseEnd_1534089 < baseStart_1534089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534244 : List Nat := [2, 3, 1, 3, 1, 2, 3, 2, 4]
def baseStart_1534244 : Nat := 118140960795 + 1534244 * 2 ^ 59
def prefixEnd_1534244 : Nat := 4983230072969 + 3 ^ 40 * 1534244 * 2
def baseEnd_1534244 : Nat := 350135383678577998664065

theorem tailTrace_1534244 : CollatzResearch.WordTrace tailWord_1534244 prefixEnd_1534244 350135383678577998664065 := by
  unfold tailWord_1534244
  simp only [CollatzResearch.WordTrace]
  refine ⟨27979237926851745429596893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37305650569135660572795857 27979237926851745429596893)
  ·
    refine ⟨10492214222569404536098835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27979237926851745429596893 10492214222569404536098835)
    ·
      refine ⟨15738321333854106804148253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10492214222569404536098835 15738321333854106804148253)
      ·
        refine ⟨5901870500195290051555595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15738321333854106804148253 5901870500195290051555595)
        ·
          refine ⟨8852805750292935077333393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5901870500195290051555595 8852805750292935077333393)
          ·
            refine ⟨6639604312719701308000045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8852805750292935077333393 6639604312719701308000045)
            ·
              refine ⟨2489851617269887990500017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6639604312719701308000045 2489851617269887990500017)
              ·
                refine ⟨1867388712952415992875013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2489851617269887990500017 1867388712952415992875013)
                ·
                  refine ⟨350135383678577998664065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1867388712952415992875013 350135383678577998664065)
                  ·
                    rfl

theorem cell21_1534244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_1534244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1534244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1534244 prefixEnd_1534244 := by exact prefixLift 1534244
  have htrace : WordTrace (prefixWord ++ tailWord_1534244) baseStart_1534244 baseEnd_1534244 := by
    simpa [prefixWord, tailWord_1534244, baseEnd_1534244] using wordTrace_append hprefix tailTrace_1534244
  have hstable : (prefixWord ++ tailWord_1534244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534244).length < 2 ^ (prefixWord ++ tailWord_1534244).sum := by decide
  have hdescent : baseEnd_1534244 < baseStart_1534244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534306 : List Nat := [3, 3, 2, 1, 1, 4, 1, 1, 5]
def baseStart_1534306 : Nat := 118140960795 + 1534306 * 2 ^ 59
def prefixEnd_1534306 : Nat := 4983230072969 + 3 ^ 40 * 1534306 * 2
def baseEnd_1534306 : Nat := 350149532923279668630605

theorem tailTrace_1534306 : CollatzResearch.WordTrace tailWord_1534306 prefixEnd_1534306 350149532923279668630605 := by
  unfold tailWord_1534306
  simp only [CollatzResearch.WordTrace]
  refine ⟨13990184294869718861987693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37307158119652583631967181 13990184294869718861987693)
  ·
    refine ⟨5246319110576144573245385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13990184294869718861987693 5246319110576144573245385)
    ·
      refine ⟨3934739332932108429934039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5246319110576144573245385 3934739332932108429934039)
      ·
        refine ⟨5902108999398162644901059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3934739332932108429934039 5902108999398162644901059)
        ·
          refine ⟨8853163499097243967351589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5902108999398162644901059 8853163499097243967351589)
          ·
            refine ⟨1659968156080733243878423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8853163499097243967351589 1659968156080733243878423)
            ·
              refine ⟨2489952234121099865817635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1659968156080733243878423 2489952234121099865817635)
              ·
                refine ⟨3734928351181649798726453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2489952234121099865817635 3734928351181649798726453)
                ·
                  refine ⟨350149532923279668630605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3734928351181649798726453 350149532923279668630605)
                  ·
                    rfl

theorem cell21_1534306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_1534306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1534306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1534306 prefixEnd_1534306 := by exact prefixLift 1534306
  have htrace : WordTrace (prefixWord ++ tailWord_1534306) baseStart_1534306 baseEnd_1534306 := by
    simpa [prefixWord, tailWord_1534306, baseEnd_1534306] using wordTrace_append hprefix tailTrace_1534306
  have hstable : (prefixWord ++ tailWord_1534306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534306).length < 2 ^ (prefixWord ++ tailWord_1534306).sum := by decide
  have hdescent : baseEnd_1534306 < baseStart_1534306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534320 : List Nat := [2, 1, 1, 1, 4, 3, 4, 1, 4]
def baseStart_1534320 : Nat := 118140960795 + 1534320 * 2 ^ 59
def prefixEnd_1534320 : Nat := 4983230072969 + 3 ^ 40 * 1534320 * 2
def baseEnd_1534320 : Nat := 350152727914018755397243

theorem tailTrace_1534320 : CollatzResearch.WordTrace tailWord_1534320 prefixEnd_1534320 350152727914018755397243 := by
  unfold tailWord_1534320
  simp only [CollatzResearch.WordTrace]
  refine ⟨27980623900714077919480207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37307498534285437225973609 27980623900714077919480207)
  ·
    refine ⟨41970935851071116879220311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27980623900714077919480207 41970935851071116879220311)
    ·
      refine ⟨62956403776606675318830467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41970935851071116879220311 62956403776606675318830467)
      ·
        refine ⟨94434605664910012978245701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62956403776606675318830467 94434605664910012978245701)
        ·
          refine ⟨17706488562170627433421069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94434605664910012978245701 17706488562170627433421069)
          ·
            refine ⟨6639933210813985287532901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17706488562170627433421069 6639933210813985287532901)
            ·
              refine ⟨1244987477027622241412419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6639933210813985287532901 1244987477027622241412419)
              ·
                refine ⟨1867481215541433362118629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1244987477027622241412419 1867481215541433362118629)
                ·
                  refine ⟨350152727914018755397243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1867481215541433362118629 350152727914018755397243)
                  ·
                    rfl

theorem cell21_1534320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 4].length) (baseStart_1534320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1534320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1534320 prefixEnd_1534320 := by exact prefixLift 1534320
  have htrace : WordTrace (prefixWord ++ tailWord_1534320) baseStart_1534320 baseEnd_1534320 := by
    simpa [prefixWord, tailWord_1534320, baseEnd_1534320] using wordTrace_append hprefix tailTrace_1534320
  have hstable : (prefixWord ++ tailWord_1534320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534320).length < 2 ^ (prefixWord ++ tailWord_1534320).sum := by decide
  have hdescent : baseEnd_1534320 < baseStart_1534320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534514 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 8]
def baseStart_1534514 : Nat := 118140960795 + 1534514 * 2 ^ 59
def prefixEnd_1534514 : Nat := 4983230072969 + 3 ^ 40 * 1534514 * 2
def baseEnd_1534514 : Nat := 350197001357117529163513

theorem tailTrace_1534514 : CollatzResearch.WordTrace tailWord_1534514 prefixEnd_1534514 350197001357117529163513 := by
  unfold tailWord_1534514
  simp only [CollatzResearch.WordTrace]
  refine ⟨13992080890681331742880649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37312215708483551314348397 13992080890681331742880649)
  ·
    refine ⟨10494060668010998807160487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13992080890681331742880649 10494060668010998807160487)
    ·
      refine ⟨15741091002016498210740731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10494060668010998807160487 15741091002016498210740731)
      ·
        refine ⟨23611636503024747316111097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15741091002016498210740731 23611636503024747316111097)
        ·
          refine ⟨17708727377268560487083323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23611636503024747316111097 17708727377268560487083323)
          ·
            refine ⟨26563091065902840730624985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17708727377268560487083323 26563091065902840730624985)
            ·
              refine ⟨19922318299427130547968739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26563091065902840730624985 19922318299427130547968739)
              ·
                refine ⟨29883477449140695821953109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19922318299427130547968739 29883477449140695821953109)
                ·
                  refine ⟨350197001357117529163513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29883477449140695821953109 350197001357117529163513)
                  ·
                    rfl

theorem cell21_1534514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_1534514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1534514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1534514 prefixEnd_1534514 := by exact prefixLift 1534514
  have htrace : WordTrace (prefixWord ++ tailWord_1534514) baseStart_1534514 baseEnd_1534514 := by
    simpa [prefixWord, tailWord_1534514, baseEnd_1534514] using wordTrace_append hprefix tailTrace_1534514
  have hstable : (prefixWord ++ tailWord_1534514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534514).length < 2 ^ (prefixWord ++ tailWord_1534514).sum := by decide
  have hdescent : baseEnd_1534514 < baseStart_1534514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534517 : List Nat := [1, 3, 3, 1, 1, 2, 2, 5, 3]
def baseStart_1534517 : Nat := 118140960795 + 1534517 * 2 ^ 59
def prefixEnd_1534517 : Nat := 4983230072969 + 3 ^ 40 * 1534517 * 2
def baseEnd_1534517 : Nat := 350197685997990190613507

theorem tailTrace_1534517 : CollatzResearch.WordTrace tailWord_1534517 prefixEnd_1534517 350197685997990190613507 := by
  unfold tailWord_1534517
  simp only [CollatzResearch.WordTrace]
  refine ⟨55968432981714458483881805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37312288654476305655921203 55968432981714458483881805)
  ·
    refine ⟨20988162368142921931455677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55968432981714458483881805 20988162368142921931455677)
    ·
      refine ⟨7870560888053595724295879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20988162368142921931455677 7870560888053595724295879)
      ·
        refine ⟨11805841332080393586443819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7870560888053595724295879 11805841332080393586443819)
        ·
          refine ⟨17708761998120590379665729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11805841332080393586443819 17708761998120590379665729)
          ·
            refine ⟨13281571498590442784749297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17708761998120590379665729 13281571498590442784749297)
            ·
              refine ⟨9961178623942832088561973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13281571498590442784749297 9961178623942832088561973)
              ·
                refine ⟨933860495994640508302685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9961178623942832088561973 933860495994640508302685)
                ·
                  refine ⟨350197685997990190613507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 933860495994640508302685 350197685997990190613507)
                  ·
                    rfl

theorem cell21_1534517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5, 3].length) (baseStart_1534517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1534517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1534517 prefixEnd_1534517 := by exact prefixLift 1534517
  have htrace : WordTrace (prefixWord ++ tailWord_1534517) baseStart_1534517 baseEnd_1534517 := by
    simpa [prefixWord, tailWord_1534517, baseEnd_1534517] using wordTrace_append hprefix tailTrace_1534517
  have hstable : (prefixWord ++ tailWord_1534517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534517).length < 2 ^ (prefixWord ++ tailWord_1534517).sum := by decide
  have hdescent : baseEnd_1534517 < baseStart_1534517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534545 : List Nat := [1, 2, 2, 1, 3, 3, 3, 6]
def baseStart_1534545 : Nat := 118140960795 + 1534545 * 2 ^ 59
def prefixEnd_1534545 : Nat := 4983230072969 + 3 ^ 40 * 1534545 * 2
def baseEnd_1534545 : Nat := 116734691993156121382261

theorem tailTrace_1534545 : CollatzResearch.WordTrace tailWord_1534545 prefixEnd_1534545 116734691993156121382261 := by
  unfold tailWord_1534545
  simp only [CollatzResearch.WordTrace]
  refine ⟨55969454225613019265901089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37312969483742012843934059 55969454225613019265901089)
  ·
    refine ⟨41977090669209764449425817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55969454225613019265901089 41977090669209764449425817)
    ·
      refine ⟨31482818001907323337069363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41977090669209764449425817 31482818001907323337069363)
      ·
        refine ⟨47224227002860985005604045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31482818001907323337069363 47224227002860985005604045)
        ·
          refine ⟨17709085126072869377101517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47224227002860985005604045 17709085126072869377101517)
          ·
            refine ⟨6640906922277326016413069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17709085126072869377101517 6640906922277326016413069)
            ·
              refine ⟨2490340095853997256154901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6640906922277326016413069 2490340095853997256154901)
              ·
                refine ⟨116734691993156121382261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2490340095853997256154901 116734691993156121382261)
                ·
                  rfl

theorem cell21_1534545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 6].length) (baseStart_1534545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1534545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1534545 prefixEnd_1534545 := by exact prefixLift 1534545
  have htrace : WordTrace (prefixWord ++ tailWord_1534545) baseStart_1534545 baseEnd_1534545 := by
    simpa [prefixWord, tailWord_1534545, baseEnd_1534545] using wordTrace_append hprefix tailTrace_1534545
  have hstable : (prefixWord ++ tailWord_1534545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534545).length < 2 ^ (prefixWord ++ tailWord_1534545).sum := by decide
  have hdescent : baseEnd_1534545 < baseStart_1534545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534582 : List Nat := [5, 1, 1, 2, 4, 1, 1, 2, 4]
def baseStart_1534582 : Nat := 118140960795 + 1534582 * 2 ^ 59
def prefixEnd_1534582 : Nat := 4983230072969 + 3 ^ 40 * 1534582 * 2
def baseEnd_1534582 : Nat := 350212519883564522030041

theorem tailTrace_1534582 : CollatzResearch.WordTrace tailWord_1534582 prefixEnd_1534582 350212519883564522030041 := by
  unfold tailWord_1534582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3498175232904935911562375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37313869150985983056665333 3498175232904935911562375)
  ·
    refine ⟨5247262849357403867343563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3498175232904935911562375 5247262849357403867343563)
    ·
      refine ⟨7870894274036105801015345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5247262849357403867343563 7870894274036105801015345)
      ·
        refine ⟨5903170705527079350761509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7870894274036105801015345 5903170705527079350761509)
        ·
          refine ⟨1106844507286327378267783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5903170705527079350761509 1106844507286327378267783)
          ·
            refine ⟨1660266760929491067401675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1106844507286327378267783 1660266760929491067401675)
            ·
              refine ⟨2490400141394236601102513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1660266760929491067401675 2490400141394236601102513)
              ·
                refine ⟨1867800106045677450826885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2490400141394236601102513 1867800106045677450826885)
                ·
                  refine ⟨350212519883564522030041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1867800106045677450826885 350212519883564522030041)
                  ·
                    rfl

theorem cell21_1534582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_1534582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1534582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1534582 prefixEnd_1534582 := by exact prefixLift 1534582
  have htrace : WordTrace (prefixWord ++ tailWord_1534582) baseStart_1534582 baseEnd_1534582 := by
    simpa [prefixWord, tailWord_1534582, baseEnd_1534582] using wordTrace_append hprefix tailTrace_1534582
  have hstable : (prefixWord ++ tailWord_1534582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534582).length < 2 ^ (prefixWord ++ tailWord_1534582).sum := by decide
  have hdescent : baseEnd_1534582 < baseStart_1534582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534593 : List Nat := [1, 2, 4, 2, 1, 1, 1, 6, 3]
def baseStart_1534593 : Nat := 118140960795 + 1534593 * 2 ^ 59
def prefixEnd_1534593 : Nat := 4983230072969 + 3 ^ 40 * 1534593 * 2
def baseEnd_1534593 : Nat := 350215030233430947346685

theorem tailTrace_1534593 : CollatzResearch.WordTrace tailWord_1534593 prefixEnd_1534593 350215030233430947346685 := by
  unfold tailWord_1534593
  simp only [CollatzResearch.WordTrace]
  refine ⟨55971204929439123463648433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37314136619626082309098955 55971204929439123463648433)
  ·
    refine ⟨41978403697079342597736325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55971204929439123463648433 41978403697079342597736325)
    ·
      refine ⟨7870950693202376737075561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41978403697079342597736325 7870950693202376737075561)
      ·
        refine ⟨5903213019901782552806671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7870950693202376737075561 5903213019901782552806671)
        ·
          refine ⟨8854819529852673829210007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5903213019901782552806671 8854819529852673829210007)
          ·
            refine ⟨13282229294779010743815011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8854819529852673829210007 13282229294779010743815011)
            ·
              refine ⟨19923343942168516115722517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13282229294779010743815011 19923343942168516115722517)
              ·
                refine ⟨933906747289149192924493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19923343942168516115722517 933906747289149192924493)
                ·
                  refine ⟨350215030233430947346685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 933906747289149192924493 350215030233430947346685)
                  ·
                    rfl

theorem cell21_1534593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6, 3].length) (baseStart_1534593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1534593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1534593 prefixEnd_1534593 := by exact prefixLift 1534593
  have htrace : WordTrace (prefixWord ++ tailWord_1534593) baseStart_1534593 baseEnd_1534593 := by
    simpa [prefixWord, tailWord_1534593, baseEnd_1534593] using wordTrace_append hprefix tailTrace_1534593
  have hstable : (prefixWord ++ tailWord_1534593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534593).length < 2 ^ (prefixWord ++ tailWord_1534593).sum := by decide
  have hdescent : baseEnd_1534593 < baseStart_1534593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534638 : List Nat := [4, 1, 4, 1, 1, 1, 9]
def baseStart_1534638 : Nat := 118140960795 + 1534638 * 2 ^ 59
def prefixEnd_1534638 : Nat := 4983230072969 + 3 ^ 40 * 1534638 * 2
def baseEnd_1534638 : Nat := 38913922205168985455177

theorem tailTrace_1534638 : CollatzResearch.WordTrace tailWord_1534638 prefixEnd_1534638 38913922205168985455177 := by
  unfold tailWord_1534638
  simp only [CollatzResearch.WordTrace]
  refine ⟨6996605776784512018629571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37315230809517397432691045 6996605776784512018629571)
  ·
    refine ⟨10494908665176768027944357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6996605776784512018629571 10494908665176768027944357)
    ·
      refine ⟨1967795374720644005239567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10494908665176768027944357 1967795374720644005239567)
      ·
        refine ⟨2951693062080966007859351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1967795374720644005239567 2951693062080966007859351)
        ·
          refine ⟨4427539593121449011789027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2951693062080966007859351 4427539593121449011789027)
          ·
            refine ⟨6641309389682173517683541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4427539593121449011789027 6641309389682173517683541)
            ·
              refine ⟨38913922205168985455177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6641309389682173517683541 38913922205168985455177)
              ·
                rfl

theorem cell21_1534638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 9].length) (baseStart_1534638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1534638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1534638 prefixEnd_1534638 := by exact prefixLift 1534638
  have htrace : WordTrace (prefixWord ++ tailWord_1534638) baseStart_1534638 baseEnd_1534638 := by
    simpa [prefixWord, tailWord_1534638, baseEnd_1534638] using wordTrace_append hprefix tailTrace_1534638
  have hstable : (prefixWord ++ tailWord_1534638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534638).length < 2 ^ (prefixWord ++ tailWord_1534638).sum := by decide
  have hdescent : baseEnd_1534638 < baseStart_1534638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534711 : List Nat := [1, 1, 3, 1, 1, 1, 3, 5, 5]
def baseStart_1534711 : Nat := 118140960795 + 1534711 * 2 ^ 59
def prefixEnd_1534711 : Nat := 4983230072969 + 3 ^ 40 * 1534711 * 2
def baseEnd_1534711 : Nat := 350241959441088964379777

theorem tailTrace_1534711 : CollatzResearch.WordTrace tailWord_1534711 prefixEnd_1534711 350241959441088964379777 := by
  unfold tailWord_1534711
  simp only [CollatzResearch.WordTrace]
  refine ⟨55975508743011629616443987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37317005828674419744295991 55975508743011629616443987)
  ·
    refine ⟨83963263114517444424665981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55975508743011629616443987 83963263114517444424665981)
    ·
      refine ⟨31486223667944041659249743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83963263114517444424665981 31486223667944041659249743)
      ·
        refine ⟨47229335501916062488874615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31486223667944041659249743 47229335501916062488874615)
        ·
          refine ⟨70844003252874093733311923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47229335501916062488874615 70844003252874093733311923)
          ·
            refine ⟨106266004879311140599967885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70844003252874093733311923 106266004879311140599967885)
            ·
              refine ⟨39849751829741677724987957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106266004879311140599967885 39849751829741677724987957)
              ·
                refine ⟨3735914234038282286717621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39849751829741677724987957 3735914234038282286717621)
                ·
                  refine ⟨350241959441088964379777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3735914234038282286717621 350241959441088964379777)
                  ·
                    rfl

theorem cell21_1534711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 5].length) (baseStart_1534711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1534711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1534711 prefixEnd_1534711 := by exact prefixLift 1534711
  have htrace : WordTrace (prefixWord ++ tailWord_1534711) baseStart_1534711 baseEnd_1534711 := by
    simpa [prefixWord, tailWord_1534711, baseEnd_1534711] using wordTrace_append hprefix tailTrace_1534711
  have hstable : (prefixWord ++ tailWord_1534711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534711).length < 2 ^ (prefixWord ++ tailWord_1534711).sum := by decide
  have hdescent : baseEnd_1534711 < baseStart_1534711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534728 : List Nat := [2, 1, 3, 2, 2, 3, 1, 2, 5]
def baseStart_1534728 : Nat := 118140960795 + 1534728 * 2 ^ 59
def prefixEnd_1534728 : Nat := 4983230072969 + 3 ^ 40 * 1534728 * 2
def baseEnd_1534728 : Nat := 350245839072700712596409

theorem tailTrace_1534728 : CollatzResearch.WordTrace tailWord_1534728 prefixEnd_1534728 350245839072700712596409 := by
  unfold tailWord_1534728
  simp only [CollatzResearch.WordTrace]
  refine ⟨27988064391975020759906419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37317419189300027679875225 27988064391975020759906419)
  ·
    refine ⟨41982096587962531139859629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27988064391975020759906419 41982096587962531139859629)
    ·
      refine ⟨15743286220485949177447361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41982096587962531139859629 15743286220485949177447361)
      ·
        refine ⟨11807464665364461883085521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15743286220485949177447361 11807464665364461883085521)
        ·
          refine ⟨8855598499023346412314141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11807464665364461883085521 8855598499023346412314141)
          ·
            refine ⟨3320849437133754904617803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8855598499023346412314141 3320849437133754904617803)
            ·
              refine ⟨4981274155700632356926705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3320849437133754904617803 4981274155700632356926705)
              ·
                refine ⟨3735955616775474267695029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4981274155700632356926705 3735955616775474267695029)
                ·
                  refine ⟨350245839072700712596409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3735955616775474267695029 350245839072700712596409)
                  ·
                    rfl

theorem cell21_1534728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 5].length) (baseStart_1534728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1534728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1534728 prefixEnd_1534728 := by exact prefixLift 1534728
  have htrace : WordTrace (prefixWord ++ tailWord_1534728) baseStart_1534728 baseEnd_1534728 := by
    simpa [prefixWord, tailWord_1534728, baseEnd_1534728] using wordTrace_append hprefix tailTrace_1534728
  have hstable : (prefixWord ++ tailWord_1534728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534728).length < 2 ^ (prefixWord ++ tailWord_1534728).sum := by decide
  have hdescent : baseEnd_1534728 < baseStart_1534728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534762 : List Nat := [3, 1, 4, 3, 1, 1, 2, 1, 5]
def baseStart_1534762 : Nat := 118140960795 + 1534762 * 2 ^ 59
def prefixEnd_1534762 : Nat := 4983230072969 + 3 ^ 40 * 1534762 * 2
def baseEnd_1534762 : Nat := 350253598335924209029673

theorem tailTrace_1534762 : CollatzResearch.WordTrace tailWord_1534762 prefixEnd_1534762 350253598335924209029673 := by
  unfold tailWord_1534762
  simp only [CollatzResearch.WordTrace]
  refine ⟨13994342216456716331637635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37318245910551243551033693 13994342216456716331637635)
  ·
    refine ⟨20991513324685074497456453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13994342216456716331637635 20991513324685074497456453)
    ·
      refine ⟨3935908748378451468273085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20991513324685074497456453 3935908748378451468273085)
      ·
        refine ⟨1475965780641919300602407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3935908748378451468273085 1475965780641919300602407)
        ·
          refine ⟨2213948670962878950903611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1475965780641919300602407 2213948670962878950903611)
          ·
            refine ⟨3320923006444318426355417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2213948670962878950903611 3320923006444318426355417)
            ·
              refine ⟨2490692254833238819766563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3320923006444318426355417 2490692254833238819766563)
              ·
                refine ⟨3736038382249858229649845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2490692254833238819766563 3736038382249858229649845)
                ·
                  refine ⟨350253598335924209029673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3736038382249858229649845 350253598335924209029673)
                  ·
                    rfl

theorem cell21_1534762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_1534762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1534762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1534762 prefixEnd_1534762 := by exact prefixLift 1534762
  have htrace : WordTrace (prefixWord ++ tailWord_1534762) baseStart_1534762 baseEnd_1534762 := by
    simpa [prefixWord, tailWord_1534762, baseEnd_1534762] using wordTrace_append hprefix tailTrace_1534762
  have hstable : (prefixWord ++ tailWord_1534762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534762).length < 2 ^ (prefixWord ++ tailWord_1534762).sum := by decide
  have hdescent : baseEnd_1534762 < baseStart_1534762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534787 : List Nat := [1, 1, 1, 3, 1, 4, 1, 4, 5]
def baseStart_1534787 : Nat := 118140960795 + 1534787 * 2 ^ 59
def prefixEnd_1534787 : Nat := 4983230072969 + 3 ^ 40 * 1534787 * 2
def baseEnd_1534787 : Nat := 350259303676529721112955

theorem tailTrace_1534787 : CollatzResearch.WordTrace tailWord_1534787 prefixEnd_1534787 350259303676529721112955 := by
  unfold tailWord_1534787
  simp only [CollatzResearch.WordTrace]
  refine ⟨55978280690736294596210615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37318853793824196397473743 55978280690736294596210615)
  ·
    refine ⟨83967421036104441894315923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55978280690736294596210615 83967421036104441894315923)
    ·
      refine ⟨125951131554156662841473885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83967421036104441894315923 125951131554156662841473885)
      ·
        refine ⟨47231674332808748565552707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125951131554156662841473885 47231674332808748565552707)
        ·
          refine ⟨70847511499213122848329061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47231674332808748565552707 70847511499213122848329061)
          ·
            refine ⟨13283908406102460534061699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70847511499213122848329061 13283908406102460534061699)
            ·
              refine ⟨19925862609153690801092549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13283908406102460534061699 19925862609153690801092549)
              ·
                refine ⟨3736099239216317025204853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19925862609153690801092549 3736099239216317025204853)
                ·
                  refine ⟨350259303676529721112955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3736099239216317025204853 350259303676529721112955)
                  ·
                    rfl

theorem cell21_1534787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 5].length) (baseStart_1534787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1534787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1534787 prefixEnd_1534787 := by exact prefixLift 1534787
  have htrace : WordTrace (prefixWord ++ tailWord_1534787) baseStart_1534787 baseEnd_1534787 := by
    simpa [prefixWord, tailWord_1534787, baseEnd_1534787] using wordTrace_append hprefix tailTrace_1534787
  have hstable : (prefixWord ++ tailWord_1534787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534787).length < 2 ^ (prefixWord ++ tailWord_1534787).sum := by decide
  have hdescent : baseEnd_1534787 < baseStart_1534787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534832 : List Nat := [2, 1, 1, 1, 4, 1, 3, 8]
def baseStart_1534832 : Nat := 118140960795 + 1534832 * 2 ^ 59
def prefixEnd_1534832 : Nat := 4983230072969 + 3 ^ 40 * 1534832 * 2
def baseEnd_1534832 : Nat := 116756524429873214287621

theorem tailTrace_1534832 : CollatzResearch.WordTrace tailWord_1534832 prefixEnd_1534832 116756524429873214287621 := by
  unfold tailWord_1534832
  simp only [CollatzResearch.WordTrace]
  refine ⟨27989960987786633640799375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37319947983715511521065833 27989960987786633640799375)
  ·
    refine ⟨41984941481679950461199063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27989960987786633640799375 41984941481679950461199063)
    ·
      refine ⟨62977412222519925691798595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41984941481679950461199063 62977412222519925691798595)
      ·
        refine ⟨94466118333779888537697893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62977412222519925691798595 94466118333779888537697893)
        ·
          refine ⟨17712397187583729100818355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94466118333779888537697893 17712397187583729100818355)
          ·
            refine ⟨26568595781375593651227533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17712397187583729100818355 26568595781375593651227533)
            ·
              refine ⟨9963223418015847619210325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26568595781375593651227533 9963223418015847619210325)
              ·
                refine ⟨116756524429873214287621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9963223418015847619210325 116756524429873214287621)
                ·
                  rfl

theorem cell21_1534832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 8].length) (baseStart_1534832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1534832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1534832 prefixEnd_1534832 := by exact prefixLift 1534832
  have htrace : WordTrace (prefixWord ++ tailWord_1534832) baseStart_1534832 baseEnd_1534832 := by
    simpa [prefixWord, tailWord_1534832, baseEnd_1534832] using wordTrace_append hprefix tailTrace_1534832
  have hstable : (prefixWord ++ tailWord_1534832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534832).length < 2 ^ (prefixWord ++ tailWord_1534832).sum := by decide
  have hdescent : baseEnd_1534832 < baseStart_1534832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534835 : List Nat := [1, 1, 1, 2, 2, 1, 8, 1, 4]
def baseStart_1534835 : Nat := 118140960795 + 1534835 * 2 ^ 59
def prefixEnd_1534835 : Nat := 4983230072969 + 3 ^ 40 * 1534835 * 2
def baseEnd_1534835 : Nat := 350270257930492304312857

theorem tailTrace_1534835 : CollatzResearch.WordTrace tailWord_1534835 prefixEnd_1534835 350270257930492304312857 := by
  unfold tailWord_1534835
  simp only [CollatzResearch.WordTrace]
  refine ⟨55980031394562398793957959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37320020929708265862638639 55980031394562398793957959)
  ·
    refine ⟨83970047091843598190936939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55980031394562398793957959 83970047091843598190936939)
    ·
      refine ⟨125955070637765397286405409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83970047091843598190936939 125955070637765397286405409)
      ·
        refine ⟨94466302978324047964804057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125955070637765397286405409 94466302978324047964804057)
        ·
          refine ⟨70849727233743035973603043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94466302978324047964804057 70849727233743035973603043)
          ·
            refine ⟨106274590850614553960404565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70849727233743035973603043 106274590850614553960404565)
            ·
              refine ⟨1245405361530639304223491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 106274590850614553960404565 1245405361530639304223491)
              ·
                refine ⟨1868108042295958956335237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1245405361530639304223491 1868108042295958956335237)
                ·
                  refine ⟨350270257930492304312857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1868108042295958956335237 350270257930492304312857)
                  ·
                    rfl

theorem cell21_1534835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 4].length) (baseStart_1534835 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1534835 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1534835 prefixEnd_1534835 := by exact prefixLift 1534835
  have htrace : WordTrace (prefixWord ++ tailWord_1534835) baseStart_1534835 baseEnd_1534835 := by
    simpa [prefixWord, tailWord_1534835, baseEnd_1534835] using wordTrace_append hprefix tailTrace_1534835
  have hstable : (prefixWord ++ tailWord_1534835).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534835).length < 2 ^ (prefixWord ++ tailWord_1534835).sum := by decide
  have hdescent : baseEnd_1534835 < baseStart_1534835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534866 : List Nat := [3, 2, 3, 2, 3, 8]
def baseStart_1534866 : Nat := 118140960795 + 1534866 * 2 ^ 59
def prefixEnd_1534866 : Nat := 4983230072969 + 3 ^ 40 * 1534866 * 2
def baseEnd_1534866 : Nat := 12973234538994190344301

theorem tailTrace_1534866 : CollatzResearch.WordTrace tailWord_1534866 prefixEnd_1534866 12973234538994190344301 := by
  unfold tailWord_1534866
  simp only [CollatzResearch.WordTrace]
  refine ⟨13995290514362522772084113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37320774704966727392224301 13995290514362522772084113)
  ·
    refine ⟨10496467885771892079063085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13995290514362522772084113 10496467885771892079063085)
    ·
      refine ⟨3936175457164459529648657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10496467885771892079063085 3936175457164459529648657)
      ·
        refine ⟨2952131592873344647236493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3936175457164459529648657 2952131592873344647236493)
        ·
          refine ⟨1107049347327504242713685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2952131592873344647236493 1107049347327504242713685)
          ·
            refine ⟨12973234538994190344301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1107049347327504242713685 12973234538994190344301)
            ·
              rfl

theorem cell21_1534866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 8].length) (baseStart_1534866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1534866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1534866 prefixEnd_1534866 := by exact prefixLift 1534866
  have htrace : WordTrace (prefixWord ++ tailWord_1534866) baseStart_1534866 baseEnd_1534866 := by
    simpa [prefixWord, tailWord_1534866, baseEnd_1534866] using wordTrace_append hprefix tailTrace_1534866
  have hstable : (prefixWord ++ tailWord_1534866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534866).length < 2 ^ (prefixWord ++ tailWord_1534866).sum := by decide
  have hdescent : baseEnd_1534866 < baseStart_1534866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534984 : List Nat := [2, 1, 3, 2, 1, 3, 9]
def baseStart_1534984 : Nat := 118140960795 + 1534984 * 2 ^ 59
def prefixEnd_1534984 : Nat := 4983230072969 + 3 ^ 40 * 1534984 * 2
def baseEnd_1534984 : Nat := 38922695751166795147691

theorem tailTrace_1534984 : CollatzResearch.WordTrace tailWord_1534984 prefixEnd_1534984 38922695751166795147691 := by
  unfold tailWord_1534984
  simp only [CollatzResearch.WordTrace]
  refine ⟨27992732935511298620566003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37323643914015064827421337 27992732935511298620566003)
  ·
    refine ⟨41989099403266947930849005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27992732935511298620566003 41989099403266947930849005)
    ·
      refine ⟨15745912276225105474068377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41989099403266947930849005 15745912276225105474068377)
      ·
        refine ⟨11809434207168829105551283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15745912276225105474068377 11809434207168829105551283)
        ·
          refine ⟨17714151310753243658326925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11809434207168829105551283 17714151310753243658326925)
          ·
            refine ⟨6642806741532466371872597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17714151310753243658326925 6642806741532466371872597)
            ·
              refine ⟨38922695751166795147691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6642806741532466371872597 38922695751166795147691)
              ·
                rfl

theorem cell21_1534984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 9].length) (baseStart_1534984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1534984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1534984 prefixEnd_1534984 := by exact prefixLift 1534984
  have htrace : WordTrace (prefixWord ++ tailWord_1534984) baseStart_1534984 baseEnd_1534984 := by
    simpa [prefixWord, tailWord_1534984, baseEnd_1534984] using wordTrace_append hprefix tailTrace_1534984
  have hstable : (prefixWord ++ tailWord_1534984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534984).length < 2 ^ (prefixWord ++ tailWord_1534984).sum := by decide
  have hdescent : baseEnd_1534984 < baseStart_1534984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534990 : List Nat := [4, 1, 1, 2, 2, 3, 3, 2, 3]
def baseStart_1534990 : Nat := 118140960795 + 1534990 * 2 ^ 59
def prefixEnd_1534990 : Nat := 4983230072969 + 3 ^ 40 * 1534990 * 2
def baseEnd_1534990 : Nat := 350305631042246479229207

theorem tailTrace_1534990 : CollatzResearch.WordTrace tailWord_1534990 prefixEnd_1534990 350305631042246479229207 := by
  unfold tailWord_1534990
  simp only [CollatzResearch.WordTrace]
  refine ⟨6998210588625107533231303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37323789806000573510566949 6998210588625107533231303)
  ·
    refine ⟨10497315882937661299846955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6998210588625107533231303 10497315882937661299846955)
    ·
      refine ⟨15745973824406491949770433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10497315882937661299846955 15745973824406491949770433)
      ·
        refine ⟨11809480368304868962327825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15745973824406491949770433 11809480368304868962327825)
        ·
          refine ⟨8857110276228651721745869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11809480368304868962327825 8857110276228651721745869)
          ·
            refine ⟨3321416353585744395654701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8857110276228651721745869 3321416353585744395654701)
            ·
              refine ⟨1245531132594654148370513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3321416353585744395654701 1245531132594654148370513)
              ·
                refine ⟨934148349445990611277885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1245531132594654148370513 934148349445990611277885)
                ·
                  refine ⟨350305631042246479229207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 934148349445990611277885 350305631042246479229207)
                  ·
                    rfl

theorem cell21_1534990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_1534990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1534990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1534990 prefixEnd_1534990 := by exact prefixLift 1534990
  have htrace : WordTrace (prefixWord ++ tailWord_1534990) baseStart_1534990 baseEnd_1534990 := by
    simpa [prefixWord, tailWord_1534990, baseEnd_1534990] using wordTrace_append hprefix tailTrace_1534990
  have hstable : (prefixWord ++ tailWord_1534990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534990).length < 2 ^ (prefixWord ++ tailWord_1534990).sum := by decide
  have hdescent : baseEnd_1534990 < baseStart_1534990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
