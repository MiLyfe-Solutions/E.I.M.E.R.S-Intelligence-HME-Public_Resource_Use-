import V185TrunkScan23Chunk1396

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8274667 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 3, 5, 2]
def baseStart_8274667 : Nat := 118140960795 + 8274667 * 2 ^ 59
def prefixEnd_8274667 : Nat := 4983230072969 + 3 ^ 40 * 8274667 * 2
def baseEnd_8274667 : Nat := 4248881426897282061008005

theorem tailTrace_8274667 : CollatzResearch.WordTrace tailWord_8274667 prefixEnd_8274667 4248881426897282061008005 := by
  unfold tailWord_8274667
  simp only [CollatzResearch.WordTrace]
  refine ⟨301801899513302134458062255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201201266342201422972041503 301801899513302134458062255)
  ·
    refine ⟨452702849269953201687093383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301801899513302134458062255 452702849269953201687093383)
    ·
      refine ⟨679054273904929802530640075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452702849269953201687093383 679054273904929802530640075)
      ·
        refine ⟨1018581410857394703795960113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679054273904929802530640075 1018581410857394703795960113)
        ·
          refine ⟨763936058143046027846970085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1018581410857394703795960113 763936058143046027846970085)
          ·
            refine ⟨143238010901821130221306891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 763936058143046027846970085 143238010901821130221306891)
            ·
              refine ⟨214857016352731695331960337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143238010901821130221306891 214857016352731695331960337)
              ·
                refine ⟨161142762264548771498970253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214857016352731695331960337 161142762264548771498970253)
                ·
                  refine ⟨60428535849205789312113845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161142762264548771498970253 60428535849205789312113845)
                  ·
                    refine ⟨5665175235863042748010673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60428535849205789312113845 5665175235863042748010673)
                    ·
                      refine ⟨4248881426897282061008005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5665175235863042748010673 4248881426897282061008005)
                      ·
                        rfl

theorem cell23_8274667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 5, 2].length) (baseStart_8274667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274667 prefixEnd_8274667 := by exact prefixLift 8274667
  have htrace : WordTrace (prefixWord ++ tailWord_8274667) baseStart_8274667 baseEnd_8274667 := by
    simpa [prefixWord, tailWord_8274667, baseEnd_8274667] using wordTrace_append hprefix tailTrace_8274667
  have hstable : (prefixWord ++ tailWord_8274667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274667).length < 2 ^ (prefixWord ++ tailWord_8274667).sum := by decide
  have hdescent : baseEnd_8274667 < baseStart_8274667 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274697 : List Nat := [1, 2, 1, 1, 3, 2, 4, 1, 3, 1, 4]
def baseStart_8274697 : Nat := 118140960795 + 8274697 * 2 ^ 59
def prefixEnd_8274697 : Nat := 4983230072969 + 3 ^ 40 * 8274697 * 2
def baseEnd_8274697 : Nat := 4248896831316916943632867

theorem tailTrace_8274697 : CollatzResearch.WordTrace tailWord_8274697 prefixEnd_8274697 4248896831316916943632867 := by
  unfold tailWord_8274697
  simp only [CollatzResearch.WordTrace]
  refine ⟨301802993703193449581654345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201201995802128966387769563 301802993703193449581654345)
  ·
    refine ⟨226352245277395087186240759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301802993703193449581654345 226352245277395087186240759)
    ·
      refine ⟨339528367916092630779361139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226352245277395087186240759 339528367916092630779361139)
      ·
        refine ⟨509292551874138946169041709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339528367916092630779361139 509292551874138946169041709)
        ·
          refine ⟨190984706952802104813390641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 509292551874138946169041709 190984706952802104813390641)
          ·
            refine ⟨143238530214601578610042981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190984706952802104813390641 143238530214601578610042981)
            ·
              refine ⟨26857224415237795989383059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143238530214601578610042981 26857224415237795989383059)
              ·
                refine ⟨40285836622856693984074589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26857224415237795989383059 40285836622856693984074589)
                ·
                  refine ⟨15107188733571260244027971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40285836622856693984074589 15107188733571260244027971)
                  ·
                    refine ⟨22660783100356890366041957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15107188733571260244027971 22660783100356890366041957)
                    ·
                      refine ⟨4248896831316916943632867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22660783100356890366041957 4248896831316916943632867)
                      ·
                        rfl

theorem cell23_8274697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 1, 4].length) (baseStart_8274697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274697 prefixEnd_8274697 := by exact prefixLift 8274697
  have htrace : WordTrace (prefixWord ++ tailWord_8274697) baseStart_8274697 baseEnd_8274697 := by
    simpa [prefixWord, tailWord_8274697, baseEnd_8274697] using wordTrace_append hprefix tailTrace_8274697
  have hstable : (prefixWord ++ tailWord_8274697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274697).length < 2 ^ (prefixWord ++ tailWord_8274697).sum := by decide
  have hdescent : baseEnd_8274697 < baseStart_8274697 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274707 : List Nat := [1, 1, 1, 2, 1, 3, 4, 2, 4, 4]
def baseStart_8274707 : Nat := 118140960795 + 8274707 * 2 ^ 59
def prefixEnd_8274707 : Nat := 4983230072969 + 3 ^ 40 * 8274707 * 2
def baseEnd_8274707 : Nat := 1416300655374487301502607

theorem tailTrace_8274707 : CollatzResearch.WordTrace tailWord_8274707 prefixEnd_8274707 1416300655374487301502607 := by
  unfold tailWord_8274707
  simp only [CollatzResearch.WordTrace]
  refine ⟨301803358433157221289518375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201202238955438147526345583 301803358433157221289518375)
  ·
    refine ⟨452705037649735831934277563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301803358433157221289518375 452705037649735831934277563)
    ·
      refine ⟨679057556474603747901416345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452705037649735831934277563 679057556474603747901416345)
      ·
        refine ⟨509293167355952810926062259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 679057556474603747901416345 509293167355952810926062259)
        ·
          refine ⟨763939751033929216389093389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509293167355952810926062259 763939751033929216389093389)
          ·
            refine ⟨286477406637723456145910021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 763939751033929216389093389 286477406637723456145910021)
            ·
              refine ⟨53714513744573148027358129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 286477406637723456145910021 53714513744573148027358129)
              ·
                refine ⟨40285885308429861020518597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53714513744573148027358129 40285885308429861020518597)
                ·
                  refine ⟨7553603495330598941347237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40285885308429861020518597 7553603495330598941347237)
                  ·
                    refine ⟨1416300655374487301502607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7553603495330598941347237 1416300655374487301502607)
                    ·
                      rfl

theorem cell23_8274707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4, 4].length) (baseStart_8274707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274707 prefixEnd_8274707 := by exact prefixLift 8274707
  have htrace : WordTrace (prefixWord ++ tailWord_8274707) baseStart_8274707 baseEnd_8274707 := by
    simpa [prefixWord, tailWord_8274707, baseEnd_8274707] using wordTrace_append hprefix tailTrace_8274707
  have hstable : (prefixWord ++ tailWord_8274707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274707).length < 2 ^ (prefixWord ++ tailWord_8274707).sum := by decide
  have hdescent : baseEnd_8274707 < baseStart_8274707 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274714 : List Nat := [3, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4]
def baseStart_8274714 : Nat := 118140960795 + 8274714 * 2 ^ 59
def prefixEnd_8274714 : Nat := 4983230072969 + 3 ^ 40 * 8274714 * 2
def baseEnd_8274714 : Nat := 4248905560488043377120289

theorem tailTrace_8274714 : CollatzResearch.WordTrace tailWord_8274714 prefixEnd_8274714 4248905560488043377120289 := by
  unfold tailWord_8274714
  simp only [CollatzResearch.WordTrace]
  refine ⟨75450903436032965371255799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201202409162754574323348797 75450903436032965371255799)
  ·
    refine ⟨113176355154049448056883699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75450903436032965371255799 113176355154049448056883699)
    ·
      refine ⟨169764532731074172085325549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113176355154049448056883699 169764532731074172085325549)
      ·
        refine ⟨63661699774152814531997081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169764532731074172085325549 63661699774152814531997081)
        ·
          refine ⟨47746274830614610898997811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63661699774152814531997081 47746274830614610898997811)
          ·
            refine ⟨71619412245921916348496717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47746274830614610898997811 71619412245921916348496717)
            ·
              refine ⟨26857279592220718630686269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71619412245921916348496717 26857279592220718630686269)
              ·
                refine ⟨10071479847082769486507351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26857279592220718630686269 10071479847082769486507351)
                ·
                  refine ⟨15107219770624154229761027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10071479847082769486507351 15107219770624154229761027)
                  ·
                    refine ⟨22660829655936231344641541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15107219770624154229761027 22660829655936231344641541)
                    ·
                      refine ⟨4248905560488043377120289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22660829655936231344641541 4248905560488043377120289)
                      ·
                        rfl

theorem cell23_8274714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_8274714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274714 prefixEnd_8274714 := by exact prefixLift 8274714
  have htrace : WordTrace (prefixWord ++ tailWord_8274714) baseStart_8274714 baseEnd_8274714 := by
    simpa [prefixWord, tailWord_8274714, baseEnd_8274714] using wordTrace_append hprefix tailTrace_8274714
  have hstable : (prefixWord ++ tailWord_8274714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274714).length < 2 ^ (prefixWord ++ tailWord_8274714).sum := by decide
  have hdescent : baseEnd_8274714 < baseStart_8274714 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274734 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_8274734 : Nat := 118140960795 + 8274734 * 2 ^ 59
def prefixEnd_8274734 : Nat := 4983230072969 + 3 ^ 40 * 8274734 * 2
def baseEnd_8274734 : Nat := 4248915830101133298870197

theorem tailTrace_8274734 : CollatzResearch.WordTrace tailWord_8274734 prefixEnd_8274734 4248915830101133298870197 := by
  unfold tailWord_8274734
  simp only [CollatzResearch.WordTrace]
  refine ⟨37725542900507425612593907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201202895469372936600500837 37725542900507425612593907)
  ·
    refine ⟨56588314350761138418890861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37725542900507425612593907 56588314350761138418890861)
    ·
      refine ⟨21220617881535426907084073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56588314350761138418890861 21220617881535426907084073)
      ·
        refine ⟨15915463411151570180313055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21220617881535426907084073 15915463411151570180313055)
        ·
          refine ⟨23873195116727355270469583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15915463411151570180313055 23873195116727355270469583)
          ·
            refine ⟨35809792675091032905704375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23873195116727355270469583 35809792675091032905704375)
            ·
              refine ⟨53714689012636549358556563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35809792675091032905704375 53714689012636549358556563)
              ·
                refine ⟨80572033518954824037834845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53714689012636549358556563 80572033518954824037834845)
                ·
                  refine ⟨30214512569608059014188067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80572033518954824037834845 30214512569608059014188067)
                  ·
                    refine ⟨45321768854412088521282101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30214512569608059014188067 45321768854412088521282101)
                    ·
                      refine ⟨4248915830101133298870197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45321768854412088521282101 4248915830101133298870197)
                      ·
                        rfl

theorem cell23_8274734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_8274734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274734 prefixEnd_8274734 := by exact prefixLift 8274734
  have htrace : WordTrace (prefixWord ++ tailWord_8274734) baseStart_8274734 baseEnd_8274734 := by
    simpa [prefixWord, tailWord_8274734, baseEnd_8274734] using wordTrace_append hprefix tailTrace_8274734
  have hstable : (prefixWord ++ tailWord_8274734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274734).length < 2 ^ (prefixWord ++ tailWord_8274734).sum := by decide
  have hdescent : baseEnd_8274734 < baseStart_8274734 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274751 : List Nat := [1, 1, 2, 2, 5, 2, 2, 2, 1, 2, 3]
def baseStart_8274751 : Nat := 118140960795 + 8274751 * 2 ^ 59
def prefixEnd_8274751 : Nat := 4983230072969 + 3 ^ 40 * 8274751 * 2
def baseEnd_8274751 : Nat := 4248924559272259732357619

theorem tailTrace_8274751 : CollatzResearch.WordTrace tailWord_8274751 prefixEnd_8274751 4248924559272259732357619 := by
  unfold tailWord_8274751
  simp only [CollatzResearch.WordTrace]
  refine ⟨301804963244997816804120107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201203308829998544536080071 301804963244997816804120107)
  ·
    refine ⟨452707444867496725206180161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301804963244997816804120107 452707444867496725206180161)
    ·
      refine ⟨339530583650622543904635121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452707444867496725206180161 339530583650622543904635121)
      ·
        refine ⟨254647937737966907928476341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339530583650622543904635121 254647937737966907928476341)
        ·
          refine ⟨23873244162934397618294657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 254647937737966907928476341 23873244162934397618294657)
          ·
            refine ⟨17904933122200798213720993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23873244162934397618294657 17904933122200798213720993)
            ·
              refine ⟨13428699841650598660290745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17904933122200798213720993 13428699841650598660290745)
              ·
                refine ⟨10071524881237948995218059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13428699841650598660290745 10071524881237948995218059)
                ·
                  refine ⟨15107287321856923492827089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10071524881237948995218059 15107287321856923492827089)
                  ·
                    refine ⟨11330465491392692619620317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15107287321856923492827089 11330465491392692619620317)
                    ·
                      refine ⟨4248924559272259732357619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11330465491392692619620317 4248924559272259732357619)
                      ·
                        rfl

theorem cell23_8274751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 2, 3].length) (baseStart_8274751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274751 prefixEnd_8274751 := by exact prefixLift 8274751
  have htrace : WordTrace (prefixWord ++ tailWord_8274751) baseStart_8274751 baseEnd_8274751 := by
    simpa [prefixWord, tailWord_8274751, baseEnd_8274751] using wordTrace_append hprefix tailTrace_8274751
  have hstable : (prefixWord ++ tailWord_8274751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274751).length < 2 ^ (prefixWord ++ tailWord_8274751).sum := by decide
  have hdescent : baseEnd_8274751 < baseStart_8274751 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274797 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 1, 8]
def baseStart_8274797 : Nat := 118140960795 + 8274797 * 2 ^ 59
def prefixEnd_8274797 : Nat := 4983230072969 + 3 ^ 40 * 8274797 * 2
def baseEnd_8274797 : Nat := 1416316059794122184127469

theorem tailTrace_8274797 : CollatzResearch.WordTrace tailWord_8274797 prefixEnd_8274797 1416316059794122184127469 := by
  unfold tailWord_8274797
  simp only [CollatzResearch.WordTrace]
  refine ⟨301806641002831166660294645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201204427335220777773529763 301806641002831166660294645)
  ·
    refine ⟨28294372594015421874402623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 301806641002831166660294645 28294372594015421874402623)
    ·
      refine ⟨42441558891023132811603935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28294372594015421874402623 42441558891023132811603935)
      ·
        refine ⟨63662338336534699217405903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42441558891023132811603935 63662338336534699217405903)
        ·
          refine ⟨95493507504802048826108855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63662338336534699217405903 95493507504802048826108855)
          ·
            refine ⟨143240261257203073239163283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95493507504802048826108855 143240261257203073239163283)
            ·
              refine ⟨214860391885804609858744925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143240261257203073239163283 214860391885804609858744925)
              ·
                refine ⟨80572646957176728697029347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214860391885804609858744925 80572646957176728697029347)
                ·
                  refine ⟨120858970435765093045544021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80572646957176728697029347 120858970435765093045544021)
                  ·
                    refine ⟨1416316059794122184127469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120858970435765093045544021 1416316059794122184127469)
                    ·
                      rfl

theorem cell23_8274797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_8274797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274797 prefixEnd_8274797 := by exact prefixLift 8274797
  have htrace : WordTrace (prefixWord ++ tailWord_8274797) baseStart_8274797 baseEnd_8274797 := by
    simpa [prefixWord, tailWord_8274797, baseEnd_8274797] using wordTrace_append hprefix tailTrace_8274797
  have hstable : (prefixWord ++ tailWord_8274797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274797).length < 2 ^ (prefixWord ++ tailWord_8274797).sum := by decide
  have hdescent : baseEnd_8274797 < baseStart_8274797 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274821 : List Nat := [1, 3, 1, 1, 3, 4, 1, 2, 1, 4, 2]
def baseStart_8274821 : Nat := 118140960795 + 8274821 * 2 ^ 59
def prefixEnd_8274821 : Nat := 4983230072969 + 3 ^ 40 * 8274821 * 2
def baseEnd_8274821 : Nat := 4248960502918074458482297

theorem tailTrace_8274821 : CollatzResearch.WordTrace tailWord_8274821 prefixEnd_8274821 4248960502918074458482297 := by
  unfold tailWord_8274821
  simp only [CollatzResearch.WordTrace]
  refine ⟨301807516354744218759168317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201205010903162812506112211 301807516354744218759168317)
  ·
    refine ⟨113177818633029082034688119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301807516354744218759168317 113177818633029082034688119)
    ·
      refine ⟨169766727949543623052032179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113177818633029082034688119 169766727949543623052032179)
      ·
        refine ⟨254650091924315434578048269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169766727949543623052032179 254650091924315434578048269)
        ·
          refine ⟨95493784471618287966768101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254650091924315434578048269 95493784471618287966768101)
          ·
            refine ⟨17905084588428428993769019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95493784471618287966768101 17905084588428428993769019)
            ·
              refine ⟨26857626882642643490653529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17905084588428428993769019 26857626882642643490653529)
              ·
                refine ⟨20143220161981982617990147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26857626882642643490653529 20143220161981982617990147)
                ·
                  refine ⟨30214830242972973926985221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20143220161981982617990147 30214830242972973926985221)
                  ·
                    refine ⟨5665280670557432611309729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30214830242972973926985221 5665280670557432611309729)
                    ·
                      refine ⟨4248960502918074458482297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5665280670557432611309729 4248960502918074458482297)
                      ·
                        rfl

theorem cell23_8274821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 4, 2].length) (baseStart_8274821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274821 prefixEnd_8274821 := by exact prefixLift 8274821
  have htrace : WordTrace (prefixWord ++ tailWord_8274821) baseStart_8274821 baseEnd_8274821 := by
    simpa [prefixWord, tailWord_8274821, baseEnd_8274821] using wordTrace_append hprefix tailTrace_8274821
  have hstable : (prefixWord ++ tailWord_8274821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274821).length < 2 ^ (prefixWord ++ tailWord_8274821).sum := by decide
  have hdescent : baseEnd_8274821 < baseStart_8274821 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274824 : List Nat := [2, 1, 3, 3, 2, 1, 2, 1, 2, 1, 5]
def baseStart_8274824 : Nat := 118140960795 + 8274824 * 2 ^ 59
def prefixEnd_8274824 : Nat := 4983230072969 + 3 ^ 40 * 8274824 * 2
def baseEnd_8274824 : Nat := 4248962043360037946744783

theorem tailTrace_8274824 : CollatzResearch.WordTrace tailWord_8274824 prefixEnd_8274824 4248962043360037946744783 := by
  unfold tailWord_8274824
  simp only [CollatzResearch.WordTrace]
  refine ⟨150903812886866675135763763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201205083849155566847685017 150903812886866675135763763)
  ·
    refine ⟨226355719330300012703645645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150903812886866675135763763 226355719330300012703645645)
    ·
      refine ⟨84883394748862504763867117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226355719330300012703645645 84883394748862504763867117)
      ·
        refine ⟨31831273030823439286450169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84883394748862504763867117 31831273030823439286450169)
        ·
          refine ⟨23873454773117579464837627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31831273030823439286450169 23873454773117579464837627)
          ·
            refine ⟨35810182159676369197256441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23873454773117579464837627 35810182159676369197256441)
            ·
              refine ⟨26857636619757276897942331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35810182159676369197256441 26857636619757276897942331)
              ·
                refine ⟨40286454929635915346913497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26857636619757276897942331 40286454929635915346913497)
                ·
                  refine ⟨30214841197226936510185123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40286454929635915346913497 30214841197226936510185123)
                  ·
                    refine ⟨45322261795840404765277685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30214841197226936510185123 45322261795840404765277685)
                    ·
                      refine ⟨4248962043360037946744783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45322261795840404765277685 4248962043360037946744783)
                      ·
                        rfl

theorem cell23_8274824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_8274824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274824 prefixEnd_8274824 := by exact prefixLift 8274824
  have htrace : WordTrace (prefixWord ++ tailWord_8274824) baseStart_8274824 baseEnd_8274824 := by
    simpa [prefixWord, tailWord_8274824, baseEnd_8274824] using wordTrace_append hprefix tailTrace_8274824
  have hstable : (prefixWord ++ tailWord_8274824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274824).length < 2 ^ (prefixWord ++ tailWord_8274824).sum := by decide
  have hdescent : baseEnd_8274824 < baseStart_8274824 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274838 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_8274838 : Nat := 118140960795 + 8274838 * 2 ^ 59
def prefixEnd_8274838 : Nat := 4983230072969 + 3 ^ 40 * 8274838 * 2
def baseEnd_8274838 : Nat := 4248969232089200891969719

theorem tailTrace_8274838 : CollatzResearch.WordTrace tailWord_8274838 prefixEnd_8274838 4248969232089200891969719 := by
  unfold tailWord_8274838
  simp only [CollatzResearch.WordTrace]
  refine ⟨18863008524730164416408573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201205424263788420441691445 18863008524730164416408573)
  ·
    refine ⟨7073628196773811656153215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18863008524730164416408573 7073628196773811656153215)
    ·
      refine ⟨10610442295160717484229823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7073628196773811656153215 10610442295160717484229823)
      ·
        refine ⟨15915663442741076226344735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10610442295160717484229823 15915663442741076226344735)
        ·
          refine ⟨23873495164111614339517103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15915663442741076226344735 23873495164111614339517103)
          ·
            refine ⟨35810242746167421509275655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23873495164111614339517103 35810242746167421509275655)
            ·
              refine ⟨53715364119251132263913483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35810242746167421509275655 53715364119251132263913483)
              ·
                refine ⟨80573046178876698395870225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53715364119251132263913483 80573046178876698395870225)
                ·
                  refine ⟨60429784634157523796902669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80573046178876698395870225 60429784634157523796902669)
                  ·
                    refine ⟨22661169237809071423838501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60429784634157523796902669 22661169237809071423838501)
                    ·
                      refine ⟨4248969232089200891969719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22661169237809071423838501 4248969232089200891969719)
                      ·
                        rfl

theorem cell23_8274838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_8274838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274838 prefixEnd_8274838 := by exact prefixLift 8274838
  have htrace : WordTrace (prefixWord ++ tailWord_8274838) baseStart_8274838 baseEnd_8274838 := by
    simpa [prefixWord, tailWord_8274838, baseEnd_8274838] using wordTrace_append hprefix tailTrace_8274838
  have hstable : (prefixWord ++ tailWord_8274838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274838).length < 2 ^ (prefixWord ++ tailWord_8274838).sum := by decide
  have hdescent : baseEnd_8274838 < baseStart_8274838 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274857 : List Nat := [1, 2, 1, 1, 1, 1, 6, 2, 1, 7]
def baseStart_8274857 : Nat := 118140960795 + 8274857 * 2 ^ 59
def prefixEnd_8274857 : Nat := 4983230072969 + 3 ^ 40 * 8274857 * 2
def baseEnd_8274857 : Nat := 1416326329407212105877377

theorem tailTrace_8274857 : CollatzResearch.WordTrace tailWord_8274857 prefixEnd_8274857 1416326329407212105877377 := by
  unfold tailWord_8274857
  simp only [CollatzResearch.WordTrace]
  refine ⟨301808829382613796907478825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201205886255075864604985883 301808829382613796907478825)
  ·
    refine ⟨226356622036960347680609119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301808829382613796907478825 226356622036960347680609119)
    ·
      refine ⟨339534933055440521520913679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226356622036960347680609119 339534933055440521520913679)
      ·
        refine ⟨509302399583160782281370519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339534933055440521520913679 509302399583160782281370519)
        ·
          refine ⟨763953599374741173422055779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509302399583160782281370519 763953599374741173422055779)
          ·
            refine ⟨1145930399062111760133083669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763953599374741173422055779 1145930399062111760133083669)
            ·
              refine ⟨53715487456036488756238297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1145930399062111760133083669 53715487456036488756238297)
              ·
                refine ⟨40286615592027366567178723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53715487456036488756238297 40286615592027366567178723)
                ·
                  refine ⟨60429923388041049850768085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40286615592027366567178723 60429923388041049850768085)
                  ·
                    refine ⟨1416326329407212105877377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60429923388041049850768085 1416326329407212105877377)
                    ·
                      rfl

theorem cell23_8274857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 7].length) (baseStart_8274857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274857 prefixEnd_8274857 := by exact prefixLift 8274857
  have htrace : WordTrace (prefixWord ++ tailWord_8274857) baseStart_8274857 baseEnd_8274857 := by
    simpa [prefixWord, tailWord_8274857, baseEnd_8274857] using wordTrace_append hprefix tailTrace_8274857
  have hstable : (prefixWord ++ tailWord_8274857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274857).length < 2 ^ (prefixWord ++ tailWord_8274857).sum := by decide
  have hdescent : baseEnd_8274857 < baseStart_8274857 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274867 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 5]
def baseStart_8274867 : Nat := 118140960795 + 8274867 * 2 ^ 59
def prefixEnd_8274867 : Nat := 4983230072969 + 3 ^ 40 * 8274867 * 2
def baseEnd_8274867 : Nat := 4248984123028181278507085

theorem tailTrace_8274867 : CollatzResearch.WordTrace tailWord_8274867 prefixEnd_8274867 4248984123028181278507085 := by
  unfold tailWord_8274867
  simp only [CollatzResearch.WordTrace]
  refine ⟨301809194112577568615342855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201206129408385045743561903 301809194112577568615342855)
  ·
    refine ⟨452713791168866352923014283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301809194112577568615342855 452713791168866352923014283)
    ·
      refine ⟨679070686753299529384521425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452713791168866352923014283 679070686753299529384521425)
      ·
        refine ⟨509303015064974647038391069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 679070686753299529384521425 509303015064974647038391069)
        ·
          refine ⟨190988630649365492639396651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 509303015064974647038391069 190988630649365492639396651)
          ·
            refine ⟨286482945974048238959094977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190988630649365492639396651 286482945974048238959094977)
            ·
              refine ⟨214862209480536179219321233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286482945974048238959094977 214862209480536179219321233)
              ·
                refine ⟨161146657110402134414490925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214862209480536179219321233 161146657110402134414490925)
                ·
                  refine ⟨60429996416400800405434097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161146657110402134414490925 60429996416400800405434097)
                  ·
                    refine ⟨45322497312300600304075573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60429996416400800405434097 45322497312300600304075573)
                    ·
                      refine ⟨4248984123028181278507085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45322497312300600304075573 4248984123028181278507085)
                      ·
                        rfl

theorem cell23_8274867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 5].length) (baseStart_8274867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274867 prefixEnd_8274867 := by exact prefixLift 8274867
  have htrace : WordTrace (prefixWord ++ tailWord_8274867) baseStart_8274867 baseEnd_8274867 := by
    simpa [prefixWord, tailWord_8274867, baseEnd_8274867] using wordTrace_append hprefix tailTrace_8274867
  have hstable : (prefixWord ++ tailWord_8274867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274867).length < 2 ^ (prefixWord ++ tailWord_8274867).sum := by decide
  have hdescent : baseEnd_8274867 < baseStart_8274867 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274955 : List Nat := [1, 1, 1, 1, 6, 3, 3, 2, 1, 4]
def baseStart_8274955 : Nat := 118140960795 + 8274955 * 2 ^ 59
def prefixEnd_8274955 : Nat := 4983230072969 + 3 ^ 40 * 8274955 * 2
def baseEnd_8274955 : Nat := 1416343103108592311402227

theorem tailTrace_8274955 : CollatzResearch.WordTrace tailWord_8274955 prefixEnd_8274955 1416343103108592311402227 := by
  unfold tailWord_8274955
  simp only [CollatzResearch.WordTrace]
  refine ⟨301812403736258759644546319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201208269157505839763030879 301812403736258759644546319)
  ·
    refine ⟨452718605604388139466819479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301812403736258759644546319 452718605604388139466819479)
    ·
      refine ⟨679077908406582209200229219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452718605604388139466819479 679077908406582209200229219)
      ·
        refine ⟨1018616862609873313800343829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679077908406582209200229219 1018616862609873313800343829)
        ·
          refine ⟨47747665434837811584391117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1018616862609873313800343829 47747665434837811584391117)
          ·
            refine ⟨17905374538064179344146669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47747665434837811584391117 17905374538064179344146669)
            ·
              refine ⟨6714515451774067254055001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17905374538064179344146669 6714515451774067254055001)
              ·
                refine ⟨5035886588830550440541251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6714515451774067254055001 5035886588830550440541251)
                ·
                  refine ⟨7553829883245825660811877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5035886588830550440541251 7553829883245825660811877)
                  ·
                    refine ⟨1416343103108592311402227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7553829883245825660811877 1416343103108592311402227)
                    ·
                      rfl

theorem cell23_8274955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2, 1, 4].length) (baseStart_8274955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274955 prefixEnd_8274955 := by exact prefixLift 8274955
  have htrace : WordTrace (prefixWord ++ tailWord_8274955) baseStart_8274955 baseEnd_8274955 := by
    simpa [prefixWord, tailWord_8274955, baseEnd_8274955] using wordTrace_append hprefix tailTrace_8274955
  have hstable : (prefixWord ++ tailWord_8274955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274955).length < 2 ^ (prefixWord ++ tailWord_8274955).sum := by decide
  have hdescent : baseEnd_8274955 < baseStart_8274955 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274968 : List Nat := [2, 1, 2, 3, 2, 4, 2, 1, 6]
def baseStart_8274968 : Nat := 118140960795 + 8274968 * 2 ^ 59
def prefixEnd_8274968 : Nat := 4983230072969 + 3 ^ 40 * 8274968 * 2
def baseEnd_8274968 : Nat := 472115109397142820371569

theorem tailTrace_8274968 : CollatzResearch.WordTrace tailWord_8274968 prefixEnd_8274968 472115109397142820371569 := by
  unfold tailWord_8274968
  simp only [CollatzResearch.WordTrace]
  refine ⟨150906438942605831432384779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201208585256807775243179705 150906438942605831432384779)
  ·
    refine ⟨226359658413908747148577169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150906438942605831432384779 226359658413908747148577169)
    ·
      refine ⟨169769743810431560361432877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226359658413908747148577169 169769743810431560361432877)
      ·
        refine ⟨63663653928911835135537329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169769743810431560361432877 63663653928911835135537329)
        ·
          refine ⟨47747740446683876351652997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63663653928911835135537329 47747740446683876351652997)
          ·
            refine ⟨8952701333753226815934937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47747740446683876351652997 8952701333753226815934937)
            ·
              refine ⟨6714526000314920111951203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8952701333753226815934937 6714526000314920111951203)
              ·
                refine ⟨10071789000472380167926805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6714526000314920111951203 10071789000472380167926805)
                ·
                  refine ⟨472115109397142820371569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10071789000472380167926805 472115109397142820371569)
                  ·
                    rfl

theorem cell23_8274968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 6].length) (baseStart_8274968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274968 prefixEnd_8274968 := by exact prefixLift 8274968
  have htrace : WordTrace (prefixWord ++ tailWord_8274968) baseStart_8274968 baseEnd_8274968 := by
    simpa [prefixWord, tailWord_8274968, baseEnd_8274968] using wordTrace_append hprefix tailTrace_8274968
  have hstable : (prefixWord ++ tailWord_8274968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274968).length < 2 ^ (prefixWord ++ tailWord_8274968).sum := by decide
  have hdescent : baseEnd_8274968 < baseStart_8274968 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274988 : List Nat := [2, 2, 1, 1, 1, 2, 6, 1, 2, 3, 2]
def baseStart_8274988 : Nat := 118140960795 + 8274988 * 2 ^ 59
def prefixEnd_8274988 : Nat := 4983230072969 + 3 ^ 40 * 8274988 * 2
def baseEnd_8274988 : Nat := 4249046254187375305094029

theorem tailTrace_8274988 : CollatzResearch.WordTrace tailWord_8274988 prefixEnd_8274988 4249046254187375305094029 := by
  unfold tailWord_8274988
  simp only [CollatzResearch.WordTrace]
  refine ⟨150906803672569603140248809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201209071563426137520331745 150906803672569603140248809)
  ·
    refine ⟨113180102754427202355186607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150906803672569603140248809 113180102754427202355186607)
    ·
      refine ⟨169770154131640803532779911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113180102754427202355186607 169770154131640803532779911)
      ·
        refine ⟨254655231197461205299169867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169770154131640803532779911 254655231197461205299169867)
        ·
          refine ⟨381982846796191807948754801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254655231197461205299169867 381982846796191807948754801)
          ·
            refine ⟨286487135097143855961566101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381982846796191807948754801 286487135097143855961566101)
            ·
              refine ⟨13429084457678618248198411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 286487135097143855961566101 13429084457678618248198411)
              ·
                refine ⟨20143626686517927372297617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13429084457678618248198411 20143626686517927372297617)
                ·
                  refine ⟨15107720014888445529223213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20143626686517927372297617 15107720014888445529223213)
                  ·
                    refine ⟨5665395005583167073458705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15107720014888445529223213 5665395005583167073458705)
                    ·
                      refine ⟨4249046254187375305094029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5665395005583167073458705 4249046254187375305094029)
                      ·
                        rfl

theorem cell23_8274988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 3, 2].length) (baseStart_8274988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274988 prefixEnd_8274988 := by exact prefixLift 8274988
  have htrace : WordTrace (prefixWord ++ tailWord_8274988) baseStart_8274988 baseEnd_8274988 := by
    simpa [prefixWord, tailWord_8274988, baseEnd_8274988] using wordTrace_append hprefix tailTrace_8274988
  have hstable : (prefixWord ++ tailWord_8274988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274988).length < 2 ^ (prefixWord ++ tailWord_8274988).sum := by decide
  have hdescent : baseEnd_8274988 < baseStart_8274988 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275028 : List Nat := [2, 4, 1, 1, 1, 1, 4, 3, 2, 4]
def baseStart_8275028 : Nat := 118140960795 + 8275028 * 2 ^ 59
def prefixEnd_8275028 : Nat := 4983230072969 + 3 ^ 40 * 8275028 * 2
def baseEnd_8275028 : Nat := 1416355597804518382864615

theorem tailTrace_8275028 : CollatzResearch.WordTrace tailWord_8275028 prefixEnd_8275028 1416355597804518382864615 := by
  unfold tailWord_8275028
  simp only [CollatzResearch.WordTrace]
  refine ⟨150907533132497146555976869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201210044176662862074635825 150907533132497146555976869)
  ·
    refine ⟨28295162462343214979245663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150907533132497146555976869 28295162462343214979245663)
    ·
      refine ⟨42442743693514822468868495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28295162462343214979245663 42442743693514822468868495)
      ·
        refine ⟨63664115540272233703302743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42442743693514822468868495 63664115540272233703302743)
        ·
          refine ⟨95496173310408350554954115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63664115540272233703302743 95496173310408350554954115)
          ·
            refine ⟨143244259965612525832431173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95496173310408350554954115 143244259965612525832431173)
            ·
              refine ⟨26858298743552348593580845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143244259965612525832431173 26858298743552348593580845)
              ·
                refine ⟨10071862028832130722592817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26858298743552348593580845 10071862028832130722592817)
                ·
                  refine ⟨7553896521624098041944613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10071862028832130722592817 7553896521624098041944613)
                  ·
                    refine ⟨1416355597804518382864615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7553896521624098041944613 1416355597804518382864615)
                    ·
                      rfl

theorem cell23_8275028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_8275028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275028 prefixEnd_8275028 := by exact prefixLift 8275028
  have htrace : WordTrace (prefixWord ++ tailWord_8275028) baseStart_8275028 baseEnd_8275028 := by
    simpa [prefixWord, tailWord_8275028, baseEnd_8275028] using wordTrace_append hprefix tailTrace_8275028
  have hstable : (prefixWord ++ tailWord_8275028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275028).length < 2 ^ (prefixWord ++ tailWord_8275028).sum := by decide
  have hdescent : baseEnd_8275028 < baseStart_8275028 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275052 : List Nat := [2, 2, 1, 1, 3, 2, 4, 3, 1, 2, 2]
def baseStart_8275052 : Nat := 118140960795 + 8275052 * 2 ^ 59
def prefixEnd_8275052 : Nat := 4983230072969 + 3 ^ 40 * 8275052 * 2
def baseEnd_8275052 : Nat := 4249079116949263054693735

theorem tailTrace_8275052 : CollatzResearch.WordTrace tailWord_8275052 prefixEnd_8275052 4249079116949263054693735 := by
  unfold tailWord_8275052
  simp only [CollatzResearch.WordTrace]
  refine ⟨150907970808453672605413705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201210627744604896807218273 150907970808453672605413705)
  ·
    refine ⟨113180978106340254454060279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150907970808453672605413705 113180978106340254454060279)
    ·
      refine ⟨169771467159510381681090419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113180978106340254454060279 169771467159510381681090419)
      ·
        refine ⟨254657200739265572521635629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169771467159510381681090419 254657200739265572521635629)
        ·
          refine ⟨95496450277224589695613361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254657200739265572521635629 95496450277224589695613361)
          ·
            refine ⟨71622337707918442271710021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95496450277224589695613361 71622337707918442271710021)
            ·
              refine ⟨13429188320234707925945629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71622337707918442271710021 13429188320234707925945629)
              ·
                refine ⟨5035945620088015472229611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13429188320234707925945629 5035945620088015472229611)
                ·
                  refine ⟨7553918430132023208344417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5035945620088015472229611 7553918430132023208344417)
                  ·
                    refine ⟨5665438822599017406258313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7553918430132023208344417 5665438822599017406258313)
                    ·
                      refine ⟨4249079116949263054693735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5665438822599017406258313 4249079116949263054693735)
                      ·
                        rfl

theorem cell23_8275052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3, 1, 2, 2].length) (baseStart_8275052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275052 prefixEnd_8275052 := by exact prefixLift 8275052
  have htrace : WordTrace (prefixWord ++ tailWord_8275052) baseStart_8275052 baseEnd_8275052 := by
    simpa [prefixWord, tailWord_8275052, baseEnd_8275052] using wordTrace_append hprefix tailTrace_8275052
  have hstable : (prefixWord ++ tailWord_8275052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275052).length < 2 ^ (prefixWord ++ tailWord_8275052).sum := by decide
  have hdescent : baseEnd_8275052 < baseStart_8275052 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275068 : List Nat := [2, 2, 2, 1, 1, 3, 3, 1, 4, 1, 3]
def baseStart_8275068 : Nat := 118140960795 + 8275068 * 2 ^ 59
def prefixEnd_8275068 : Nat := 4983230072969 + 3 ^ 40 * 8275068 * 2
def baseEnd_8275068 : Nat := 4249087332639734992093661

theorem tailTrace_8275068 : CollatzResearch.WordTrace tailWord_8275068 prefixEnd_8275068 4249087332639734992093661 := by
  unfold tailWord_8275068
  simp only [CollatzResearch.WordTrace]
  refine ⟨150908262592424689971704929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201211016789899586628939905 150908262592424689971704929)
  ·
    refine ⟨113181196944318517478778697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150908262592424689971704929 113181196944318517478778697)
    ·
      refine ⟨84885897708238888109084023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113181196944318517478778697 84885897708238888109084023)
      ·
        refine ⟨127328846562358332163626035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84885897708238888109084023 127328846562358332163626035)
        ·
          refine ⟨190993269843537498245439053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127328846562358332163626035 190993269843537498245439053)
          ·
            refine ⟨71622476191326561842039645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190993269843537498245439053 71622476191326561842039645)
            ·
              refine ⟨26858428571747460690764867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71622476191326561842039645 26858428571747460690764867)
              ·
                refine ⟨40287642857621191036147301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26858428571747460690764867 40287642857621191036147301)
                ·
                  refine ⟨7553933035803973319277619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40287642857621191036147301 7553933035803973319277619)
                  ·
                    refine ⟨11330899553705959978916429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7553933035803973319277619 11330899553705959978916429)
                    ·
                      refine ⟨4249087332639734992093661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11330899553705959978916429 4249087332639734992093661)
                      ·
                        rfl

theorem cell23_8275068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_8275068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275068 prefixEnd_8275068 := by exact prefixLift 8275068
  have htrace : WordTrace (prefixWord ++ tailWord_8275068) baseStart_8275068 baseEnd_8275068 := by
    simpa [prefixWord, tailWord_8275068, baseEnd_8275068] using wordTrace_append hprefix tailTrace_8275068
  have hstable : (prefixWord ++ tailWord_8275068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275068).length < 2 ^ (prefixWord ++ tailWord_8275068).sum := by decide
  have hdescent : baseEnd_8275068 < baseStart_8275068 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275095 : List Nat := [1, 1, 3, 3, 3, 1, 1, 4, 1, 3, 2]
def baseStart_8275095 : Nat := 118140960795 + 8275095 * 2 ^ 59
def prefixEnd_8275095 : Nat := 4983230072969 + 3 ^ 40 * 8275095 * 2
def baseEnd_8275095 : Nat := 4249101196617406386456037

theorem tailTrace_8275095 : CollatzResearch.WordTrace tailWord_8275095 prefixEnd_8275095 4249101196617406386456037 := by
  unfold tailWord_8275095
  simp only [CollatzResearch.WordTrace]
  refine ⟨301817509955751563554642739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201211673303834375703095159 301817509955751563554642739)
  ·
    refine ⟨452726264933627345331964109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301817509955751563554642739 452726264933627345331964109)
    ·
      refine ⟨169772349350110254499486541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452726264933627345331964109 169772349350110254499486541)
      ·
        refine ⟨63664631006291345437307453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169772349350110254499486541 63664631006291345437307453)
        ·
          refine ⟨23874236627359254538990295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63664631006291345437307453 23874236627359254538990295)
          ·
            refine ⟨35811354941038881808485443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23874236627359254538990295 35811354941038881808485443)
            ·
              refine ⟨53717032411558322712728165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35811354941038881808485443 53717032411558322712728165)
              ·
                refine ⟨10071943577167185508636531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53717032411558322712728165 10071943577167185508636531)
                ·
                  refine ⟨15107915365750778262954797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10071943577167185508636531 15107915365750778262954797)
                  ·
                    refine ⟨5665468262156541848608049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15107915365750778262954797 5665468262156541848608049)
                    ·
                      refine ⟨4249101196617406386456037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5665468262156541848608049 4249101196617406386456037)
                      ·
                        rfl

theorem cell23_8275095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_8275095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275095 prefixEnd_8275095 := by exact prefixLift 8275095
  have htrace : WordTrace (prefixWord ++ tailWord_8275095) baseStart_8275095 baseEnd_8275095 := by
    simpa [prefixWord, tailWord_8275095, baseEnd_8275095] using wordTrace_append hprefix tailTrace_8275095
  have hstable : (prefixWord ++ tailWord_8275095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275095).length < 2 ^ (prefixWord ++ tailWord_8275095).sum := by decide
  have hdescent : baseEnd_8275095 < baseStart_8275095 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275141 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 1, 5, 3]
def baseStart_8275141 : Nat := 118140960795 + 8275141 * 2 ^ 59
def prefixEnd_8275141 : Nat := 4983230072969 + 3 ^ 40 * 8275141 * 2
def baseEnd_8275141 : Nat := 4249124816727513206480825

theorem tailTrace_8275141 : CollatzResearch.WordTrace tailWord_8275141 prefixEnd_8275141 4249124816727513206480825 := by
  unfold tailWord_8275141
  simp only [CollatzResearch.WordTrace]
  refine ⟨301819187713584913410817277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201212791809056608940544851 301819187713584913410817277)
  ·
    refine ⟨113182195392594342529056479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301819187713584913410817277 113182195392594342529056479)
    ·
      refine ⟨169773293088891513793584719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113182195392594342529056479 169773293088891513793584719)
      ·
        refine ⟨254659939633337270690377079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169773293088891513793584719 254659939633337270690377079)
        ·
          refine ⟨381989909450005906035565619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254659939633337270690377079 381989909450005906035565619)
          ·
            refine ⟨572984864175008859053348429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381989909450005906035565619 572984864175008859053348429)
            ·
              refine ⟨214869324065628322145005661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 572984864175008859053348429 214869324065628322145005661)
              ·
                refine ⟨80575996524610620804377123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214869324065628322145005661 80575996524610620804377123)
                ·
                  refine ⟨120863994786915931206565685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80575996524610620804377123 120863994786915931206565685)
                  ·
                    refine ⟨11330999511273368550615533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120863994786915931206565685 11330999511273368550615533)
                    ·
                      refine ⟨4249124816727513206480825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11330999511273368550615533 4249124816727513206480825)
                      ·
                        rfl

theorem cell23_8275141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 5, 3].length) (baseStart_8275141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275141 prefixEnd_8275141 := by exact prefixLift 8275141
  have htrace : WordTrace (prefixWord ++ tailWord_8275141) baseStart_8275141 baseEnd_8275141 := by
    simpa [prefixWord, tailWord_8275141, baseEnd_8275141] using wordTrace_append hprefix tailTrace_8275141
  have hstable : (prefixWord ++ tailWord_8275141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275141).length < 2 ^ (prefixWord ++ tailWord_8275141).sum := by decide
  have hdescent : baseEnd_8275141 < baseStart_8275141 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275178 : List Nat := [3, 1, 3, 1, 1, 3, 2, 2, 2, 5]
def baseStart_8275178 : Nat := 118140960795 + 8275178 * 2 ^ 59
def prefixEnd_8275178 : Nat := 4983230072969 + 3 ^ 40 * 8275178 * 2
def baseEnd_8275178 : Nat := 1416381271837243187239385

theorem tailTrace_8275178 : CollatzResearch.WordTrace tailWord_8275178 prefixEnd_8275178 1416381271837243187239385 := by
  unfold tailWord_8275178
  simp only [CollatzResearch.WordTrace]
  refine ⟨75455134303612717182478547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201213691476300579153276125 75455134303612717182478547)
  ·
    refine ⟨113182701455419075773717821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75455134303612717182478547 113182701455419075773717821)
    ·
      refine ⟨42443513045782153415144183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113182701455419075773717821 42443513045782153415144183)
      ·
        refine ⟨63665269568673230122716275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42443513045782153415144183 63665269568673230122716275)
        ·
          refine ⟨95497904353009845184074413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63665269568673230122716275 95497904353009845184074413)
          ·
            refine ⟨35811714132378691944027905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95497904353009845184074413 35811714132378691944027905)
            ·
              refine ⟨26858785599284018958020929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35811714132378691944027905 26858785599284018958020929)
              ·
                refine ⟨20144089199463014218515697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26858785599284018958020929 20144089199463014218515697)
                ·
                  refine ⟨15108066899597260663886773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20144089199463014218515697 15108066899597260663886773)
                  ·
                    refine ⟨1416381271837243187239385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15108066899597260663886773 1416381271837243187239385)
                    ·
                      rfl

theorem cell23_8275178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_8275178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275178 prefixEnd_8275178 := by exact prefixLift 8275178
  have htrace : WordTrace (prefixWord ++ tailWord_8275178) baseStart_8275178 baseEnd_8275178 := by
    simpa [prefixWord, tailWord_8275178, baseEnd_8275178] using wordTrace_append hprefix tailTrace_8275178
  have hstable : (prefixWord ++ tailWord_8275178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275178).length < 2 ^ (prefixWord ++ tailWord_8275178).sum := by decide
  have hdescent : baseEnd_8275178 < baseStart_8275178 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275221 : List Nat := [1, 3, 2, 1, 2, 1, 1, 4, 8]
def baseStart_8275221 : Nat := 118140960795 + 8275221 * 2 ^ 59
def prefixEnd_8275221 : Nat := 4983230072969 + 3 ^ 40 * 8275221 * 2
def baseEnd_8275221 : Nat := 472129543908874765942273

theorem tailTrace_8275221 : CollatzResearch.WordTrace tailWord_8275221 prefixEnd_8275221 472129543908874765942273 := by
  unfold tailWord_8275221
  simp only [CollatzResearch.WordTrace]
  refine ⟨301822105553295087073729517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201214737035530058049153011 301822105553295087073729517)
  ·
    refine ⟨113183289582485657652648569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301822105553295087073729517 113183289582485657652648569)
    ·
      refine ⟨84887467186864243239486427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113183289582485657652648569 84887467186864243239486427)
      ·
        refine ⟨127331200780296364859229641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84887467186864243239486427 127331200780296364859229641)
        ·
          refine ⟨95498400585222273644422231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127331200780296364859229641 95498400585222273644422231)
          ·
            refine ⟨143247600877833410466633347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95498400585222273644422231 143247600877833410466633347)
            ·
              refine ⟨214871401316750115699950021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143247600877833410466633347 214871401316750115699950021)
              ·
                refine ⟨40288387746890646693740629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214871401316750115699950021 40288387746890646693740629)
                ·
                  refine ⟨472129543908874765942273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40288387746890646693740629 472129543908874765942273)
                  ·
                    rfl

theorem cell23_8275221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 8].length) (baseStart_8275221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275221 prefixEnd_8275221 := by exact prefixLift 8275221
  have htrace : WordTrace (prefixWord ++ tailWord_8275221) baseStart_8275221 baseEnd_8275221 := by
    simpa [prefixWord, tailWord_8275221, baseEnd_8275221] using wordTrace_append hprefix tailTrace_8275221
  have hstable : (prefixWord ++ tailWord_8275221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275221).length < 2 ^ (prefixWord ++ tailWord_8275221).sum := by decide
  have hdescent : baseEnd_8275221 < baseStart_8275221 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275242 : List Nat := [3, 1, 4, 2, 1, 2, 2, 1, 3, 4]
def baseStart_8275242 : Nat := 118140960795 + 8275242 * 2 ^ 59
def prefixEnd_8275242 : Nat := 4983230072969 + 3 ^ 40 * 8275242 * 2
def baseEnd_8275242 : Nat := 1416392226091205770439287

theorem tailTrace_8275242 : CollatzResearch.WordTrace tailWord_8275242 prefixEnd_8275242 1416392226091205770439287 := by
  unfold tailWord_8275242
  simp only [CollatzResearch.WordTrace]
  refine ⟨75455717871554751915060995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201215247657479338440162653 75455717871554751915060995)
  ·
    refine ⟨113183576807332127872591493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75455717871554751915060995 113183576807332127872591493)
    ·
      refine ⟨21221920651374773976110905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113183576807332127872591493 21221920651374773976110905)
      ·
        refine ⟨15916440488531080482083179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21221920651374773976110905 15916440488531080482083179)
        ·
          refine ⟨23874660732796620723124769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15916440488531080482083179 23874660732796620723124769)
          ·
            refine ⟨17905995549597465542343577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23874660732796620723124769 17905995549597465542343577)
            ·
              refine ⟨13429496662198099156757683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17905995549597465542343577 13429496662198099156757683)
              ·
                refine ⟨20144244993297148735136525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13429496662198099156757683 20144244993297148735136525)
                ·
                  refine ⟨7554091872486430775676197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20144244993297148735136525 7554091872486430775676197)
                  ·
                    refine ⟨1416392226091205770439287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7554091872486430775676197 1416392226091205770439287)
                    ·
                      rfl

theorem cell23_8275242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_8275242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275242 prefixEnd_8275242 := by exact prefixLift 8275242
  have htrace : WordTrace (prefixWord ++ tailWord_8275242) baseStart_8275242 baseEnd_8275242 := by
    simpa [prefixWord, tailWord_8275242, baseEnd_8275242] using wordTrace_append hprefix tailTrace_8275242
  have hstable : (prefixWord ++ tailWord_8275242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275242).length < 2 ^ (prefixWord ++ tailWord_8275242).sum := by decide
  have hdescent : baseEnd_8275242 < baseStart_8275242 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275285 : List Nat := [1, 3, 2, 2, 3, 1, 2, 3, 1, 5]
def baseStart_8275285 : Nat := 118140960795 + 8275285 * 2 ^ 59
def prefixEnd_8275285 : Nat := 4983230072969 + 3 ^ 40 * 8275285 * 2
def baseEnd_8275285 : Nat := 1416399585980586881026721

theorem tailTrace_8275285 : CollatzResearch.WordTrace tailWord_8275285 prefixEnd_8275285 1416399585980586881026721 := by
  unfold tailWord_8275285
  simp only [CollatzResearch.WordTrace]
  refine ⟨301824439825063226004059309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201216293216708817336039539 301824439825063226004059309)
  ·
    refine ⟨113184164934398709751522241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301824439825063226004059309 113184164934398709751522241)
    ·
      refine ⟨84888123700799032313641681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113184164934398709751522241 84888123700799032313641681)
      ·
        refine ⟨63666092775599274235231261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84888123700799032313641681 63666092775599274235231261)
        ·
          refine ⟨23874784790849727838211723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63666092775599274235231261 23874784790849727838211723)
          ·
            refine ⟨35812177186274591757317585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23874784790849727838211723 35812177186274591757317585)
            ·
              refine ⟨26859132889705943817988189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35812177186274591757317585 26859132889705943817988189)
              ·
                refine ⟨10072174833639728931745571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26859132889705943817988189 10072174833639728931745571)
                ·
                  refine ⟨15108262250459593397618357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10072174833639728931745571 15108262250459593397618357)
                  ·
                    refine ⟨1416399585980586881026721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15108262250459593397618357 1416399585980586881026721)
                    ·
                      rfl

theorem cell23_8275285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_8275285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275285 prefixEnd_8275285 := by exact prefixLift 8275285
  have htrace : WordTrace (prefixWord ++ tailWord_8275285) baseStart_8275285 baseEnd_8275285 := by
    simpa [prefixWord, tailWord_8275285, baseEnd_8275285] using wordTrace_append hprefix tailTrace_8275285
  have hstable : (prefixWord ++ tailWord_8275285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275285).length < 2 ^ (prefixWord ++ tailWord_8275285).sum := by decide
  have hdescent : baseEnd_8275285 < baseStart_8275285 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275293 : List Nat := [1, 4, 5, 1, 2, 1, 1, 1, 3, 4]
def baseStart_8275293 : Nat := 118140960795 + 8275293 * 2 ^ 59
def prefixEnd_8275293 : Nat := 4983230072969 + 3 ^ 40 * 8275293 * 2
def baseEnd_8275293 : Nat := 1416400955262332203926709

theorem tailTrace_8275293 : CollatzResearch.WordTrace tailWord_8275293 prefixEnd_8275293 1416400955262332203926709 := by
  unfold tailWord_8275293
  simp only [CollatzResearch.WordTrace]
  refine ⟨301824731609034243370350533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201216487739356162246900355 301824731609034243370350533)
  ·
    refine ⟨56592137176693920631940725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301824731609034243370350533 56592137176693920631940725)
    ·
      refine ⟨5305512860315055059244443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56592137176693920631940725 5305512860315055059244443)
      ·
        refine ⟨7958269290472582588866665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5305512860315055059244443 7958269290472582588866665)
        ·
          refine ⟨5968701967854436941649999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7958269290472582588866665 5968701967854436941649999)
          ·
            refine ⟨8953052951781655412474999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5968701967854436941649999 8953052951781655412474999)
            ·
              refine ⟨13429579427672483118712499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8953052951781655412474999 13429579427672483118712499)
              ·
                refine ⟨20144369141508724678068749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13429579427672483118712499 20144369141508724678068749)
                ·
                  refine ⟨7554138428065771754275781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20144369141508724678068749 7554138428065771754275781)
                  ·
                    refine ⟨1416400955262332203926709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7554138428065771754275781 1416400955262332203926709)
                    ·
                      rfl

theorem cell23_8275293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_8275293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275293 prefixEnd_8275293 := by exact prefixLift 8275293
  have htrace : WordTrace (prefixWord ++ tailWord_8275293) baseStart_8275293 baseEnd_8275293 := by
    simpa [prefixWord, tailWord_8275293, baseEnd_8275293] using wordTrace_append hprefix tailTrace_8275293
  have hstable : (prefixWord ++ tailWord_8275293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275293).length < 2 ^ (prefixWord ++ tailWord_8275293).sum := by decide
  have hdescent : baseEnd_8275293 < baseStart_8275293 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275325 : List Nat := [1, 4, 1, 1, 2, 2, 3, 1, 3, 2, 3]
def baseStart_8275325 : Nat := 118140960795 + 8275325 * 2 ^ 59
def prefixEnd_8275325 : Nat := 4983230072969 + 3 ^ 40 * 8275325 * 2
def baseEnd_8275325 : Nat := 4249219297167940486579979

theorem tailTrace_8275325 : CollatzResearch.WordTrace tailWord_8275325 prefixEnd_8275325 4249219297167940486579979 := by
  unfold tailWord_8275325
  simp only [CollatzResearch.WordTrace]
  refine ⟨301825898744918312835515429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201217265829945541890343619 301825898744918312835515429)
  ·
    refine ⟨56592356014672183656659143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301825898744918312835515429 56592356014672183656659143)
    ·
      refine ⟨84888534022008275484988715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56592356014672183656659143 84888534022008275484988715)
      ·
        refine ⟨127332801033012413227483073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84888534022008275484988715 127332801033012413227483073)
        ·
          refine ⟨95499600774759309920612305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127332801033012413227483073 95499600774759309920612305)
          ·
            refine ⟨71624700581069482440459229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95499600774759309920612305 71624700581069482440459229)
            ·
              refine ⟨26859262717901055915172211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71624700581069482440459229 26859262717901055915172211)
              ·
                refine ⟨40288894076851583872758317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26859262717901055915172211 40288894076851583872758317)
                ·
                  refine ⟨15108335278819343952284369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40288894076851583872758317 15108335278819343952284369)
                  ·
                    refine ⟨11331251459114507964213277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15108335278819343952284369 11331251459114507964213277)
                    ·
                      refine ⟨4249219297167940486579979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11331251459114507964213277 4249219297167940486579979)
                      ·
                        rfl

theorem cell23_8275325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_8275325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275325 prefixEnd_8275325 := by exact prefixLift 8275325
  have htrace : WordTrace (prefixWord ++ tailWord_8275325) baseStart_8275325 baseEnd_8275325 := by
    simpa [prefixWord, tailWord_8275325, baseEnd_8275325] using wordTrace_append hprefix tailTrace_8275325
  have hstable : (prefixWord ++ tailWord_8275325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275325).length < 2 ^ (prefixWord ++ tailWord_8275325).sum := by decide
  have hdescent : baseEnd_8275325 < baseStart_8275325 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275335 : List Nat := [1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 4]
def baseStart_8275335 : Nat := 118140960795 + 8275335 * 2 ^ 59
def prefixEnd_8275335 : Nat := 4983230072969 + 3 ^ 40 * 8275335 * 2
def baseEnd_8275335 : Nat := 4249224431974485447454933

theorem tailTrace_8275335 : CollatzResearch.WordTrace tailWord_8275335 prefixEnd_8275335 4249224431974485447454933 := by
  unfold tailWord_8275335
  simp only [CollatzResearch.WordTrace]
  refine ⟨301826263474882084543379459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201217508983254723028919639 301826263474882084543379459)
  ·
    refine ⟨452739395212323126815069189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301826263474882084543379459 452739395212323126815069189)
    ·
      refine ⟨84888636602310586277825473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 452739395212323126815069189 84888636602310586277825473)
      ·
        refine ⟨63666477451732939708369105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84888636602310586277825473 63666477451732939708369105)
        ·
          refine ⟨47749858088799704781276829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63666477451732939708369105 47749858088799704781276829)
          ·
            refine ⟨17906196783299889292978811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47749858088799704781276829 17906196783299889292978811)
            ·
              refine ⟨26859295174949833939468217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17906196783299889292978811 26859295174949833939468217)
              ·
                refine ⟨20144471381212375454601163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26859295174949833939468217 20144471381212375454601163)
                ·
                  refine ⟨30216707071818563181901745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20144471381212375454601163 30216707071818563181901745)
                  ·
                    refine ⟨22662530303863922386426309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30216707071818563181901745 22662530303863922386426309)
                    ·
                      refine ⟨4249224431974485447454933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22662530303863922386426309 4249224431974485447454933)
                      ·
                        rfl

theorem cell23_8275335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_8275335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275335 prefixEnd_8275335 := by exact prefixLift 8275335
  have htrace : WordTrace (prefixWord ++ tailWord_8275335) baseStart_8275335 baseEnd_8275335 := by
    simpa [prefixWord, tailWord_8275335, baseEnd_8275335] using wordTrace_append hprefix tailTrace_8275335
  have hstable : (prefixWord ++ tailWord_8275335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275335).length < 2 ^ (prefixWord ++ tailWord_8275335).sum := by decide
  have hdescent : baseEnd_8275335 < baseStart_8275335 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275339 : List Nat := [1, 1, 1, 1, 4, 3, 2, 5, 1, 2, 2]
def baseStart_8275339 : Nat := 118140960795 + 8275339 * 2 ^ 59
def prefixEnd_8275339 : Nat := 4983230072969 + 3 ^ 40 * 8275339 * 2
def baseEnd_8275339 : Nat := 4249226485897103431804915

theorem tailTrace_8275339 : CollatzResearch.WordTrace tailWord_8275339 prefixEnd_8275339 4249226485897103431804915 := by
  unfold tailWord_8275339
  simp only [CollatzResearch.WordTrace]
  refine ⟨301826409366867593226525071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201217606244578395484350047 301826409366867593226525071)
  ·
    refine ⟨452739614050301389839787607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301826409366867593226525071 452739614050301389839787607)
    ·
      refine ⟨679109421075452084759681411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452739614050301389839787607 679109421075452084759681411)
      ·
        refine ⟨1018664131613178127139522117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679109421075452084759681411 1018664131613178127139522117)
        ·
          refine ⟨190999524677470898838660397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1018664131613178127139522117 190999524677470898838660397)
          ·
            refine ⟨71624821754051587064497649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190999524677470898838660397 71624821754051587064497649)
            ·
              refine ⟨53718616315538690298373237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71624821754051587064497649 53718616315538690298373237)
              ·
                refine ⟨5036120279581752215472491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53718616315538690298373237 5036120279581752215472491)
                ·
                  refine ⟨7554180419372628323208737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5036120279581752215472491 7554180419372628323208737)
                  ·
                    refine ⟨5665635314529471242406553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7554180419372628323208737 5665635314529471242406553)
                    ·
                      refine ⟨4249226485897103431804915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5665635314529471242406553 4249226485897103431804915)
                      ·
                        rfl

theorem cell23_8275339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5, 1, 2, 2].length) (baseStart_8275339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275339 prefixEnd_8275339 := by exact prefixLift 8275339
  have htrace : WordTrace (prefixWord ++ tailWord_8275339) baseStart_8275339 baseEnd_8275339 := by
    simpa [prefixWord, tailWord_8275339, baseEnd_8275339] using wordTrace_append hprefix tailTrace_8275339
  have hstable : (prefixWord ++ tailWord_8275339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275339).length < 2 ^ (prefixWord ++ tailWord_8275339).sum := by decide
  have hdescent : baseEnd_8275339 < baseStart_8275339 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275372 : List Nat := [2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 3]
def baseStart_8275372 : Nat := 118140960795 + 8275372 * 2 ^ 59
def prefixEnd_8275372 : Nat := 4983230072969 + 3 ^ 40 * 8275372 * 2
def baseEnd_8275372 : Nat := 4249243430758701802692263

theorem tailTrace_8275372 : CollatzResearch.WordTrace tailWord_8275372 prefixEnd_8275372 4249243430758701802692263 := by
  unfold tailWord_8275372
  simp only [CollatzResearch.WordTrace]
  refine ⟨150913806487874019931238185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201218408650498693241650913 150913806487874019931238185)
  ·
    refine ⟨113185354865905514948428639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150913806487874019931238185 113185354865905514948428639)
    ·
      refine ⟨169778032298858272422642959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113185354865905514948428639 169778032298858272422642959)
      ·
        refine ⟨254667048448287408633964439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169778032298858272422642959 254667048448287408633964439)
        ·
          refine ⟨382000572672431112950946659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254667048448287408633964439 382000572672431112950946659)
          ·
            refine ⟨573000859008646669426419989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382000572672431112950946659 573000859008646669426419989)
            ·
              refine ⟨26859415266030312629363437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 573000859008646669426419989 26859415266030312629363437)
              ·
                refine ⟨10072280724761367236011289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26859415266030312629363437 10072280724761367236011289)
                ·
                  refine ⟨7554210543571025427008467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10072280724761367236011289 7554210543571025427008467)
                  ·
                    refine ⟨11331315815356538140512701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7554210543571025427008467 11331315815356538140512701)
                    ·
                      refine ⟨4249243430758701802692263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11331315815356538140512701 4249243430758701802692263)
                      ·
                        rfl

theorem cell23_8275372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 3].length) (baseStart_8275372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275372 prefixEnd_8275372 := by exact prefixLift 8275372
  have htrace : WordTrace (prefixWord ++ tailWord_8275372) baseStart_8275372 baseEnd_8275372 := by
    simpa [prefixWord, tailWord_8275372, baseEnd_8275372] using wordTrace_append hprefix tailTrace_8275372
  have hstable : (prefixWord ++ tailWord_8275372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275372).length < 2 ^ (prefixWord ++ tailWord_8275372).sum := by decide
  have hdescent : baseEnd_8275372 < baseStart_8275372 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275408 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 4]
def baseStart_8275408 : Nat := 118140960795 + 8275408 * 2 ^ 59
def prefixEnd_8275408 : Nat := 4983230072969 + 3 ^ 40 * 8275408 * 2
def baseEnd_8275408 : Nat := 4249261916062263661842097

theorem tailTrace_8275408 : CollatzResearch.WordTrace tailWord_8275408 prefixEnd_8275408 4249261916062263661842097 := by
  unfold tailWord_8275408
  simp only [CollatzResearch.WordTrace]
  refine ⟨150914463001808809005393439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201219284002411745340524585 150914463001808809005393439)
  ·
    refine ⟨226371694502713213508090159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150914463001808809005393439 226371694502713213508090159)
    ·
      refine ⟨339557541754069820262135239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226371694502713213508090159 339557541754069820262135239)
      ·
        refine ⟨509336312631104730393202859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339557541754069820262135239 509336312631104730393202859)
        ·
          refine ⟨764004468946657095589804289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509336312631104730393202859 764004468946657095589804289)
          ·
            refine ⟨573003351709992821692353217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 764004468946657095589804289 573003351709992821692353217)
            ·
              refine ⟨429752513782494616269264913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 573003351709992821692353217 429752513782494616269264913)
              ·
                refine ⟨322314385336870962201948685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 429752513782494616269264913 322314385336870962201948685)
                ·
                  refine ⟨120867894501326610825730757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322314385336870962201948685 120867894501326610825730757)
                  ·
                    refine ⟨22662730218998739529824517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120867894501326610825730757 22662730218998739529824517)
                    ·
                      refine ⟨4249261916062263661842097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22662730218998739529824517 4249261916062263661842097)
                      ·
                        rfl

theorem cell23_8275408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 4].length) (baseStart_8275408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275408 prefixEnd_8275408 := by exact prefixLift 8275408
  have htrace : WordTrace (prefixWord ++ tailWord_8275408) baseStart_8275408 baseEnd_8275408 := by
    simpa [prefixWord, tailWord_8275408, baseEnd_8275408] using wordTrace_append hprefix tailTrace_8275408
  have hstable : (prefixWord ++ tailWord_8275408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275408).length < 2 ^ (prefixWord ++ tailWord_8275408).sum := by decide
  have hdescent : baseEnd_8275408 < baseStart_8275408 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275425 : List Nat := [1, 2, 3, 1, 2, 3, 2, 1, 2, 2, 4]
def baseStart_8275425 : Nat := 118140960795 + 8275425 * 2 ^ 59
def prefixEnd_8275425 : Nat := 4983230072969 + 3 ^ 40 * 8275425 * 2
def baseEnd_8275425 : Nat := 4249270645233390095329519

theorem tailTrace_8275425 : CollatzResearch.WordTrace tailWord_8275425 prefixEnd_8275425 4249270645233390095329519 := by
  unfold tailWord_8275425
  simp only [CollatzResearch.WordTrace]
  refine ⟨301829546044556029914155729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201219697363037353276103819 301829546044556029914155729)
  ·
    refine ⟨226372159533417022435616797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301829546044556029914155729 226372159533417022435616797)
    ·
      refine ⟨84889559825031383413356299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226372159533417022435616797 84889559825031383413356299)
      ·
        refine ⟨127334339737547075120034449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84889559825031383413356299 127334339737547075120034449)
        ·
          refine ⟨95500754803160306340025837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127334339737547075120034449 95500754803160306340025837)
          ·
            refine ⟨35812783051185114877509689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95500754803160306340025837 35812783051185114877509689)
            ·
              refine ⟨26859587288388836158132267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35812783051185114877509689 26859587288388836158132267)
              ·
                refine ⟨40289380932583254237198401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26859587288388836158132267 40289380932583254237198401)
                ·
                  refine ⟨30217035699437440677898801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40289380932583254237198401 30217035699437440677898801)
                  ·
                    refine ⟨22662776774578080508424101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30217035699437440677898801 22662776774578080508424101)
                    ·
                      refine ⟨4249270645233390095329519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22662776774578080508424101 4249270645233390095329519)
                      ·
                        rfl

theorem cell23_8275425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_8275425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275425 prefixEnd_8275425 := by exact prefixLift 8275425
  have htrace : WordTrace (prefixWord ++ tailWord_8275425) baseStart_8275425 baseEnd_8275425 := by
    simpa [prefixWord, tailWord_8275425, baseEnd_8275425] using wordTrace_append hprefix tailTrace_8275425
  have hstable : (prefixWord ++ tailWord_8275425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275425).length < 2 ^ (prefixWord ++ tailWord_8275425).sum := by decide
  have hdescent : baseEnd_8275425 < baseStart_8275425 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275428 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 1, 1, 9]
def baseStart_8275428 : Nat := 118140960795 + 8275428 * 2 ^ 59
def prefixEnd_8275428 : Nat := 4983230072969 + 3 ^ 40 * 8275428 * 2
def baseEnd_8275428 : Nat := 4249272185675353583592005

theorem tailTrace_8275428 : CollatzResearch.WordTrace tailWord_8275428 prefixEnd_8275428 4249272185675353583592005 := by
  unfold tailWord_8275428
  simp only [CollatzResearch.WordTrace]
  refine ⟨150914827731772580713257469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201219770309030107617676625 150914827731772580713257469)
  ·
    refine ⟨56593060399414717767471551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150914827731772580713257469 56593060399414717767471551)
    ·
      refine ⟨84889590599122076651207327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56593060399414717767471551 84889590599122076651207327)
      ·
        refine ⟨127334385898683114976810991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84889590599122076651207327 127334385898683114976810991)
        ·
          refine ⟨191001578848024672465216487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127334385898683114976810991 191001578848024672465216487)
          ·
            refine ⟨286502368272037008697824731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191001578848024672465216487 286502368272037008697824731)
            ·
              refine ⟨429753552408055513046737097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286502368272037008697824731 429753552408055513046737097)
              ·
                refine ⟨322315164306041634785052823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 429753552408055513046737097 322315164306041634785052823)
                ·
                  refine ⟨483472746459062452177579235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322315164306041634785052823 483472746459062452177579235)
                  ·
                    refine ⟨725209119688593678266368853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 483472746459062452177579235 725209119688593678266368853)
                    ·
                      refine ⟨4249272185675353583592005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 725209119688593678266368853 4249272185675353583592005)
                      ·
                        rfl

theorem cell23_8275428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_8275428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275428 prefixEnd_8275428 := by exact prefixLift 8275428
  have htrace : WordTrace (prefixWord ++ tailWord_8275428) baseStart_8275428 baseEnd_8275428 := by
    simpa [prefixWord, tailWord_8275428, baseEnd_8275428] using wordTrace_append hprefix tailTrace_8275428
  have hstable : (prefixWord ++ tailWord_8275428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275428).length < 2 ^ (prefixWord ++ tailWord_8275428).sum := by decide
  have hdescent : baseEnd_8275428 < baseStart_8275428 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275429 : List Nat := [1, 3, 1, 5, 1, 1, 3, 1, 1, 4, 2]
def baseStart_8275429 : Nat := 118140960795 + 8275429 * 2 ^ 59
def prefixEnd_8275429 : Nat := 4983230072969 + 3 ^ 40 * 8275429 * 2
def baseEnd_8275429 : Nat := 4249272699156008079679501

theorem tailTrace_8275429 : CollatzResearch.WordTrace tailWord_8275429 prefixEnd_8275429 4249272699156008079679501 := by
  unfold tailWord_8275429
  simp only [CollatzResearch.WordTrace]
  refine ⟨301829691936541538597301341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201219794624361025731534227 301829691936541538597301341)
  ·
    refine ⟨113186134476203076973988003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301829691936541538597301341 113186134476203076973988003)
    ·
      refine ⟨169779201714304615460982005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113186134476203076973988003 169779201714304615460982005)
      ·
        refine ⟨15916800160716057699467063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169779201714304615460982005 15916800160716057699467063)
        ·
          refine ⟨23875200241074086549200595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15916800160716057699467063 23875200241074086549200595)
          ·
            refine ⟨35812800361611129823800893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23875200241074086549200595 35812800361611129823800893)
            ·
              refine ⟨13429800135604173683925335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35812800361611129823800893 13429800135604173683925335)
              ·
                refine ⟨20144700203406260525888003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13429800135604173683925335 20144700203406260525888003)
                ·
                  refine ⟨30217050305109390788832005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20144700203406260525888003 30217050305109390788832005)
                  ·
                    refine ⟨5665696932208010772906001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30217050305109390788832005 5665696932208010772906001)
                    ·
                      refine ⟨4249272699156008079679501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5665696932208010772906001 4249272699156008079679501)
                      ·
                        rfl

theorem cell23_8275429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_8275429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275429 prefixEnd_8275429 := by exact prefixLift 8275429
  have htrace : WordTrace (prefixWord ++ tailWord_8275429) baseStart_8275429 baseEnd_8275429 := by
    simpa [prefixWord, tailWord_8275429, baseEnd_8275429] using wordTrace_append hprefix tailTrace_8275429
  have hstable : (prefixWord ++ tailWord_8275429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275429).length < 2 ^ (prefixWord ++ tailWord_8275429).sum := by decide
  have hdescent : baseEnd_8275429 < baseStart_8275429 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275452 : List Nat := [2, 2, 2, 1, 2, 1, 5, 3, 5]
def baseStart_8275452 : Nat := 118140960795 + 8275452 * 2 ^ 59
def prefixEnd_8275452 : Nat := 4983230072969 + 3 ^ 40 * 8275452 * 2
def baseEnd_8275452 : Nat := 472142723245673498854655

theorem tailTrace_8275452 : CollatzResearch.WordTrace tailWord_8275452 prefixEnd_8275452 472142723245673498854655 := by
  unfold tailWord_8275452
  simp only [CollatzResearch.WordTrace]
  refine ⟨150915265407729106762694305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201220353876972142350259073 150915265407729106762694305)
  ·
    refine ⟨113186449055796830072020729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150915265407729106762694305 113186449055796830072020729)
    ·
      refine ⟨84889836791847622554015547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113186449055796830072020729 84889836791847622554015547)
      ·
        refine ⟨127334755187771433831023321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84889836791847622554015547 127334755187771433831023321)
        ·
          refine ⟨95501066390828575373267491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127334755187771433831023321 95501066390828575373267491)
          ·
            refine ⟨143251599586242863059901237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95501066390828575373267491 143251599586242863059901237)
            ·
              refine ⟨13429837461210268411865741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143251599586242863059901237 13429837461210268411865741)
              ·
                refine ⟨5036189047953850654449653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13429837461210268411865741 5036189047953850654449653)
                ·
                  refine ⟨472142723245673498854655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5036189047953850654449653 472142723245673498854655)
                  ·
                    rfl

theorem cell23_8275452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3, 5].length) (baseStart_8275452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275452 prefixEnd_8275452 := by exact prefixLift 8275452
  have htrace : WordTrace (prefixWord ++ tailWord_8275452) baseStart_8275452 baseEnd_8275452 := by
    simpa [prefixWord, tailWord_8275452, baseEnd_8275452] using wordTrace_append hprefix tailTrace_8275452
  have hstable : (prefixWord ++ tailWord_8275452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275452).length < 2 ^ (prefixWord ++ tailWord_8275452).sum := by decide
  have hdescent : baseEnd_8275452 < baseStart_8275452 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275465 : List Nat := [1, 2, 1, 1, 3, 1, 5, 2, 2, 5]
def baseStart_8275465 : Nat := 118140960795 + 8275465 * 2 ^ 59
def prefixEnd_8275465 : Nat := 4983230072969 + 3 ^ 40 * 8275465 * 2
def baseEnd_8275465 : Nat := 1416430394819856646276445

theorem tailTrace_8275465 : CollatzResearch.WordTrace tailWord_8275465 prefixEnd_8275465 1416430394819856646276445 := by
  unfold tailWord_8275465
  simp only [CollatzResearch.WordTrace]
  refine ⟨301831004964411116745611849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201220669976274077830407899 301831004964411116745611849)
  ·
    refine ⟨226373253723308337559208887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301831004964411116745611849 226373253723308337559208887)
    ·
      refine ⟨339559880584962506338813331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226373253723308337559208887 339559880584962506338813331)
      ·
        refine ⟨509339820877443759508219997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339559880584962506338813331 509339820877443759508219997)
        ·
          refine ⟨191002432829041409815582499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 509339820877443759508219997 191002432829041409815582499)
          ·
            refine ⟨286503649243562114723373749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191002432829041409815582499 286503649243562114723373749)
            ·
              refine ⟨26859717116583948255316289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 286503649243562114723373749 26859717116583948255316289)
              ·
                refine ⟨20144787837437961191487217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26859717116583948255316289 20144787837437961191487217)
                ·
                  refine ⟨15108590878078470893615413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20144787837437961191487217 15108590878078470893615413)
                  ·
                    refine ⟨1416430394819856646276445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15108590878078470893615413 1416430394819856646276445)
                    ·
                      rfl

theorem cell23_8275465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 5].length) (baseStart_8275465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275465 prefixEnd_8275465 := by exact prefixLift 8275465
  have htrace : WordTrace (prefixWord ++ tailWord_8275465) baseStart_8275465 baseEnd_8275465 := by
    simpa [prefixWord, tailWord_8275465, baseEnd_8275465] using wordTrace_append hprefix tailTrace_8275465
  have hstable : (prefixWord ++ tailWord_8275465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275465).length < 2 ^ (prefixWord ++ tailWord_8275465).sum := by decide
  have hdescent : baseEnd_8275465 < baseStart_8275465 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275475 : List Nat := [1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 5]
def baseStart_8275475 : Nat := 118140960795 + 8275475 * 2 ^ 59
def prefixEnd_8275475 : Nat := 4983230072969 + 3 ^ 40 * 8275475 * 2
def baseEnd_8275475 : Nat := 4249296319266114899704289

theorem tailTrace_8275475 : CollatzResearch.WordTrace tailWord_8275475 prefixEnd_8275475 4249296319266114899704289 := by
  unfold tailWord_8275475
  simp only [CollatzResearch.WordTrace]
  refine ⟨301831369694374888453475879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201220913129583258968983919 301831369694374888453475879)
  ·
    refine ⟨452747054541562332680213819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301831369694374888453475879 452747054541562332680213819)
    ·
      refine ⟨679120581812343499020320729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452747054541562332680213819 679120581812343499020320729)
      ·
        refine ⟨509340436359257624265240547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 679120581812343499020320729 509340436359257624265240547)
        ·
          refine ⟨764010654538886436397860821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509340436359257624265240547 764010654538886436397860821)
          ·
            refine ⟨17906499715755150853074863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 764010654538886436397860821 17906499715755150853074863)
            ·
              refine ⟨26859749573632726279612295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17906499715755150853074863 26859749573632726279612295)
              ·
                refine ⟨40289624360449089419418443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26859749573632726279612295 40289624360449089419418443)
                ·
                  refine ⟨60434436540673634129127665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40289624360449089419418443 60434436540673634129127665)
                  ·
                    refine ⟨45325827405505225596845749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60434436540673634129127665 45325827405505225596845749)
                    ·
                      refine ⟨4249296319266114899704289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45325827405505225596845749 4249296319266114899704289)
                      ·
                        rfl

theorem cell23_8275475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 5].length) (baseStart_8275475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275475 prefixEnd_8275475 := by exact prefixLift 8275475
  have htrace : WordTrace (prefixWord ++ tailWord_8275475) baseStart_8275475 baseEnd_8275475 := by
    simpa [prefixWord, tailWord_8275475, baseEnd_8275475] using wordTrace_append hprefix tailTrace_8275475
  have hstable : (prefixWord ++ tailWord_8275475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275475).length < 2 ^ (prefixWord ++ tailWord_8275475).sum := by decide
  have hdescent : baseEnd_8275475 < baseStart_8275475 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275480 : List Nat := [2, 1, 2, 3, 5, 1, 2, 1, 2, 2, 2]
def baseStart_8275480 : Nat := 118140960795 + 8275480 * 2 ^ 59
def prefixEnd_8275480 : Nat := 4983230072969 + 3 ^ 40 * 8275480 * 2
def baseEnd_8275480 : Nat := 4249298886669387380141767

theorem tailTrace_8275480 : CollatzResearch.WordTrace tailWord_8275480 prefixEnd_8275480 4249298886669387380141767 := by
  unfold tailWord_8275480
  simp only [CollatzResearch.WordTrace]
  refine ⟨150915776029678387153703947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201221034706237849538271929 150915776029678387153703947)
  ·
    refine ⟨226373664044517580730555921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150915776029678387153703947 226373664044517580730555921)
    ·
      refine ⟨169780248033388185547916941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226373664044517580730555921 169780248033388185547916941)
      ·
        refine ⟨63667593012520569580468853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169780248033388185547916941 63667593012520569580468853)
        ·
          refine ⟨5968836844923803398168955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63667593012520569580468853 5968836844923803398168955)
          ·
            refine ⟨8953255267385705097253433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5968836844923803398168955 8953255267385705097253433)
            ·
              refine ⟨6714941450539278822940075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8953255267385705097253433 6714941450539278822940075)
              ·
                refine ⟨10072412175808918234410113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6714941450539278822940075 10072412175808918234410113)
                ·
                  refine ⟨7554309131856688675807585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10072412175808918234410113 7554309131856688675807585)
                  ·
                    refine ⟨5665731848892516506855689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7554309131856688675807585 5665731848892516506855689)
                    ·
                      refine ⟨4249298886669387380141767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5665731848892516506855689 4249298886669387380141767)
                      ·
                        rfl

theorem cell23_8275480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_8275480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275480 prefixEnd_8275480 := by exact prefixLift 8275480
  have htrace : WordTrace (prefixWord ++ tailWord_8275480) baseStart_8275480 baseEnd_8275480 := by
    simpa [prefixWord, tailWord_8275480, baseEnd_8275480] using wordTrace_append hprefix tailTrace_8275480
  have hstable : (prefixWord ++ tailWord_8275480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275480).length < 2 ^ (prefixWord ++ tailWord_8275480).sum := by decide
  have hdescent : baseEnd_8275480 < baseStart_8275480 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275535 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 2, 5, 3]
def baseStart_8275535 : Nat := 118140960795 + 8275535 * 2 ^ 59
def prefixEnd_8275535 : Nat := 4983230072969 + 3 ^ 40 * 8275535 * 2
def baseEnd_8275535 : Nat := 4249327128105384664954013

theorem tailTrace_8275535 : CollatzResearch.WordTrace tailWord_8275535 prefixEnd_8275535 4249327128105384664954013 := by
  unfold tailWord_8275535
  simp only [CollatzResearch.WordTrace]
  refine ⟨301833558074157518700660059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201222372049438345800440039 301833558074157518700660059)
  ·
    refine ⟨452750337111236278050990089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301833558074157518700660059 452750337111236278050990089)
    ·
      refine ⟨339562752833427208538242567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452750337111236278050990089 339562752833427208538242567)
      ·
        refine ⟨509344129250140812807363851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339562752833427208538242567 509344129250140812807363851)
        ·
          refine ⟨764016193875211219211045777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509344129250140812807363851 764016193875211219211045777)
          ·
            refine ⟨573012145406408414408284333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 764016193875211219211045777 573012145406408414408284333)
            ·
              refine ⟨214879554527403155403106625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 573012145406408414408284333 214879554527403155403106625)
              ·
                refine ⟨161159665895552366552329969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214879554527403155403106625 161159665895552366552329969)
                ·
                  refine ⟨120869749421664274914247477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161159665895552366552329969 120869749421664274914247477)
                  ·
                    refine ⟨11331539008281025773210701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120869749421664274914247477 11331539008281025773210701)
                    ·
                      refine ⟨4249327128105384664954013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11331539008281025773210701 4249327128105384664954013)
                      ·
                        rfl

theorem cell23_8275535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5, 3].length) (baseStart_8275535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275535 prefixEnd_8275535 := by exact prefixLift 8275535
  have htrace : WordTrace (prefixWord ++ tailWord_8275535) baseStart_8275535 baseEnd_8275535 := by
    simpa [prefixWord, tailWord_8275535, baseEnd_8275535] using wordTrace_append hprefix tailTrace_8275535
  have hstable : (prefixWord ++ tailWord_8275535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275535).length < 2 ^ (prefixWord ++ tailWord_8275535).sum := by decide
  have hdescent : baseEnd_8275535 < baseStart_8275535 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275609 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 5, 2, 2]
def baseStart_8275609 : Nat := 118140960795 + 8275609 * 2 ^ 59
def prefixEnd_8275609 : Nat := 4983230072969 + 3 ^ 40 * 8275609 * 2
def baseEnd_8275609 : Nat := 4249365125673817375428673

theorem tailTrace_8275609 : CollatzResearch.WordTrace tailWord_8275609 prefixEnd_8275609 4249365125673817375428673 := by
  unfold tailWord_8275609
  simp only [CollatzResearch.WordTrace]
  refine ⟨301836257075889429338853881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201224171383926286225902587 301836257075889429338853881)
  ·
    refine ⟨226377192806917072004140411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301836257075889429338853881 226377192806917072004140411)
    ·
      refine ⟨339565789210375608006210617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226377192806917072004140411 339565789210375608006210617)
      ·
        refine ⟨254674341907781706004657963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339565789210375608006210617 254674341907781706004657963)
        ·
          refine ⟨382011512861672559006986945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254674341907781706004657963 382011512861672559006986945)
          ·
            refine ⟨286508634646254419255240209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382011512861672559006986945 286508634646254419255240209)
            ·
              refine ⟨214881475984690814441430157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286508634646254419255240209 214881475984690814441430157)
              ·
                refine ⟨80580553494259055415536309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214881475984690814441430157 80580553494259055415536309)
                ·
                  refine ⟨7554426890086786445206529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80580553494259055415536309 7554426890086786445206529)
                  ·
                    refine ⟨5665820167565089833904897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7554426890086786445206529 5665820167565089833904897)
                    ·
                      refine ⟨4249365125673817375428673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5665820167565089833904897 4249365125673817375428673)
                      ·
                        rfl

theorem cell23_8275609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5, 2, 2].length) (baseStart_8275609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275609 prefixEnd_8275609 := by exact prefixLift 8275609
  have htrace : WordTrace (prefixWord ++ tailWord_8275609) baseStart_8275609 baseEnd_8275609 := by
    simpa [prefixWord, tailWord_8275609, baseEnd_8275609] using wordTrace_append hprefix tailTrace_8275609
  have hstable : (prefixWord ++ tailWord_8275609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275609).length < 2 ^ (prefixWord ++ tailWord_8275609).sum := by decide
  have hdescent : baseEnd_8275609 < baseStart_8275609 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275629 : List Nat := [1, 5, 2, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_8275629 : Nat := 118140960795 + 8275629 * 2 ^ 59
def prefixEnd_8275629 : Nat := 4983230072969 + 3 ^ 40 * 8275629 * 2
def baseEnd_8275629 : Nat := 4249375395286907297178581

theorem tailTrace_8275629 : CollatzResearch.WordTrace tailWord_8275629 prefixEnd_8275629 4249375395286907297178581 := by
  unfold tailWord_8275629
  simp only [CollatzResearch.WordTrace]
  refine ⟨301836986535816972754581941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201224657690544648503054627 301836986535816972754581941)
  ·
    refine ⟨28297217487732841195742057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 301836986535816972754581941 28297217487732841195742057)
    ·
      refine ⟨21222913115799630896806543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28297217487732841195742057 21222913115799630896806543)
      ·
        refine ⟨31834369673699446345209815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21222913115799630896806543 31834369673699446345209815)
        ·
          refine ⟨47751554510549169517814723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31834369673699446345209815 47751554510549169517814723)
          ·
            refine ⟨71627331765823754276722085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47751554510549169517814723 71627331765823754276722085)
            ·
              refine ⟨13430124706091953926885391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71627331765823754276722085 13430124706091953926885391)
              ·
                refine ⟨20145187059137930890328087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13430124706091953926885391 20145187059137930890328087)
                ·
                  refine ⟨30217780588706896335492131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20145187059137930890328087 30217780588706896335492131)
                  ·
                    refine ⟨45326670883060344503238197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30217780588706896335492131 45326670883060344503238197)
                    ·
                      refine ⟨4249375395286907297178581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45326670883060344503238197 4249375395286907297178581)
                      ·
                        rfl

theorem cell23_8275629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_8275629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275629 prefixEnd_8275629 := by exact prefixLift 8275629
  have htrace : WordTrace (prefixWord ++ tailWord_8275629) baseStart_8275629 baseEnd_8275629 := by
    simpa [prefixWord, tailWord_8275629, baseEnd_8275629] using wordTrace_append hprefix tailTrace_8275629
  have hstable : (prefixWord ++ tailWord_8275629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275629).length < 2 ^ (prefixWord ++ tailWord_8275629).sum := by decide
  have hdescent : baseEnd_8275629 < baseStart_8275629 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275652 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_8275652 : Nat := 118140960795 + 8275652 * 2 ^ 59
def prefixEnd_8275652 : Nat := 4983230072969 + 3 ^ 40 * 8275652 * 2
def baseEnd_8275652 : Nat := 4249387205341960707190975

theorem tailTrace_8275652 : CollatzResearch.WordTrace tailWord_8275652 prefixEnd_8275652 4249387205341960707190975 := by
  unfold tailWord_8275652
  simp only [CollatzResearch.WordTrace]
  refine ⟨150918912707366823841334605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201225216943155765121779473 150918912707366823841334605)
  ·
    refine ⟨56594592265262558940500477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150918912707366823841334605 56594592265262558940500477)
    ·
      refine ⟨21222972099473459602687679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56594592265262558940500477 21222972099473459602687679)
      ·
        refine ⟨31834458149210189404031519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21222972099473459602687679 31834458149210189404031519)
        ·
          refine ⟨47751687223815284106047279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31834458149210189404031519 47751687223815284106047279)
          ·
            refine ⟨71627530835722926159070919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47751687223815284106047279 71627530835722926159070919)
            ·
              refine ⟨107441296253584389238606379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71627530835722926159070919 107441296253584389238606379)
              ·
                refine ⟨161161944380376583857909569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107441296253584389238606379 161161944380376583857909569)
                ·
                  refine ⟨120871458285282437893432177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161161944380376583857909569 120871458285282437893432177)
                  ·
                    refine ⟨90653593713961828420074133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120871458285282437893432177 90653593713961828420074133)
                    ·
                      refine ⟨4249387205341960707190975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90653593713961828420074133 4249387205341960707190975)
                      ·
                        rfl

theorem cell23_8275652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_8275652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275652 prefixEnd_8275652 := by exact prefixLift 8275652
  have htrace : WordTrace (prefixWord ++ tailWord_8275652) baseStart_8275652 baseEnd_8275652 := by
    simpa [prefixWord, tailWord_8275652, baseEnd_8275652] using wordTrace_append hprefix tailTrace_8275652
  have hstable : (prefixWord ++ tailWord_8275652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275652).length < 2 ^ (prefixWord ++ tailWord_8275652).sum := by decide
  have hdescent : baseEnd_8275652 < baseStart_8275652 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275693 : List Nat := [1, 5, 1, 2, 1, 3, 2, 2, 2, 1, 3]
def baseStart_8275693 : Nat := 118140960795 + 8275693 * 2 ^ 59
def prefixEnd_8275693 : Nat := 4983230072969 + 3 ^ 40 * 8275693 * 2
def baseEnd_8275693 : Nat := 4249408258048795046778287

theorem tailTrace_8275693 : CollatzResearch.WordTrace tailWord_8275693 prefixEnd_8275693 4249408258048795046778287 := by
  unfold tailWord_8275693
  simp only [CollatzResearch.WordTrace]
  refine ⟨301839320807585111684911733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201226213871723407789941155 301839320807585111684911733)
  ·
    refine ⟨28297436325711104220460475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 301839320807585111684911733 28297436325711104220460475)
    ·
      refine ⟨42446154488566656330690713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28297436325711104220460475 42446154488566656330690713)
      ·
        refine ⟨31834615866424992248018035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42446154488566656330690713 31834615866424992248018035)
        ·
          refine ⟨47751923799637488372027053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31834615866424992248018035 47751923799637488372027053)
          ·
            refine ⟨17906971424864058139510145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47751923799637488372027053 17906971424864058139510145)
            ·
              refine ⟨13430228568648043604632609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17906971424864058139510145 13430228568648043604632609)
              ·
                refine ⟨10072671426486032703474457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13430228568648043604632609 10072671426486032703474457)
                ·
                  refine ⟨7554503569864524527605843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10072671426486032703474457 7554503569864524527605843)
                  ·
                    refine ⟨11331755354796786791408765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7554503569864524527605843 11331755354796786791408765)
                    ·
                      refine ⟨4249408258048795046778287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11331755354796786791408765 4249408258048795046778287)
                      ·
                        rfl

theorem cell23_8275693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_8275693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275693 prefixEnd_8275693 := by exact prefixLift 8275693
  have htrace : WordTrace (prefixWord ++ tailWord_8275693) baseStart_8275693 baseEnd_8275693 := by
    simpa [prefixWord, tailWord_8275693, baseEnd_8275693] using wordTrace_append hprefix tailTrace_8275693
  have hstable : (prefixWord ++ tailWord_8275693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275693).length < 2 ^ (prefixWord ++ tailWord_8275693).sum := by decide
  have hdescent : baseEnd_8275693 < baseStart_8275693 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275712 : List Nat := [2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 4]
def baseStart_8275712 : Nat := 118140960795 + 8275712 * 2 ^ 59
def prefixEnd_8275712 : Nat := 4983230072969 + 3 ^ 40 * 8275712 * 2
def baseEnd_8275712 : Nat := 4249418014181230472440699

theorem tailTrace_8275712 : CollatzResearch.WordTrace tailWord_8275712 prefixEnd_8275712 4249418014181230472440699 := by
  unfold tailWord_8275712
  simp only [CollatzResearch.WordTrace]
  refine ⟨150920006897258138964926695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201226675863010851953235593 150920006897258138964926695)
  ·
    refine ⟨226380010345887208447390043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150920006897258138964926695 226380010345887208447390043)
    ·
      refine ⟨339570015518830812671085065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226380010345887208447390043 339570015518830812671085065)
      ·
        refine ⟨254677511639123109503313799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339570015518830812671085065 254677511639123109503313799)
        ·
          refine ⟨382016267458684664254970699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254677511639123109503313799 382016267458684664254970699)
          ·
            refine ⟨573024401188026996382456049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382016267458684664254970699 573024401188026996382456049)
            ·
              refine ⟨429768300891020247286842037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 573024401188026996382456049 429768300891020247286842037)
              ·
                refine ⟨40290778208533148183141441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 429768300891020247286842037 40290778208533148183141441)
                ·
                  refine ⟨30218083656399861137356081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40290778208533148183141441 30218083656399861137356081)
                  ·
                    refine ⟨22663562742299895853017061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30218083656399861137356081 22663562742299895853017061)
                    ·
                      refine ⟨4249418014181230472440699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22663562742299895853017061 4249418014181230472440699)
                      ·
                        rfl

theorem cell23_8275712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_8275712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275712 prefixEnd_8275712 := by exact prefixLift 8275712
  have htrace : WordTrace (prefixWord ++ tailWord_8275712) baseStart_8275712 baseEnd_8275712 := by
    simpa [prefixWord, tailWord_8275712, baseEnd_8275712] using wordTrace_append hprefix tailTrace_8275712
  have hstable : (prefixWord ++ tailWord_8275712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275712).length < 2 ^ (prefixWord ++ tailWord_8275712).sum := by decide
  have hdescent : baseEnd_8275712 < baseStart_8275712 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275716 : List Nat := [2, 3, 2, 2, 1, 2, 1, 3, 1, 4, 2]
def baseStart_8275716 : Nat := 118140960795 + 8275716 * 2 ^ 59
def prefixEnd_8275716 : Nat := 4983230072969 + 3 ^ 40 * 8275716 * 2
def baseEnd_8275716 : Nat := 4249420068103848456790681

theorem tailTrace_8275716 : CollatzResearch.WordTrace tailWord_8275716 prefixEnd_8275716 4249420068103848456790681 := by
  unfold tailWord_8275716
  simp only [CollatzResearch.WordTrace]
  refine ⟨150920079843250893306499501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201226773124334524408666001 150920079843250893306499501)
  ·
    refine ⟨56595029941219084989937313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150920079843250893306499501 56595029941219084989937313)
    ·
      refine ⟨42446272455914313742452985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56595029941219084989937313 42446272455914313742452985)
      ·
        refine ⟨31834704341935735306839739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42446272455914313742452985 31834704341935735306839739)
        ·
          refine ⟨47752056512903602960259609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31834704341935735306839739 47752056512903602960259609)
          ·
            refine ⟨35814042384677702220194707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47752056512903602960259609 35814042384677702220194707)
            ·
              refine ⟨53721063577016553330292061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35814042384677702220194707 53721063577016553330292061)
              ·
                refine ⟨20145398841381207498859523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53721063577016553330292061 20145398841381207498859523)
                ·
                  refine ⟨30218098262071811248289285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20145398841381207498859523 30218098262071811248289285)
                  ·
                    refine ⟨5665893424138464609054241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30218098262071811248289285 5665893424138464609054241)
                    ·
                      refine ⟨4249420068103848456790681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5665893424138464609054241 4249420068103848456790681)
                      ·
                        rfl

theorem cell23_8275716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_8275716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275716 prefixEnd_8275716 := by exact prefixLift 8275716
  have htrace : WordTrace (prefixWord ++ tailWord_8275716) baseStart_8275716 baseEnd_8275716 := by
    simpa [prefixWord, tailWord_8275716, baseEnd_8275716] using wordTrace_append hprefix tailTrace_8275716
  have hstable : (prefixWord ++ tailWord_8275716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275716).length < 2 ^ (prefixWord ++ tailWord_8275716).sum := by decide
  have hdescent : baseEnd_8275716 < baseStart_8275716 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275722 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 9]
def baseStart_8275722 : Nat := 118140960795 + 8275722 * 2 ^ 59
def prefixEnd_8275722 : Nat := 4983230072969 + 3 ^ 40 * 8275722 * 2
def baseEnd_8275722 : Nat := 472158127665308381479517

theorem tailTrace_8275722 : CollatzResearch.WordTrace tailWord_8275722 prefixEnd_8275722 472158127665308381479517 := by
  unfold tailWord_8275722
  simp only [CollatzResearch.WordTrace]
  refine ⟨75460094631120012409429355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201226919016320033091811613 75460094631120012409429355)
  ·
    refine ⟨113190141946680018614144033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75460094631120012409429355 113190141946680018614144033)
    ·
      refine ⟨84892606460010013960608025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113190141946680018614144033 84892606460010013960608025)
      ·
        refine ⟨63669454845007510470456019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84892606460010013960608025 63669454845007510470456019)
        ·
          refine ⟨95504182267511265705684029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63669454845007510470456019 95504182267511265705684029)
          ·
            refine ⟨35814068350316724639631511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95504182267511265705684029 35814068350316724639631511)
            ·
              refine ⟨53721102525475086959447267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35814068350316724639631511 53721102525475086959447267)
              ·
                refine ⟨80581653788212630439170901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53721102525475086959447267 80581653788212630439170901)
                ·
                  refine ⟨472158127665308381479517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80581653788212630439170901 472158127665308381479517)
                  ·
                    rfl

theorem cell23_8275722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 9].length) (baseStart_8275722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275722 prefixEnd_8275722 := by exact prefixLift 8275722
  have htrace : WordTrace (prefixWord ++ tailWord_8275722) baseStart_8275722 baseEnd_8275722 := by
    simpa [prefixWord, tailWord_8275722, baseEnd_8275722] using wordTrace_append hprefix tailTrace_8275722
  have hstable : (prefixWord ++ tailWord_8275722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275722).length < 2 ^ (prefixWord ++ tailWord_8275722).sum := by decide
  have hdescent : baseEnd_8275722 < baseStart_8275722 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275749 : List Nat := [1, 3, 1, 2, 3, 2, 1, 2, 2, 3, 3]
def baseStart_8275749 : Nat := 118140960795 + 8275749 * 2 ^ 59
def prefixEnd_8275749 : Nat := 4983230072969 + 3 ^ 40 * 8275749 * 2
def baseEnd_8275749 : Nat := 4249437012965446827678029

theorem tailTrace_8275749 : CollatzResearch.WordTrace tailWord_8275749 prefixEnd_8275749 4249437012965446827678029 := by
  unfold tailWord_8275749
  simp only [CollatzResearch.WordTrace]
  refine ⟨301841363295382233248950301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201227575530254822165966867 301841363295382233248950301)
  ·
    refine ⟨113190511235768337468356363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301841363295382233248950301 113190511235768337468356363)
    ·
      refine ⟨169785766853652506202534545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113190511235768337468356363 169785766853652506202534545)
      ·
        refine ⟨127339325140239379651900909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169785766853652506202534545 127339325140239379651900909)
        ·
          refine ⟨47752246927589767369462841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127339325140239379651900909 47752246927589767369462841)
          ·
            refine ⟨35814185195692325527097131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47752246927589767369462841 35814185195692325527097131)
            ·
              refine ⟨53721277793538488290645697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35814185195692325527097131 53721277793538488290645697)
              ·
                refine ⟨40290958345153866217984273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53721277793538488290645697 40290958345153866217984273)
                ·
                  refine ⟨30218218758865399663488205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40290958345153866217984273 30218218758865399663488205)
                  ·
                    refine ⟨11331832034574524873808077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30218218758865399663488205 11331832034574524873808077)
                    ·
                      refine ⟨4249437012965446827678029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11331832034574524873808077 4249437012965446827678029)
                      ·
                        rfl

theorem cell23_8275749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_8275749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275749 prefixEnd_8275749 := by exact prefixLift 8275749
  have htrace : WordTrace (prefixWord ++ tailWord_8275749) baseStart_8275749 baseEnd_8275749 := by
    simpa [prefixWord, tailWord_8275749, baseEnd_8275749] using wordTrace_append hprefix tailTrace_8275749
  have hstable : (prefixWord ++ tailWord_8275749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275749).length < 2 ^ (prefixWord ++ tailWord_8275749).sum := by decide
  have hdescent : baseEnd_8275749 < baseStart_8275749 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275792 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 5]
def baseStart_8275792 : Nat := 118140960795 + 8275792 * 2 ^ 59
def prefixEnd_8275792 : Nat := 4983230072969 + 3 ^ 40 * 8275792 * 2
def baseEnd_8275792 : Nat := 4249459092633590159440331

theorem tailTrace_8275792 : CollatzResearch.WordTrace tailWord_8275792 prefixEnd_8275792 4249459092633590159440331 := by
  unfold tailWord_8275792
  simp only [CollatzResearch.WordTrace]
  refine ⟨150921465817113225796382815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201228621089484301061843753 150921465817113225796382815)
  ·
    refine ⟨226382198725669838694574223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150921465817113225796382815 226382198725669838694574223)
    ·
      refine ⟨339573298088504758041861335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226382198725669838694574223 339573298088504758041861335)
      ·
        refine ⟨509359947132757137062792003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339573298088504758041861335 509359947132757137062792003)
        ·
          refine ⟨764039920699135705594188005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509359947132757137062792003 764039920699135705594188005)
          ·
            refine ⟨143257485131087944798910251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 764039920699135705594188005 143257485131087944798910251)
            ·
              refine ⟨214886227696631917198365377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143257485131087944798910251 214886227696631917198365377)
              ·
                refine ⟨161164670772473937898774033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214886227696631917198365377 161164670772473937898774033)
                ·
                  refine ⟨120873503079355453424080525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161164670772473937898774033 120873503079355453424080525)
                  ·
                    refine ⟨45327563654758295034030197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120873503079355453424080525 45327563654758295034030197)
                    ·
                      refine ⟨4249459092633590159440331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45327563654758295034030197 4249459092633590159440331)
                      ·
                        rfl

theorem cell23_8275792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 5].length) (baseStart_8275792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275792 prefixEnd_8275792 := by exact prefixLift 8275792
  have htrace : WordTrace (prefixWord ++ tailWord_8275792) baseStart_8275792 baseEnd_8275792 := by
    simpa [prefixWord, tailWord_8275792, baseEnd_8275792] using wordTrace_append hprefix tailTrace_8275792
  have hstable : (prefixWord ++ tailWord_8275792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275792).length < 2 ^ (prefixWord ++ tailWord_8275792).sum := by decide
  have hdescent : baseEnd_8275792 < baseStart_8275792 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275832 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 3, 1, 8]
def baseStart_8275832 : Nat := 118140960795 + 8275832 * 2 ^ 59
def prefixEnd_8275832 : Nat := 4983230072969 + 3 ^ 40 * 8275832 * 2
def baseEnd_8275832 : Nat := 4249479631859770002940147

theorem tailTrace_8275832 : CollatzResearch.WordTrace tailWord_8275832 prefixEnd_8275832 4249479631859770002940147 := by
  unfold tailWord_8275832
  simp only [CollatzResearch.WordTrace]
  refine ⟨150922195277040769212110875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201229593702721025616147833 150922195277040769212110875)
  ·
    refine ⟨226383292915561153818166313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150922195277040769212110875 226383292915561153818166313)
    ·
      refine ⟨169787469686670865363624735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226383292915561153818166313 169787469686670865363624735)
      ·
        refine ⟨254681204530006298045437103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169787469686670865363624735 254681204530006298045437103)
        ·
          refine ⟨382021806795009447068155655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254681204530006298045437103 382021806795009447068155655)
          ·
            refine ⟨573032710192514170602233483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382021806795009447068155655 573032710192514170602233483)
            ·
              refine ⟨859549065288771255903350225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573032710192514170602233483 859549065288771255903350225)
              ·
                refine ⟨644661798966578441927512669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 859549065288771255903350225 644661798966578441927512669)
                ·
                  refine ⟨241748174612466915722817251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 644661798966578441927512669 241748174612466915722817251)
                  ·
                    refine ⟨362622261918700373584225877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 241748174612466915722817251 362622261918700373584225877)
                    ·
                      refine ⟨4249479631859770002940147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 362622261918700373584225877 4249479631859770002940147)
                      ·
                        rfl

theorem cell23_8275832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_8275832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275832 prefixEnd_8275832 := by exact prefixLift 8275832
  have htrace : WordTrace (prefixWord ++ tailWord_8275832) baseStart_8275832 baseEnd_8275832 := by
    simpa [prefixWord, tailWord_8275832, baseEnd_8275832] using wordTrace_append hprefix tailTrace_8275832
  have hstable : (prefixWord ++ tailWord_8275832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275832).length < 2 ^ (prefixWord ++ tailWord_8275832).sum := by decide
  have hdescent : baseEnd_8275832 < baseStart_8275832 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275896 : List Nat := [2, 1, 2, 1, 2, 3, 2, 4, 1, 1, 4]
def baseStart_8275896 : Nat := 118140960795 + 8275896 * 2 ^ 59
def prefixEnd_8275896 : Nat := 4983230072969 + 3 ^ 40 * 8275896 * 2
def baseEnd_8275896 : Nat := 4249512494621657752539853

theorem tailTrace_8275896 : CollatzResearch.WordTrace tailWord_8275896 prefixEnd_8275896 4249512494621657752539853 := by
  unfold tailWord_8275896
  simp only [CollatzResearch.WordTrace]
  refine ⟨150923362412924838677275771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201231149883899784903034361 150923362412924838677275771)
  ·
    refine ⟨226385043619387258015913657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150923362412924838677275771 226385043619387258015913657)
    ·
      refine ⟨169788782714540443511935243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226385043619387258015913657 169788782714540443511935243)
      ·
        refine ⟨254683174071810665267902865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169788782714540443511935243 254683174071810665267902865)
        ·
          refine ⟨191012380553857998950927149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254683174071810665267902865 191012380553857998950927149)
          ·
            refine ⟨71629642707696749606597681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191012380553857998950927149 71629642707696749606597681)
            ·
              refine ⟨53722232030772562204948261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71629642707696749606597681 53722232030772562204948261)
              ·
                refine ⟨10072918505769855413427799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53722232030772562204948261 10072918505769855413427799)
                ·
                  refine ⟨15109377758654783120141699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10072918505769855413427799 15109377758654783120141699)
                  ·
                    refine ⟨22664066637982174680212549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15109377758654783120141699 22664066637982174680212549)
                    ·
                      refine ⟨4249512494621657752539853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22664066637982174680212549 4249512494621657752539853)
                      ·
                        rfl

theorem cell23_8275896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 1, 1, 4].length) (baseStart_8275896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275896 prefixEnd_8275896 := by exact prefixLift 8275896
  have htrace : WordTrace (prefixWord ++ tailWord_8275896) baseStart_8275896 baseEnd_8275896 := by
    simpa [prefixWord, tailWord_8275896, baseEnd_8275896] using wordTrace_append hprefix tailTrace_8275896
  have hstable : (prefixWord ++ tailWord_8275896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275896).length < 2 ^ (prefixWord ++ tailWord_8275896).sum := by decide
  have hdescent : baseEnd_8275896 < baseStart_8275896 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275900 : List Nat := [2, 2, 2, 5, 1, 1, 1, 1, 1, 5, 2]
def baseStart_8275900 : Nat := 118140960795 + 8275900 * 2 ^ 59
def prefixEnd_8275900 : Nat := 4983230072969 + 3 ^ 40 * 8275900 * 2
def baseEnd_8275900 : Nat := 4249514548544275736889835

theorem tailTrace_8275900 : CollatzResearch.WordTrace tailWord_8275900 prefixEnd_8275900 4249514548544275736889835 := by
  unfold tailWord_8275900
  simp only [CollatzResearch.WordTrace]
  refine ⟨150923435358917593018848577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201231247145223457358464769 150923435358917593018848577)
  ·
    refine ⟨113192576519188194764136433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150923435358917593018848577 113192576519188194764136433)
    ·
      refine ⟨84894432389391146073102325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113192576519188194764136433 84894432389391146073102325)
      ·
        refine ⟨7958853036505419944353343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84894432389391146073102325 7958853036505419944353343)
        ·
          refine ⟨11938279554758129916530015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7958853036505419944353343 11938279554758129916530015)
          ·
            refine ⟨17907419332137194874795023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11938279554758129916530015 17907419332137194874795023)
            ·
              refine ⟨26861128998205792312192535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17907419332137194874795023 26861128998205792312192535)
              ·
                refine ⟨40291693497308688468288803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26861128998205792312192535 40291693497308688468288803)
                ·
                  refine ⟨60437540245963032702433205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40291693497308688468288803 60437540245963032702433205)
                  ·
                    refine ⟨5666019398059034315853113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60437540245963032702433205 5666019398059034315853113)
                    ·
                      refine ⟨4249514548544275736889835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5666019398059034315853113 4249514548544275736889835)
                      ·
                        rfl

theorem cell23_8275900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_8275900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275900 prefixEnd_8275900 := by exact prefixLift 8275900
  have htrace : WordTrace (prefixWord ++ tailWord_8275900) baseStart_8275900 baseEnd_8275900 := by
    simpa [prefixWord, tailWord_8275900, baseEnd_8275900] using wordTrace_append hprefix tailTrace_8275900
  have hstable : (prefixWord ++ tailWord_8275900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275900).length < 2 ^ (prefixWord ++ tailWord_8275900).sum := by decide
  have hdescent : baseEnd_8275900 < baseStart_8275900 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275909 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 3, 2, 4]
def baseStart_8275909 : Nat := 118140960795 + 8275909 * 2 ^ 59
def prefixEnd_8275909 : Nat := 4983230072969 + 3 ^ 40 * 8275909 * 2
def baseEnd_8275909 : Nat := 4249519169870166201677293

theorem tailTrace_8275909 : CollatzResearch.WordTrace tailWord_8275909 prefixEnd_8275909 4249519169870166201677293 := by
  unfold tailWord_8275909
  simp only [CollatzResearch.WordTrace]
  refine ⟨301847198974802580574774781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201231465983201720383183187 301847198974802580574774781)
  ·
    refine ⟨113192699615550967715540543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301847198974802580574774781 113192699615550967715540543)
    ·
      refine ⟨169789049423326451573310815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113192699615550967715540543 169789049423326451573310815)
      ·
        refine ⟨254683574134989677359966223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169789049423326451573310815 254683574134989677359966223)
        ·
          refine ⟨382025361202484516039949335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254683574134989677359966223 382025361202484516039949335)
          ·
            refine ⟨573038041803726774059924003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382025361202484516039949335 573038041803726774059924003)
            ·
              refine ⟨859557062705590161089886005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573038041803726774059924003 859557062705590161089886005)
              ·
                refine ⟨80583474628649077602176813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 859557062705590161089886005 80583474628649077602176813)
                ·
                  refine ⟨30218802985743404100816305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80583474628649077602176813 30218802985743404100816305)
                  ·
                    refine ⟨22664102239307553075612229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30218802985743404100816305 22664102239307553075612229)
                    ·
                      refine ⟨4249519169870166201677293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22664102239307553075612229 4249519169870166201677293)
                      ·
                        rfl

theorem cell23_8275909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_8275909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275909 prefixEnd_8275909 := by exact prefixLift 8275909
  have htrace : WordTrace (prefixWord ++ tailWord_8275909) baseStart_8275909 baseEnd_8275909 := by
    simpa [prefixWord, tailWord_8275909, baseEnd_8275909] using wordTrace_append hprefix tailTrace_8275909
  have hstable : (prefixWord ++ tailWord_8275909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275909).length < 2 ^ (prefixWord ++ tailWord_8275909).sum := by decide
  have hdescent : baseEnd_8275909 < baseStart_8275909 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275933 : List Nat := [1, 4, 3, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_8275933 : Nat := 118140960795 + 8275933 * 2 ^ 59
def prefixEnd_8275933 : Nat := 4983230072969 + 3 ^ 40 * 8275933 * 2
def baseEnd_8275933 : Nat := 4249531493405874107777183

theorem tailTrace_8275933 : CollatzResearch.WordTrace tailWord_8275933 prefixEnd_8275933 4249531493405874107777183 := by
  unfold tailWord_8275933
  simp only [CollatzResearch.WordTrace]
  refine ⟨301848074326715632673648453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201232049551143755115765635 301848074326715632673648453)
  ·
    refine ⟨56596513936259181126309085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301848074326715632673648453 56596513936259181126309085)
    ·
      refine ⟨21223692726097192922365907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56596513936259181126309085 21223692726097192922365907)
      ·
        refine ⟨31835539089145789383548861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21223692726097192922365907 31835539089145789383548861)
        ·
          refine ⟨11938327158429671018830823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31835539089145789383548861 11938327158429671018830823)
          ·
            refine ⟨17907490737644506528246235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11938327158429671018830823 17907490737644506528246235)
            ·
              refine ⟨26861236106466759792369353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17907490737644506528246235 26861236106466759792369353)
              ·
                refine ⟨20145927079850069844277015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26861236106466759792369353 20145927079850069844277015)
                ·
                  refine ⟨30218890619775104766415523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20145927079850069844277015 30218890619775104766415523)
                  ·
                    refine ⟨45328335929662657149623285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30218890619775104766415523 45328335929662657149623285)
                    ·
                      refine ⟨4249531493405874107777183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45328335929662657149623285 4249531493405874107777183)
                      ·
                        rfl

theorem cell23_8275933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_8275933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275933 prefixEnd_8275933 := by exact prefixLift 8275933
  have htrace : WordTrace (prefixWord ++ tailWord_8275933) baseStart_8275933 baseEnd_8275933 := by
    simpa [prefixWord, tailWord_8275933, baseEnd_8275933] using wordTrace_append hprefix tailTrace_8275933
  have hstable : (prefixWord ++ tailWord_8275933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275933).length < 2 ^ (prefixWord ++ tailWord_8275933).sum := by decide
  have hdescent : baseEnd_8275933 < baseStart_8275933 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275950 : List Nat := [4, 1, 2, 1, 3, 2, 2, 2, 1, 2, 3]
def baseStart_8275950 : Nat := 118140960795 + 8275950 * 2 ^ 59
def prefixEnd_8275950 : Nat := 4983230072969 + 3 ^ 40 * 8275950 * 2
def baseEnd_8275950 : Nat := 4249540222577000541264605

theorem tailTrace_8275950 : CollatzResearch.WordTrace tailWord_8275950 prefixEnd_8275950 4249540222577000541264605 := by
  unfold tailWord_8275950
  simp only [CollatzResearch.WordTrace]
  refine ⟨37731086795956755572127163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201232462911769363051344869 37731086795956755572127163)
  ·
    refine ⟨56596630193935133358190745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37731086795956755572127163 56596630193935133358190745)
    ·
      refine ⟨42447472645451350018643059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56596630193935133358190745 42447472645451350018643059)
      ·
        refine ⟨63671208968177025027964589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42447472645451350018643059 63671208968177025027964589)
        ·
          refine ⟨23876703363066384385486721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63671208968177025027964589 23876703363066384385486721)
          ·
            refine ⟨17907527522299788289115041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23876703363066384385486721 17907527522299788289115041)
            ·
              refine ⟨13430645641724841216836281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17907527522299788289115041 13430645641724841216836281)
              ·
                refine ⟨10072984231293630912627211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13430645641724841216836281 10072984231293630912627211)
                ·
                  refine ⟨15109476346940446368940817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10072984231293630912627211 15109476346940446368940817)
                  ·
                    refine ⟨11332107260205334776705613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15109476346940446368940817 11332107260205334776705613)
                    ·
                      refine ⟨4249540222577000541264605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11332107260205334776705613 4249540222577000541264605)
                      ·
                        rfl

theorem cell23_8275950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_8275950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275950 prefixEnd_8275950 := by exact prefixLift 8275950
  have htrace : WordTrace (prefixWord ++ tailWord_8275950) baseStart_8275950 baseEnd_8275950 := by
    simpa [prefixWord, tailWord_8275950, baseEnd_8275950] using wordTrace_append hprefix tailTrace_8275950
  have hstable : (prefixWord ++ tailWord_8275950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275950).length < 2 ^ (prefixWord ++ tailWord_8275950).sum := by decide
  have hdescent : baseEnd_8275950 < baseStart_8275950 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275953 : List Nat := [1, 2, 2, 2, 5, 2, 2, 7]
def baseStart_8275953 : Nat := 118140960795 + 8275953 * 2 ^ 59
def prefixEnd_8275953 : Nat := 4983230072969 + 3 ^ 40 * 8275953 * 2
def baseEnd_8275953 : Nat := 157390435667369038130633

theorem tailTrace_8275953 : CollatzResearch.WordTrace tailWord_8275953 prefixEnd_8275953 157390435667369038130633 := by
  unfold tailWord_8275953
  simp only [CollatzResearch.WordTrace]
  refine ⟨301848803786643176089376513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201232535857762117392917675 301848803786643176089376513)
  ·
    refine ⟨226386602839982382067032385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301848803786643176089376513 226386602839982382067032385)
    ·
      refine ⟨169789952129986786550274289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226386602839982382067032385 169789952129986786550274289)
      ·
        refine ⟨127342464097490089912705717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169789952129986786550274289 127342464097490089912705717)
        ·
          refine ⟨11938356009139695929316161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127342464097490089912705717 11938356009139695929316161)
          ·
            refine ⟨8953767006854771946987121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11938356009139695929316161 8953767006854771946987121)
            ·
              refine ⟨6715325255141078960240341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8953767006854771946987121 6715325255141078960240341)
              ·
                refine ⟨157390435667369038130633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6715325255141078960240341 157390435667369038130633)
                ·
                  rfl

theorem cell23_8275953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 7].length) (baseStart_8275953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275953 prefixEnd_8275953 := by exact prefixLift 8275953
  have htrace : WordTrace (prefixWord ++ tailWord_8275953) baseStart_8275953 baseEnd_8275953 := by
    simpa [prefixWord, tailWord_8275953, baseEnd_8275953] using wordTrace_append hprefix tailTrace_8275953
  have hstable : (prefixWord ++ tailWord_8275953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275953).length < 2 ^ (prefixWord ++ tailWord_8275953).sum := by decide
  have hdescent : baseEnd_8275953 < baseStart_8275953 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8275997 : List Nat := [1, 4, 2, 2, 2, 1, 4, 1, 2, 1, 3]
def baseStart_8275997 : Nat := 118140960795 + 8275997 * 2 ^ 59
def prefixEnd_8275997 : Nat := 4983230072969 + 3 ^ 40 * 8275997 * 2
def baseEnd_8275997 : Nat := 4249564356167761857376889

theorem tailTrace_8275997 : CollatzResearch.WordTrace tailWord_8275997 prefixEnd_8275997 4249564356167761857376889 := by
  unfold tailWord_8275997
  simp only [CollatzResearch.WordTrace]
  refine ⟨301850408598483771603978245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201233605732322514402652163 301850408598483771603978245)
  ·
    refine ⟨56596951612215707175745921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301850408598483771603978245 56596951612215707175745921)
    ·
      refine ⟨42447713709161780381809441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56596951612215707175745921 42447713709161780381809441)
      ·
        refine ⟨31835785281871335286357081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42447713709161780381809441 31835785281871335286357081)
        ·
          refine ⟨23876838961403501464767811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31835785281871335286357081 23876838961403501464767811)
          ·
            refine ⟨35815258442105252197151717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23876838961403501464767811 35815258442105252197151717)
            ·
              refine ⟨6715360957894734786965947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35815258442105252197151717 6715360957894734786965947)
              ·
                refine ⟨10073041436842102180448921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6715360957894734786965947 10073041436842102180448921)
                ·
                  refine ⟨7554781077631576635336691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10073041436842102180448921 7554781077631576635336691)
                  ·
                    refine ⟨11332171616447364953005037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7554781077631576635336691 11332171616447364953005037)
                    ·
                      refine ⟨4249564356167761857376889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11332171616447364953005037 4249564356167761857376889)
                      ·
                        rfl

theorem cell23_8275997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_8275997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8275997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8275997 prefixEnd_8275997 := by exact prefixLift 8275997
  have htrace : WordTrace (prefixWord ++ tailWord_8275997) baseStart_8275997 baseEnd_8275997 := by
    simpa [prefixWord, tailWord_8275997, baseEnd_8275997] using wordTrace_append hprefix tailTrace_8275997
  have hstable : (prefixWord ++ tailWord_8275997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8275997).length < 2 ^ (prefixWord ++ tailWord_8275997).sum := by decide
  have hdescent : baseEnd_8275997 < baseStart_8275997 := by decide
  rcases family_descends (prefixWord ++ tailWord_8275997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276003 : List Nat := [1, 1, 1, 4, 3, 1, 2, 3, 1, 4, 2]
def baseStart_8276003 : Nat := 118140960795 + 8276003 * 2 ^ 59
def prefixEnd_8276003 : Nat := 4983230072969 + 3 ^ 40 * 8276003 * 2
def baseEnd_8276003 : Nat := 4249567437051688833901861

theorem tailTrace_8276003 : CollatzResearch.WordTrace tailWord_8276003 prefixEnd_8276003 4249567437051688833901861 := by
  unfold tailWord_8276003
  simp only [CollatzResearch.WordTrace]
  refine ⟨301850627436462034628696663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201233751624308023085797775 301850627436462034628696663)
  ·
    refine ⟨452775941154693051943044995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301850627436462034628696663 452775941154693051943044995)
    ·
      refine ⟨679163911732039577914567493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452775941154693051943044995 679163911732039577914567493)
      ·
        refine ⟨127343233449757420858981405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 679163911732039577914567493 127343233449757420858981405)
        ·
          refine ⟨47753712543659032822118027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127343233449757420858981405 47753712543659032822118027)
          ·
            refine ⟨71630568815488549233177041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47753712543659032822118027 71630568815488549233177041)
            ·
              refine ⟨53722926611616411924882781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71630568815488549233177041 53722926611616411924882781)
              ·
                refine ⟨20146097479356154471831043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53722926611616411924882781 20146097479356154471831043)
                ·
                  refine ⟨30219146219034231707746565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20146097479356154471831043 30219146219034231707746565)
                  ·
                    refine ⟨5666089916068918445202481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30219146219034231707746565 5666089916068918445202481)
                    ·
                      refine ⟨4249567437051688833901861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5666089916068918445202481 4249567437051688833901861)
                      ·
                        rfl

theorem cell23_8276003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 4, 2].length) (baseStart_8276003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276003 prefixEnd_8276003 := by exact prefixLift 8276003
  have htrace : WordTrace (prefixWord ++ tailWord_8276003) baseStart_8276003 baseEnd_8276003 := by
    simpa [prefixWord, tailWord_8276003, baseEnd_8276003] using wordTrace_append hprefix tailTrace_8276003
  have hstable : (prefixWord ++ tailWord_8276003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276003).length < 2 ^ (prefixWord ++ tailWord_8276003).sum := by decide
  have hdescent : baseEnd_8276003 < baseStart_8276003 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276007 : List Nat := [1, 1, 7, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_8276007 : Nat := 118140960795 + 8276007 * 2 ^ 59
def prefixEnd_8276007 : Nat := 4983230072969 + 3 ^ 40 * 8276007 * 2
def baseEnd_8276007 : Nat := 4249569490974306818251843

theorem tailTrace_8276007 : CollatzResearch.WordTrace tailWord_8276007 prefixEnd_8276007 4249569490974306818251843 := by
  unfold tailWord_8276007
  simp only [CollatzResearch.WordTrace]
  refine ⟨301850773328447543311842275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201233848885631695541228183 301850773328447543311842275)
  ·
    refine ⟨452776159992671314967763413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301850773328447543311842275 452776159992671314967763413)
    ·
      refine ⟨10611941249828233944556955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 452776159992671314967763413 10611941249828233944556955)
      ·
        refine ⟨15917911874742350916835433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10611941249828233944556955 15917911874742350916835433)
        ·
          refine ⟨11938433906056763187626575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15917911874742350916835433 11938433906056763187626575)
          ·
            refine ⟨17907650859085144781439863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11938433906056763187626575 17907650859085144781439863)
            ·
              refine ⟨26861476288627717172159795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17907650859085144781439863 26861476288627717172159795)
              ·
                refine ⟨40292214432941575758239693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26861476288627717172159795 40292214432941575758239693)
                ·
                  refine ⟨15109580412353090909339885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40292214432941575758239693 15109580412353090909339885)
                  ·
                    refine ⟨5666092654632409091002457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15109580412353090909339885 5666092654632409091002457)
                    ·
                      refine ⟨4249569490974306818251843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5666092654632409091002457 4249569490974306818251843)
                      ·
                        rfl

theorem cell23_8276007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_8276007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276007 prefixEnd_8276007 := by exact prefixLift 8276007
  have htrace : WordTrace (prefixWord ++ tailWord_8276007) baseStart_8276007 baseEnd_8276007 := by
    simpa [prefixWord, tailWord_8276007, baseEnd_8276007] using wordTrace_append hprefix tailTrace_8276007
  have hstable : (prefixWord ++ tailWord_8276007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276007).length < 2 ^ (prefixWord ++ tailWord_8276007).sum := by decide
  have hdescent : baseEnd_8276007 < baseStart_8276007 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276053 : List Nat := [1, 3, 2, 2, 1, 4, 1, 1, 2, 3, 3]
def baseStart_8276053 : Nat := 118140960795 + 8276053 * 2 ^ 59
def prefixEnd_8276053 : Nat := 4983230072969 + 3 ^ 40 * 8276053 * 2
def baseEnd_8276053 : Nat := 4249593111084413638276631

theorem tailTrace_8276053 : CollatzResearch.WordTrace tailWord_8276053 prefixEnd_8276053 4249593111084413638276631 := by
  unfold tailWord_8276053
  simp only [CollatzResearch.WordTrace]
  refine ⟨301852451086280893168016813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201234967390853928778677875 301852451086280893168016813)
  ·
    refine ⟨113194669157355334938006305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301852451086280893168016813 113194669157355334938006305)
    ·
      refine ⟨84896001868016501203504729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113194669157355334938006305 84896001868016501203504729)
      ·
        refine ⟨63672001401012375902628547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84896001868016501203504729 63672001401012375902628547)
        ·
          refine ⟨95508002101518563853942821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63672001401012375902628547 95508002101518563853942821)
          ·
            refine ⟨17907750394034730722614279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95508002101518563853942821 17907750394034730722614279)
            ·
              refine ⟨26861625591052096083921419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17907750394034730722614279 26861625591052096083921419)
              ·
                refine ⟨40292438386578144125882129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26861625591052096083921419 40292438386578144125882129)
                ·
                  refine ⟨30219328789933608094411597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40292438386578144125882129 30219328789933608094411597)
                  ·
                    refine ⟨11332248296225103035404349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30219328789933608094411597 11332248296225103035404349)
                    ·
                      refine ⟨4249593111084413638276631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11332248296225103035404349 4249593111084413638276631)
                      ·
                        rfl

theorem cell23_8276053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_8276053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276053 prefixEnd_8276053 := by exact prefixLift 8276053
  have htrace : WordTrace (prefixWord ++ tailWord_8276053) baseStart_8276053 baseEnd_8276053 := by
    simpa [prefixWord, tailWord_8276053, baseEnd_8276053] using wordTrace_append hprefix tailTrace_8276053
  have hstable : (prefixWord ++ tailWord_8276053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276053).length < 2 ^ (prefixWord ++ tailWord_8276053).sum := by decide
  have hdescent : baseEnd_8276053 < baseStart_8276053 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276054 : List Nat := [5, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_8276054 : Nat := 118140960795 + 8276054 * 2 ^ 59
def prefixEnd_8276054 : Nat := 4983230072969 + 3 ^ 40 * 8276054 * 2
def baseEnd_8276054 : Nat := 4249593624565068134364127

theorem tailTrace_8276054 : CollatzResearch.WordTrace tailWord_8276054 prefixEnd_8276054 4249593624565068134364127 := by
  unfold tailWord_8276054
  simp only [CollatzResearch.WordTrace]
  refine ⟨18865780472454829396175201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201234991706184846892535477 18865780472454829396175201)
  ·
    refine ⟨14149335354341122047131401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18865780472454829396175201 14149335354341122047131401)
    ·
      refine ⟨10612001515755841535348551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14149335354341122047131401 10612001515755841535348551)
      ·
        refine ⟨15918002273633762303022827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10612001515755841535348551 15918002273633762303022827)
        ·
          refine ⟨23877003410450643454534241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15918002273633762303022827 23877003410450643454534241)
          ·
            refine ⟨17907752557837982590900681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23877003410450643454534241 17907752557837982590900681)
            ·
              refine ⟨13430814418378486943175511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17907752557837982590900681 13430814418378486943175511)
              ·
                refine ⟨20146221627567730414763267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13430814418378486943175511 20146221627567730414763267)
                ·
                  refine ⟨30219332441351595622144901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20146221627567730414763267 30219332441351595622144901)
                  ·
                    refine ⟨5666124832753424179152169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30219332441351595622144901 5666124832753424179152169)
                    ·
                      refine ⟨4249593624565068134364127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5666124832753424179152169 4249593624565068134364127)
                      ·
                        rfl

theorem cell23_8276054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_8276054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276054 prefixEnd_8276054 := by exact prefixLift 8276054
  have htrace : WordTrace (prefixWord ++ tailWord_8276054) baseStart_8276054 baseEnd_8276054 := by
    simpa [prefixWord, tailWord_8276054, baseEnd_8276054] using wordTrace_append hprefix tailTrace_8276054
  have hstable : (prefixWord ++ tailWord_8276054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276054).length < 2 ^ (prefixWord ++ tailWord_8276054).sum := by decide
  have hdescent : baseEnd_8276054 < baseStart_8276054 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276103 : List Nat := [1, 1, 4, 2, 1, 1, 3, 3, 3, 4]
def baseStart_8276103 : Nat := 118140960795 + 8276103 * 2 ^ 59
def prefixEnd_8276103 : Nat := 4983230072969 + 3 ^ 40 * 8276103 * 2
def baseEnd_8276103 : Nat := 1416539595039046147550467

theorem tailTrace_8276103 : CollatzResearch.WordTrace tailWord_8276103 prefixEnd_8276103 1416539595039046147550467 := by
  unfold tailWord_8276103
  simp only [CollatzResearch.WordTrace]
  refine ⟨301854274736099751707336963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201236183157399834471557975 301854274736099751707336963)
  ·
    refine ⟨452781412104149627561005445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301854274736099751707336963 452781412104149627561005445)
    ·
      refine ⟨84896514769528055167688521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 452781412104149627561005445 84896514769528055167688521)
      ·
        refine ⟨63672386077146041375766391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84896514769528055167688521 63672386077146041375766391)
        ·
          refine ⟨95508579115719062063649587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63672386077146041375766391 95508579115719062063649587)
          ·
            refine ⟨143262868673578593095474381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95508579115719062063649587 143262868673578593095474381)
            ·
              refine ⟨53723575752591972410802893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143262868673578593095474381 53723575752591972410802893)
              ·
                refine ⟨20146340907221989654051085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53723575752591972410802893 20146340907221989654051085)
                ·
                  refine ⟨7554877840208246120269157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20146340907221989654051085 7554877840208246120269157)
                  ·
                    refine ⟨1416539595039046147550467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7554877840208246120269157 1416539595039046147550467)
                    ·
                      rfl

theorem cell23_8276103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_8276103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276103 prefixEnd_8276103 := by exact prefixLift 8276103
  have htrace : WordTrace (prefixWord ++ tailWord_8276103) baseStart_8276103 baseEnd_8276103 := by
    simpa [prefixWord, tailWord_8276103, baseEnd_8276103] using wordTrace_append hprefix tailTrace_8276103
  have hstable : (prefixWord ++ tailWord_8276103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276103).length < 2 ^ (prefixWord ++ tailWord_8276103).sum := by decide
  have hdescent : baseEnd_8276103 < baseStart_8276103 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276130 : List Nat := [3, 3, 1, 3, 1, 1, 2, 1, 1, 4, 3]
def baseStart_8276130 : Nat := 118140960795 + 8276130 * 2 ^ 59
def prefixEnd_8276130 : Nat := 4983230072969 + 3 ^ 40 * 8276130 * 2
def baseEnd_8276130 : Nat := 4249632649094809837013777

theorem tailTrace_8276130 : CollatzResearch.WordTrace tailWord_8276130 prefixEnd_8276130 4249632649094809837013777 := by
  unfold tailWord_8276130
  simp only [CollatzResearch.WordTrace]
  refine ⟨75463814876750483829642461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201236839671334623545713229 75463814876750483829642461)
  ·
    refine ⟨28298930578781431436115923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75463814876750483829642461 28298930578781431436115923)
    ·
      refine ⟨42448395868172147154173885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28298930578781431436115923 42448395868172147154173885)
      ·
        refine ⟨15918148450564555182815207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42448395868172147154173885 15918148450564555182815207)
        ·
          refine ⟨23877222675846832774222811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15918148450564555182815207 23877222675846832774222811)
          ·
            refine ⟨35815834013770249161334217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23877222675846832774222811 35815834013770249161334217)
            ·
              refine ⟨26861875510327686871000663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35815834013770249161334217 26861875510327686871000663)
              ·
                refine ⟨40292813265491530306500995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26861875510327686871000663 40292813265491530306500995)
                ·
                  refine ⟨60439219898237295459751493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40292813265491530306500995 60439219898237295459751493)
                  ·
                    refine ⟨11332353730919492898703405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60439219898237295459751493 11332353730919492898703405)
                    ·
                      refine ⟨4249632649094809837013777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11332353730919492898703405 4249632649094809837013777)
                      ·
                        rfl

theorem cell23_8276130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_8276130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276130 prefixEnd_8276130 := by exact prefixLift 8276130
  have htrace : WordTrace (prefixWord ++ tailWord_8276130) baseStart_8276130 baseEnd_8276130 := by
    simpa [prefixWord, tailWord_8276130, baseEnd_8276130] using wordTrace_append hprefix tailTrace_8276130
  have hstable : (prefixWord ++ tailWord_8276130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276130).length < 2 ^ (prefixWord ++ tailWord_8276130).sum := by decide
  have hdescent : baseEnd_8276130 < baseStart_8276130 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276170 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 4, 3, 2]
def baseStart_8276170 : Nat := 118140960795 + 8276170 * 2 ^ 59
def prefixEnd_8276170 : Nat := 4983230072969 + 3 ^ 40 * 8276170 * 2
def baseEnd_8276170 : Nat := 4249653188320989680513593

theorem tailTrace_8276170 : CollatzResearch.WordTrace tailWord_8276170 prefixEnd_8276170 4249653188320989680513593 := by
  unfold tailWord_8276170
  simp only [CollatzResearch.WordTrace]
  refine ⟨75464179606714255537506491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201237812284571348100017309 75464179606714255537506491)
  ·
    refine ⟨113196269410071383306259737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75464179606714255537506491 113196269410071383306259737)
    ·
      refine ⟨84897202057553537479694803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113196269410071383306259737 84897202057553537479694803)
      ·
        refine ⟨127345803086330306219542205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84897202057553537479694803 127345803086330306219542205)
        ·
          refine ⟨47754676157373864832328327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127345803086330306219542205 47754676157373864832328327)
          ·
            refine ⟨71632014236060797248492491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47754676157373864832328327 71632014236060797248492491)
            ·
              refine ⟨107448021354091195872738737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71632014236060797248492491 107448021354091195872738737)
              ·
                refine ⟨80586016015568396904554053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107448021354091195872738737 80586016015568396904554053)
                ·
                  refine ⟨15109878002919074419603885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80586016015568396904554053 15109878002919074419603885)
                  ·
                    refine ⟨5666204251094652907351457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15109878002919074419603885 5666204251094652907351457)
                    ·
                      refine ⟨4249653188320989680513593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5666204251094652907351457 4249653188320989680513593)
                      ·
                        rfl

theorem cell23_8276170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 4, 3, 2].length) (baseStart_8276170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276170 prefixEnd_8276170 := by exact prefixLift 8276170
  have htrace : WordTrace (prefixWord ++ tailWord_8276170) baseStart_8276170 baseEnd_8276170 := by
    simpa [prefixWord, tailWord_8276170, baseEnd_8276170] using wordTrace_append hprefix tailTrace_8276170
  have hstable : (prefixWord ++ tailWord_8276170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276170).length < 2 ^ (prefixWord ++ tailWord_8276170).sum := by decide
  have hdescent : baseEnd_8276170 < baseStart_8276170 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276176 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 7, 6]
def baseStart_8276176 : Nat := 118140960795 + 8276176 * 2 ^ 59
def prefixEnd_8276176 : Nat := 4983230072969 + 3 ^ 40 * 8276176 * 2
def baseEnd_8276176 : Nat := 1416552089734972219012855

theorem tailTrace_8276176 : CollatzResearch.WordTrace tailWord_8276176 prefixEnd_8276176 1416552089734972219012855 := by
  unfold tailWord_8276176
  simp only [CollatzResearch.WordTrace]
  refine ⟨150928468632417642587372191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201237958176556856783162921 150928468632417642587372191)
  ·
    refine ⟨226392702948626463881058287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150928468632417642587372191 226392702948626463881058287)
    ·
      refine ⟨339589054422939695821587431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226392702948626463881058287 339589054422939695821587431)
      ·
        refine ⟨509383581634409543732381147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339589054422939695821587431 509383581634409543732381147)
        ·
          refine ⟨764075372451614315598571721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509383581634409543732381147 764075372451614315598571721)
          ·
            refine ⟨573056529338710736698928791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 764075372451614315598571721 573056529338710736698928791)
            ·
              refine ⟨859584794008066105048393187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573056529338710736698928791 859584794008066105048393187)
              ·
                refine ⟨1289377191012099157572589781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 859584794008066105048393187 1289377191012099157572589781)
                ·
                  refine ⟨30219777914346074005607573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1289377191012099157572589781 30219777914346074005607573)
                  ·
                    refine ⟨1416552089734972219012855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30219777914346074005607573 1416552089734972219012855)
                    ·
                      rfl

theorem cell23_8276176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 7, 6].length) (baseStart_8276176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276176 prefixEnd_8276176 := by exact prefixLift 8276176
  have htrace : WordTrace (prefixWord ++ tailWord_8276176) baseStart_8276176 baseEnd_8276176 := by
    simpa [prefixWord, tailWord_8276176, baseEnd_8276176] using wordTrace_append hprefix tailTrace_8276176
  have hstable : (prefixWord ++ tailWord_8276176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276176).length < 2 ^ (prefixWord ++ tailWord_8276176).sum := by decide
  have hdescent : baseEnd_8276176 < baseStart_8276176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276193 : List Nat := [1, 2, 3, 1, 3, 1, 3, 2, 1, 6]
def baseStart_8276193 : Nat := 118140960795 + 8276193 * 2 ^ 59
def prefixEnd_8276193 : Nat := 4983230072969 + 3 ^ 40 * 8276193 * 2
def baseEnd_8276193 : Nat := 1416554999458681030175329

theorem tailTrace_8276193 : CollatzResearch.WordTrace tailWord_8276193 prefixEnd_8276193 1416554999458681030175329 := by
  unfold tailWord_8276193
  simp only [CollatzResearch.WordTrace]
  refine ⟨301857557305773697078113233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201238371537182464718742155 301857557305773697078113233)
  ·
    refine ⟨226393167979330272808584925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301857557305773697078113233 226393167979330272808584925)
    ·
      refine ⟨84897437992248852303219347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226393167979330272808584925 84897437992248852303219347)
      ·
        refine ⟨127346156988373278454829021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84897437992248852303219347 127346156988373278454829021)
        ·
          refine ⟨47754808870639979420560883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127346156988373278454829021 47754808870639979420560883)
          ·
            refine ⟨71632213305959969130841325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47754808870639979420560883 71632213305959969130841325)
            ·
              refine ⟨26862079989734988424065497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71632213305959969130841325 26862079989734988424065497)
              ·
                refine ⟨20146559992301241318049123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26862079989734988424065497 20146559992301241318049123)
                ·
                  refine ⟨30219839988451861977073685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20146559992301241318049123 30219839988451861977073685)
                  ·
                    refine ⟨1416554999458681030175329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30219839988451861977073685 1416554999458681030175329)
                    ·
                      rfl

theorem cell23_8276193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_8276193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276193 prefixEnd_8276193 := by exact prefixLift 8276193
  have htrace : WordTrace (prefixWord ++ tailWord_8276193) baseStart_8276193 baseEnd_8276193 := by
    simpa [prefixWord, tailWord_8276193, baseEnd_8276193] using wordTrace_append hprefix tailTrace_8276193
  have hstable : (prefixWord ++ tailWord_8276193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276193).length < 2 ^ (prefixWord ++ tailWord_8276193).sum := by decide
  have hdescent : baseEnd_8276193 < baseStart_8276193 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276197 : List Nat := [1, 3, 1, 4, 2, 2, 3, 1, 1, 5]
def baseStart_8276197 : Nat := 118140960795 + 8276197 * 2 ^ 59
def prefixEnd_8276197 : Nat := 4983230072969 + 3 ^ 40 * 8276197 * 2
def baseEnd_8276197 : Nat := 1416555684099553691625323

theorem tailTrace_8276197 : CollatzResearch.WordTrace tailWord_8276197 prefixEnd_8276197 1416555684099553691625323 := by
  unfold tailWord_8276197
  simp only [CollatzResearch.WordTrace]
  refine ⟨301857703197759205761258845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201238468798506137174172563 301857703197759205761258845)
  ·
    refine ⟨113196638699159702160472067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301857703197759205761258845 113196638699159702160472067)
    ·
      refine ⟨169794958048739553240708101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113196638699159702160472067 169794958048739553240708101)
      ·
        refine ⟨31836554634138666232632769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169794958048739553240708101 31836554634138666232632769)
        ·
          refine ⟨23877415975603999674474577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31836554634138666232632769 23877415975603999674474577)
          ·
            refine ⟨17908061981702999755855933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23877415975603999674474577 17908061981702999755855933)
            ·
              refine ⟨6715523243138624908445975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17908061981702999755855933 6715523243138624908445975)
              ·
                refine ⟨10073284864707937362668963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6715523243138624908445975 10073284864707937362668963)
                ·
                  refine ⟨15109927297061906044003445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10073284864707937362668963 15109927297061906044003445)
                  ·
                    refine ⟨1416555684099553691625323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15109927297061906044003445 1416555684099553691625323)
                    ·
                      rfl

theorem cell23_8276197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 1, 5].length) (baseStart_8276197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276197 prefixEnd_8276197 := by exact prefixLift 8276197
  have htrace : WordTrace (prefixWord ++ tailWord_8276197) baseStart_8276197 baseEnd_8276197 := by
    simpa [prefixWord, tailWord_8276197, baseEnd_8276197] using wordTrace_append hprefix tailTrace_8276197
  have hstable : (prefixWord ++ tailWord_8276197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276197).length < 2 ^ (prefixWord ++ tailWord_8276197).sum := by decide
  have hdescent : baseEnd_8276197 < baseStart_8276197 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276220 : List Nat := [2, 2, 2, 1, 4, 1, 1, 2, 3, 2, 3]
def baseStart_8276220 : Nat := 118140960795 + 8276220 * 2 ^ 59
def prefixEnd_8276220 : Nat := 4983230072969 + 3 ^ 40 * 8276220 * 2
def baseEnd_8276220 : Nat := 4249678862353714484888363

theorem tailTrace_8276220 : CollatzResearch.WordTrace tailWord_8276220 prefixEnd_8276220 4249678862353714484888363 := by
  unfold tailWord_8276220
  simp only [CollatzResearch.WordTrace]
  refine ⟨150929271038337940344673057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201239028051117253792897409 150929271038337940344673057)
  ·
    refine ⟨113196953278753455258504793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150929271038337940344673057 113196953278753455258504793)
    ·
      refine ⟨84897714959065091443878595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113196953278753455258504793 84897714959065091443878595)
      ·
        refine ⟨127346572438597637165817893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84897714959065091443878595 127346572438597637165817893)
        ·
          refine ⟨23877482332237056968590855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127346572438597637165817893 23877482332237056968590855)
          ·
            refine ⟨35816223498355585452886283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23877482332237056968590855 35816223498355585452886283)
            ·
              refine ⟨53724335247533378179329425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35816223498355585452886283 53724335247533378179329425)
              ·
                refine ⟨40293251435650033634497069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53724335247533378179329425 40293251435650033634497069)
                ·
                  refine ⟨15109969288368762612936401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40293251435650033634497069 15109969288368762612936401)
                  ·
                    refine ⟨11332476966276571959702301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15109969288368762612936401 11332476966276571959702301)
                    ·
                      refine ⟨4249678862353714484888363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11332476966276571959702301 4249678862353714484888363)
                      ·
                        rfl

theorem cell23_8276220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_8276220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276220 prefixEnd_8276220 := by exact prefixLift 8276220
  have htrace : WordTrace (prefixWord ++ tailWord_8276220) baseStart_8276220 baseEnd_8276220 := by
    simpa [prefixWord, tailWord_8276220, baseEnd_8276220] using wordTrace_append hprefix tailTrace_8276220
  have hstable : (prefixWord ++ tailWord_8276220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276220).length < 2 ^ (prefixWord ++ tailWord_8276220).sum := by decide
  have hdescent : baseEnd_8276220 < baseStart_8276220 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276284 : List Nat := [2, 2, 2, 2, 1, 2, 5, 1, 2, 1, 3]
def baseStart_8276284 : Nat := 118140960795 + 8276284 * 2 ^ 59
def prefixEnd_8276284 : Nat := 4983230072969 + 3 ^ 40 * 8276284 * 2
def baseEnd_8276284 : Nat := 4249711725115602234488069

theorem tailTrace_8276284 : CollatzResearch.WordTrace tailWord_8276284 prefixEnd_8276284 4249711725115602234488069 := by
  unfold tailWord_8276284
  simp only [CollatzResearch.WordTrace]
  refine ⟨150930438174222009809837953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201240584232296013079783937 150930438174222009809837953)
  ·
    refine ⟨113197828630666507357378465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150930438174222009809837953 113197828630666507357378465)
    ·
      refine ⟨84898371472999880518033849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113197828630666507357378465 84898371472999880518033849)
      ·
        refine ⟨63673778604749910388525387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84898371472999880518033849 63673778604749910388525387)
        ·
          refine ⟨95510667907124865582788081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63673778604749910388525387 95510667907124865582788081)
          ·
            refine ⟨71633000930343649187091061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95510667907124865582788081 71633000930343649187091061)
            ·
              refine ⟨6715593837219717111289787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71633000930343649187091061 6715593837219717111289787)
              ·
                refine ⟨10073390755829575666934681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6715593837219717111289787 10073390755829575666934681)
                ·
                  refine ⟨7555043066872181750201011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10073390755829575666934681 7555043066872181750201011)
                  ·
                    refine ⟨11332564600308272625301517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7555043066872181750201011 11332564600308272625301517)
                    ·
                      refine ⟨4249711725115602234488069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11332564600308272625301517 4249711725115602234488069)
                      ·
                        rfl

theorem cell23_8276284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_8276284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276284 prefixEnd_8276284 := by exact prefixLift 8276284
  have htrace : WordTrace (prefixWord ++ tailWord_8276284) baseStart_8276284 baseEnd_8276284 := by
    simpa [prefixWord, tailWord_8276284, baseEnd_8276284] using wordTrace_append hprefix tailTrace_8276284
  have hstable : (prefixWord ++ tailWord_8276284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276284).length < 2 ^ (prefixWord ++ tailWord_8276284).sum := by decide
  have hdescent : baseEnd_8276284 < baseStart_8276284 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276303 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 4]
def baseStart_8276303 : Nat := 118140960795 + 8276303 * 2 ^ 59
def prefixEnd_8276303 : Nat := 4983230072969 + 3 ^ 40 * 8276303 * 2
def baseEnd_8276303 : Nat := 4249721481248037660150481

theorem tailTrace_8276303 : CollatzResearch.WordTrace tailWord_8276303 prefixEnd_8276303 4249721481248037660150481 := by
  unfold tailWord_8276303
  simp only [CollatzResearch.WordTrace]
  refine ⟨301861569335375185864617563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201241046223583457243078375 301861569335375185864617563)
  ·
    refine ⟨452792354003062778796926345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301861569335375185864617563 452792354003062778796926345)
    ·
      refine ⟨339594265502297084097694759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452792354003062778796926345 339594265502297084097694759)
      ·
        refine ⟨509391398253445626146542139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339594265502297084097694759 509391398253445626146542139)
        ·
          refine ⟨764087097380168439219813209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509391398253445626146542139 764087097380168439219813209)
          ·
            refine ⟨573065323035126329414859907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 764087097380168439219813209 573065323035126329414859907)
            ·
              refine ⟨859597984552689494122289861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573065323035126329414859907 859597984552689494122289861)
              ·
                refine ⟨161174622103629280147929349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 859597984552689494122289861 161174622103629280147929349)
                ·
                  refine ⟨30220241644430490027736753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161174622103629280147929349 30220241644430490027736753)
                  ·
                    refine ⟨22665181233322867520802565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30220241644430490027736753 22665181233322867520802565)
                    ·
                      refine ⟨4249721481248037660150481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22665181233322867520802565 4249721481248037660150481)
                      ·
                        rfl

theorem cell23_8276303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 4].length) (baseStart_8276303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276303 prefixEnd_8276303 := by exact prefixLift 8276303
  have htrace : WordTrace (prefixWord ++ tailWord_8276303) baseStart_8276303 baseEnd_8276303 := by
    simpa [prefixWord, tailWord_8276303, baseEnd_8276303] using wordTrace_append hprefix tailTrace_8276303
  have hstable : (prefixWord ++ tailWord_8276303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276303).length < 2 ^ (prefixWord ++ tailWord_8276303).sum := by decide
  have hdescent : baseEnd_8276303 < baseStart_8276303 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276323 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 7]
def baseStart_8276323 : Nat := 118140960795 + 8276323 * 2 ^ 59
def prefixEnd_8276323 : Nat := 4983230072969 + 3 ^ 40 * 8276323 * 2
def baseEnd_8276323 : Nat := 4249731750861127581900389

theorem tailTrace_8276323 : CollatzResearch.WordTrace tailWord_8276323 prefixEnd_8276323 4249731750861127581900389 := by
  unfold tailWord_8276323
  simp only [CollatzResearch.WordTrace]
  refine ⟨301862298795302729280345623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201241532530201819520230415 301862298795302729280345623)
  ·
    refine ⟨452793448192954093920518435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301862298795302729280345623 452793448192954093920518435)
    ·
      refine ⟨679190172289431140880777653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452793448192954093920518435 679190172289431140880777653)
      ·
        refine ⟨63674078652134169457572905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 679190172289431140880777653 63674078652134169457572905)
        ·
          refine ⟨47755558989100627093179679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63674078652134169457572905 47755558989100627093179679)
          ·
            refine ⟨71633338483650940639769519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47755558989100627093179679 71633338483650940639769519)
            ·
              refine ⟨107450007725476410959654279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71633338483650940639769519 107450007725476410959654279)
              ·
                refine ⟨161175011588214616439481419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107450007725476410959654279 161175011588214616439481419)
                ·
                  refine ⟨241762517382321924659222129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161175011588214616439481419 241762517382321924659222129)
                  ·
                    refine ⟨181321888036741443494416597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 241762517382321924659222129 181321888036741443494416597)
                    ·
                      refine ⟨4249731750861127581900389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 181321888036741443494416597 4249731750861127581900389)
                      ·
                        rfl

theorem cell23_8276323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_8276323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276323 prefixEnd_8276323 := by exact prefixLift 8276323
  have htrace : WordTrace (prefixWord ++ tailWord_8276323) baseStart_8276323 baseEnd_8276323 := by
    simpa [prefixWord, tailWord_8276323, baseEnd_8276323] using wordTrace_append hprefix tailTrace_8276323
  have hstable : (prefixWord ++ tailWord_8276323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276323).length < 2 ^ (prefixWord ++ tailWord_8276323).sum := by decide
  have hdescent : baseEnd_8276323 < baseStart_8276323 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276324 : List Nat := [2, 3, 1, 1, 3, 1, 2, 4, 2, 2, 2]
def baseStart_8276324 : Nat := 118140960795 + 8276324 * 2 ^ 59
def prefixEnd_8276324 : Nat := 4983230072969 + 3 ^ 40 * 8276324 * 2
def baseEnd_8276324 : Nat := 4249732264341782077987885

theorem tailTrace_8276324 : CollatzResearch.WordTrace tailWord_8276324 prefixEnd_8276324 4249732264341782077987885 := by
  unfold tailWord_8276324
  simp only [CollatzResearch.WordTrace]
  refine ⟨150931167634149553225566013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201241556845532737634088017 150931167634149553225566013)
  ·
    refine ⟨56599187862806082459587255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150931167634149553225566013 56599187862806082459587255)
    ·
      refine ⟨84898781794209123689380883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56599187862806082459587255 84898781794209123689380883)
      ·
        refine ⟨127348172691313685534071325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84898781794209123689380883 127348172691313685534071325)
        ·
          refine ⟨47755564759242632075276747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127348172691313685534071325 47755564759242632075276747)
          ·
            refine ⟨71633347138863948112915121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47755564759242632075276747 71633347138863948112915121)
            ·
              refine ⟨53725010354147961084686341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71633347138863948112915121 53725010354147961084686341)
              ·
                refine ⟨10073439441402742703378689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53725010354147961084686341 10073439441402742703378689)
                ·
                  refine ⟨7555079581052057027534017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10073439441402742703378689 7555079581052057027534017)
                  ·
                    refine ⟨5666309685789042770650513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7555079581052057027534017 5666309685789042770650513)
                    ·
                      refine ⟨4249732264341782077987885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5666309685789042770650513 4249732264341782077987885)
                      ·
                        rfl

theorem cell23_8276324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 2, 2, 2].length) (baseStart_8276324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276324 prefixEnd_8276324 := by exact prefixLift 8276324
  have htrace : WordTrace (prefixWord ++ tailWord_8276324) baseStart_8276324 baseEnd_8276324 := by
    simpa [prefixWord, tailWord_8276324, baseEnd_8276324] using wordTrace_append hprefix tailTrace_8276324
  have hstable : (prefixWord ++ tailWord_8276324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276324).length < 2 ^ (prefixWord ++ tailWord_8276324).sum := by decide
  have hdescent : baseEnd_8276324 < baseStart_8276324 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276341 : List Nat := [1, 3, 4, 1, 2, 2, 1, 3, 2, 2, 2]
def baseStart_8276341 : Nat := 118140960795 + 8276341 * 2 ^ 59
def prefixEnd_8276341 : Nat := 4983230072969 + 3 ^ 40 * 8276341 * 2
def baseEnd_8276341 : Nat := 4249740993512908511475307

theorem tailTrace_8276341 : CollatzResearch.WordTrace tailWord_8276341 prefixEnd_8276341 4249740993512908511475307 := by
  unfold tailWord_8276341
  simp only [CollatzResearch.WordTrace]
  refine ⟨301862955309237518354500877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201241970206158345569667251 301862955309237518354500877)
  ·
    refine ⟨113198608240964069382937829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301862955309237518354500877 113198608240964069382937829)
    ·
      refine ⟨21224739045180763009300843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113198608240964069382937829 21224739045180763009300843)
      ·
        refine ⟨31837108567771144513951265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21224739045180763009300843 31837108567771144513951265)
        ·
          refine ⟨23877831425828358385463449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31837108567771144513951265 23877831425828358385463449)
          ·
            refine ⟨17908373569371268789097587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23877831425828358385463449 17908373569371268789097587)
            ·
              refine ⟨26862560354056903183646381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17908373569371268789097587 26862560354056903183646381)
              ·
                refine ⟨10073460132771338693867393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26862560354056903183646381 10073460132771338693867393)
                ·
                  refine ⟨7555095099578504020400545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10073460132771338693867393 7555095099578504020400545)
                  ·
                    refine ⟨5666321324683878015300409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7555095099578504020400545 5666321324683878015300409)
                    ·
                      refine ⟨4249740993512908511475307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5666321324683878015300409 4249740993512908511475307)
                      ·
                        rfl

theorem cell23_8276341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_8276341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276341 prefixEnd_8276341 := by exact prefixLift 8276341
  have htrace : WordTrace (prefixWord ++ tailWord_8276341) baseStart_8276341 baseEnd_8276341 := by
    simpa [prefixWord, tailWord_8276341, baseEnd_8276341] using wordTrace_append hprefix tailTrace_8276341
  have hstable : (prefixWord ++ tailWord_8276341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276341).length < 2 ^ (prefixWord ++ tailWord_8276341).sum := by decide
  have hdescent : baseEnd_8276341 < baseStart_8276341 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276343 : List Nat := [1, 1, 3, 1, 1, 2, 2, 4, 1, 7]
def baseStart_8276343 : Nat := 118140960795 + 8276343 * 2 ^ 59
def prefixEnd_8276343 : Nat := 4983230072969 + 3 ^ 40 * 8276343 * 2
def baseEnd_8276343 : Nat := 1416580673491405834550099

theorem tailTrace_8276343 : CollatzResearch.WordTrace tailWord_8276343 prefixEnd_8276343 1416580673491405834550099 := by
  unfold tailWord_8276343
  simp only [CollatzResearch.WordTrace]
  refine ⟨301863028255230272696073683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201242018836820181797382455 301863028255230272696073683)
  ·
    refine ⟨452794542382845409044110525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301863028255230272696073683 452794542382845409044110525)
    ·
      refine ⟨169797953393567028391541447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452794542382845409044110525 169797953393567028391541447)
      ·
        refine ⟨254696930090350542587312171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169797953393567028391541447 254696930090350542587312171)
        ·
          refine ⟨382045395135525813880968257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254696930090350542587312171 382045395135525813880968257)
          ·
            refine ⟨286534046351644360410726193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382045395135525813880968257 286534046351644360410726193)
            ·
              refine ⟨214900534763733270308044645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286534046351644360410726193 214900534763733270308044645)
              ·
                refine ⟨40293850268199988182758371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214900534763733270308044645 40293850268199988182758371)
                ·
                  refine ⟨60440775402299982274137557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40293850268199988182758371 60440775402299982274137557)
                  ·
                    refine ⟨1416580673491405834550099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60440775402299982274137557 1416580673491405834550099)
                    ·
                      rfl

theorem cell23_8276343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 7].length) (baseStart_8276343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276343 prefixEnd_8276343 := by exact prefixLift 8276343
  have htrace : WordTrace (prefixWord ++ tailWord_8276343) baseStart_8276343 baseEnd_8276343 := by
    simpa [prefixWord, tailWord_8276343, baseEnd_8276343] using wordTrace_append hprefix tailTrace_8276343
  have hstable : (prefixWord ++ tailWord_8276343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276343).length < 2 ^ (prefixWord ++ tailWord_8276343).sum := by decide
  have hdescent : baseEnd_8276343 < baseStart_8276343 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276381 : List Nat := [1, 4, 2, 1, 4, 2, 2, 2, 5]
def baseStart_8276381 : Nat := 118140960795 + 8276381 * 2 ^ 59
def prefixEnd_8276381 : Nat := 4983230072969 + 3 ^ 40 * 8276381 * 2
def baseEnd_8276381 : Nat := 472195725859898706108347

theorem tailTrace_8276381 : CollatzResearch.WordTrace tailWord_8276381 prefixEnd_8276381 472195725859898706108347 := by
  unfold tailWord_8276381
  simp only [CollatzResearch.WordTrace]
  refine ⟨301864414229092605185956997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201242942819395070123971331 301864414229092605185956997)
  ·
    refine ⟨56599577667954863472366937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301864414229092605185956997 56599577667954863472366937)
    ·
      refine ⟨42449683250966147604275203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56599577667954863472366937 42449683250966147604275203)
      ·
        refine ⟨63674524876449221406412805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42449683250966147604275203 63674524876449221406412805)
        ·
          refine ⟨11938973414334229013702401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63674524876449221406412805 11938973414334229013702401)
          ·
            refine ⟨8954230060750671760276801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11938973414334229013702401 8954230060750671760276801)
            ·
              refine ⟨6715672545563003820207601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8954230060750671760276801 6715672545563003820207601)
              ·
                refine ⟨5036754409172252865155701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6715672545563003820207601 5036754409172252865155701)
                ·
                  refine ⟨472195725859898706108347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5036754409172252865155701 472195725859898706108347)
                  ·
                    rfl

theorem cell23_8276381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2, 5].length) (baseStart_8276381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276381 prefixEnd_8276381 := by exact prefixLift 8276381
  have htrace : WordTrace (prefixWord ++ tailWord_8276381) baseStart_8276381 baseEnd_8276381 := by
    simpa [prefixWord, tailWord_8276381, baseEnd_8276381] using wordTrace_append hprefix tailTrace_8276381
  have hstable : (prefixWord ++ tailWord_8276381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276381).length < 2 ^ (prefixWord ++ tailWord_8276381).sum := by decide
  have hdescent : baseEnd_8276381 < baseStart_8276381 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276403 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 12]
def baseStart_8276403 : Nat := 118140960795 + 8276403 * 2 ^ 59
def prefixEnd_8276403 : Nat := 4983230072969 + 3 ^ 40 * 8276403 * 2
def baseEnd_8276403 : Nat := 472196981034831918766669

theorem tailTrace_8276403 : CollatzResearch.WordTrace tailWord_8276403 prefixEnd_8276403 472196981034831918766669 := by
  unfold tailWord_8276403
  simp only [CollatzResearch.WordTrace]
  refine ⟨301865216635012902943257863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201243477756675268628838575 301865216635012902943257863)
  ·
    refine ⟨452797824952519354414886795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301865216635012902943257863 452797824952519354414886795)
    ·
      refine ⟨679196737428779031622330193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452797824952519354414886795 679196737428779031622330193)
      ·
        refine ⟨509397553071584273716747645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 679196737428779031622330193 509397553071584273716747645)
        ·
          refine ⟨191024082401844102643780367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 509397553071584273716747645 191024082401844102643780367)
          ·
            refine ⟨286536123602766153965670551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191024082401844102643780367 286536123602766153965670551)
            ·
              refine ⟨429804185404149230948505827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286536123602766153965670551 429804185404149230948505827)
              ·
                refine ⟨644706278106223846422758741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429804185404149230948505827 644706278106223846422758741)
                ·
                  refine ⟨472196981034831918766669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 644706278106223846422758741 472196981034831918766669)
                  ·
                    rfl

theorem cell23_8276403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 12].length) (baseStart_8276403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276403 prefixEnd_8276403 := by exact prefixLift 8276403
  have htrace : WordTrace (prefixWord ++ tailWord_8276403) baseStart_8276403 baseEnd_8276403 := by
    simpa [prefixWord, tailWord_8276403, baseEnd_8276403] using wordTrace_append hprefix tailTrace_8276403
  have hstable : (prefixWord ++ tailWord_8276403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276403).length < 2 ^ (prefixWord ++ tailWord_8276403).sum := by decide
  have hdescent : baseEnd_8276403 < baseStart_8276403 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276407 : List Nat := [1, 1, 3, 1, 3, 4, 1, 2, 3, 4]
def baseStart_8276407 : Nat := 118140960795 + 8276407 * 2 ^ 59
def prefixEnd_8276407 : Nat := 4983230072969 + 3 ^ 40 * 8276407 * 2
def baseEnd_8276407 : Nat := 1416591627745368417750001

theorem tailTrace_8276407 : CollatzResearch.WordTrace tailWord_8276407 prefixEnd_8276407 1416591627745368417750001 := by
  unfold tailWord_8276407
  simp only [CollatzResearch.WordTrace]
  refine ⟨301865362526998411626403475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201243575017998941084268983 301865362526998411626403475)
  ·
    refine ⟨452798043790497617439605213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301865362526998411626403475 452798043790497617439605213)
    ·
      refine ⟨169799266421436606539851955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452798043790497617439605213 169799266421436606539851955)
      ·
        refine ⟨254698899632154909809777933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169799266421436606539851955 254698899632154909809777933)
        ·
          refine ⟨95512087362058091178666725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254698899632154909809777933 95512087362058091178666725)
          ·
            refine ⟨17908516380385892096000011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95512087362058091178666725 17908516380385892096000011)
            ·
              refine ⟨26862774570578838144000017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17908516380385892096000011 26862774570578838144000017)
              ·
                refine ⟨20147080927934128608000013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26862774570578838144000017 20147080927934128608000013)
                ·
                  refine ⟨7555155347975298228000005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20147080927934128608000013 7555155347975298228000005)
                  ·
                    refine ⟨1416591627745368417750001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7555155347975298228000005 1416591627745368417750001)
                    ·
                      rfl

theorem cell23_8276407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3, 4].length) (baseStart_8276407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276407 prefixEnd_8276407 := by exact prefixLift 8276407
  have htrace : WordTrace (prefixWord ++ tailWord_8276407) baseStart_8276407 baseEnd_8276407 := by
    simpa [prefixWord, tailWord_8276407, baseEnd_8276407] using wordTrace_append hprefix tailTrace_8276407
  have hstable : (prefixWord ++ tailWord_8276407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276407).length < 2 ^ (prefixWord ++ tailWord_8276407).sum := by decide
  have hdescent : baseEnd_8276407 < baseStart_8276407 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276424 : List Nat := [2, 1, 3, 1, 3, 2, 1, 5, 1, 4]
def baseStart_8276424 : Nat := 118140960795 + 8276424 * 2 ^ 59
def prefixEnd_8276424 : Nat := 4983230072969 + 3 ^ 40 * 8276424 * 2
def baseEnd_8276424 : Nat := 1416594537469077228912475

theorem tailTrace_8276424 : CollatzResearch.WordTrace tailWord_8276424 prefixEnd_8276424 1416594537469077228912475 := by
  unfold tailWord_8276424
  simp only [CollatzResearch.WordTrace]
  refine ⟨150932991283968411764886163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201243988378624549019848217 150932991283968411764886163)
  ·
    refine ⟨226399486925952617647329245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150932991283968411764886163 226399486925952617647329245)
    ·
      refine ⟨84899807597232231617748467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226399486925952617647329245 84899807597232231617748467)
      ·
        refine ⟨127349711395848347426622701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84899807597232231617748467 127349711395848347426622701)
        ·
          refine ⟨47756141773443130284983513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127349711395848347426622701 47756141773443130284983513)
          ·
            refine ⟨35817106330082347713737635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47756141773443130284983513 35817106330082347713737635)
            ·
              refine ⟨53725659495123521570606453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35817106330082347713737635 53725659495123521570606453)
              ·
                refine ⟨5036780577667830147244355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53725659495123521570606453 5036780577667830147244355)
                ·
                  refine ⟨7555170866501745220866533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5036780577667830147244355 7555170866501745220866533)
                  ·
                    refine ⟨1416594537469077228912475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7555170866501745220866533 1416594537469077228912475)
                    ·
                      rfl

theorem cell23_8276424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_8276424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276424 prefixEnd_8276424 := by exact prefixLift 8276424
  have htrace : WordTrace (prefixWord ++ tailWord_8276424) baseStart_8276424 baseEnd_8276424 := by
    simpa [prefixWord, tailWord_8276424, baseEnd_8276424] using wordTrace_append hprefix tailTrace_8276424
  have hstable : (prefixWord ++ tailWord_8276424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276424).length < 2 ^ (prefixWord ++ tailWord_8276424).sum := by decide
  have hdescent : baseEnd_8276424 < baseStart_8276424 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276437 : List Nat := [1, 3, 2, 3, 1, 2, 3, 2, 6]
def baseStart_8276437 : Nat := 118140960795 + 8276437 * 2 ^ 59
def prefixEnd_8276437 : Nat := 4983230072969 + 3 ^ 40 * 8276437 * 2
def baseEnd_8276437 : Nat := 472198920850637792874985

theorem tailTrace_8276437 : CollatzResearch.WordTrace tailWord_8276437 prefixEnd_8276437 472198920850637792874985 := by
  unfold tailWord_8276437
  simp only [CollatzResearch.WordTrace]
  refine ⟨301866456716889726749995565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201244304477926484499997043 301866456716889726749995565)
  ·
    refine ⟨113199921268833647531248337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301866456716889726749995565 113199921268833647531248337)
    ·
      refine ⟨84899940951625235648436253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113199921268833647531248337 84899940951625235648436253)
      ·
        refine ⟨31837477856859463368163595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84899940951625235648436253 31837477856859463368163595)
        ·
          refine ⟨47756216785289195052245393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31837477856859463368163595 47756216785289195052245393)
          ·
            refine ⟨35817162588966896289184045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47756216785289195052245393 35817162588966896289184045)
            ·
              refine ⟨13431435970862586108444017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35817162588966896289184045 13431435970862586108444017)
              ·
                refine ⟨10073576978146939581333013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13431435970862586108444017 10073576978146939581333013)
                ·
                  refine ⟨472198920850637792874985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10073576978146939581333013 472198920850637792874985)
                  ·
                    rfl

theorem cell23_8276437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 6].length) (baseStart_8276437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276437 prefixEnd_8276437 := by exact prefixLift 8276437
  have htrace : WordTrace (prefixWord ++ tailWord_8276437) baseStart_8276437 baseEnd_8276437 := by
    simpa [prefixWord, tailWord_8276437, baseEnd_8276437] using wordTrace_append hprefix tailTrace_8276437
  have hstable : (prefixWord ++ tailWord_8276437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276437).length < 2 ^ (prefixWord ++ tailWord_8276437).sum := by decide
  have hdescent : baseEnd_8276437 < baseStart_8276437 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276457 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 6, 3, 2]
def baseStart_8276457 : Nat := 118140960795 + 8276457 * 2 ^ 59
def prefixEnd_8276457 : Nat := 4983230072969 + 3 ^ 40 * 8276457 * 2
def baseEnd_8276457 : Nat := 4249800557268830057624773

theorem tailTrace_8276457 : CollatzResearch.WordTrace tailWord_8276457 prefixEnd_8276457 4249800557268830057624773 := by
  unfold tailWord_8276457
  simp only [CollatzResearch.WordTrace]
  refine ⟨301867186176817270165723625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201244790784544846777149083 301867186176817270165723625)
  ·
    refine ⟨226400389632612952624292719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301867186176817270165723625 226400389632612952624292719)
    ·
      refine ⟨339600584448919428936439079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226400389632612952624292719 339600584448919428936439079)
      ·
        refine ⟨509400876673379143404658619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339600584448919428936439079 509400876673379143404658619)
        ·
          refine ⟨764101315010068715106987929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509400876673379143404658619 764101315010068715106987929)
          ·
            refine ⟨573075986257551536330240947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 764101315010068715106987929 573075986257551536330240947)
            ·
              refine ⟨859613979386327304495361421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573075986257551536330240947 859613979386327304495361421)
              ·
                refine ⟨322355242269872739185760533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 859613979386327304495361421 322355242269872739185760533)
                ·
                  refine ⟨15110401981400284649332525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 322355242269872739185760533 15110401981400284649332525)
                  ·
                    refine ⟨5666400743025106743499697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15110401981400284649332525 5666400743025106743499697)
                    ·
                      refine ⟨4249800557268830057624773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5666400743025106743499697 4249800557268830057624773)
                      ·
                        rfl

theorem cell23_8276457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 3, 2].length) (baseStart_8276457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276457 prefixEnd_8276457 := by exact prefixLift 8276457
  have htrace : WordTrace (prefixWord ++ tailWord_8276457) baseStart_8276457 baseEnd_8276457 := by
    simpa [prefixWord, tailWord_8276457, baseEnd_8276457] using wordTrace_append hprefix tailTrace_8276457
  have hstable : (prefixWord ++ tailWord_8276457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276457).length < 2 ^ (prefixWord ++ tailWord_8276457).sum := by decide
  have hdescent : baseEnd_8276457 < baseStart_8276457 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276467 : List Nat := [1, 1, 1, 2, 2, 2, 6, 2, 1, 5]
def baseStart_8276467 : Nat := 118140960795 + 8276467 * 2 ^ 59
def prefixEnd_8276467 : Nat := 4983230072969 + 3 ^ 40 * 8276467 * 2
def baseEnd_8276467 : Nat := 1416601897358458339499909

theorem tailTrace_8276467 : CollatzResearch.WordTrace tailWord_8276467 prefixEnd_8276467 1416601897358458339499909 := by
  unfold tailWord_8276467
  simp only [CollatzResearch.WordTrace]
  refine ⟨301867550906781041873587655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201245033937854027915725103 301867550906781041873587655)
  ·
    refine ⟨452801326360171562810381483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301867550906781041873587655 452801326360171562810381483)
    ·
      refine ⟨679201989540257344215572225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452801326360171562810381483 679201989540257344215572225)
      ·
        refine ⟨509401492155193008161679169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 679201989540257344215572225 509401492155193008161679169)
        ·
          refine ⟨382051119116394756121259377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 509401492155193008161679169 382051119116394756121259377)
          ·
            refine ⟨286538339337296067090944533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382051119116394756121259377 286538339337296067090944533)
            ·
              refine ⟨13431484656435753144888025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 286538339337296067090944533 13431484656435753144888025)
              ·
                refine ⟨10073613492326814858666019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13431484656435753144888025 10073613492326814858666019)
                ·
                  refine ⟨15110420238490222287999029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10073613492326814858666019 15110420238490222287999029)
                  ·
                    refine ⟨1416601897358458339499909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15110420238490222287999029 1416601897358458339499909)
                    ·
                      rfl

theorem cell23_8276467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 5].length) (baseStart_8276467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276467 prefixEnd_8276467 := by exact prefixLift 8276467
  have htrace : WordTrace (prefixWord ++ tailWord_8276467) baseStart_8276467 baseEnd_8276467 := by
    simpa [prefixWord, tailWord_8276467, baseEnd_8276467] using wordTrace_append hprefix tailTrace_8276467
  have hstable : (prefixWord ++ tailWord_8276467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276467).length < 2 ^ (prefixWord ++ tailWord_8276467).sum := by decide
  have hdescent : baseEnd_8276467 < baseStart_8276467 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276484 : List Nat := [2, 3, 2, 3, 1, 1, 2, 3, 1, 5]
def baseStart_8276484 : Nat := 118140960795 + 8276484 * 2 ^ 59
def prefixEnd_8276484 : Nat := 4983230072969 + 3 ^ 40 * 8276484 * 2
def baseEnd_8276484 : Nat := 1416604807082167150662383

theorem tailTrace_8276484 : CollatzResearch.WordTrace tailWord_8276484 prefixEnd_8276484 1416604807082167150662383 := by
  unfold tailWord_8276484
  simp only [CollatzResearch.WordTrace]
  refine ⟨150934085473859726888478253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201245447298479635851304337 150934085473859726888478253)
  ·
    refine ⟨56600282052697397583179345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150934085473859726888478253 56600282052697397583179345)
    ·
      refine ⟨42450211539523048187384509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56600282052697397583179345 42450211539523048187384509)
      ·
        refine ⟨15918829327321143070269191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42450211539523048187384509 15918829327321143070269191)
        ·
          refine ⟨23878243990981714605403787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15918829327321143070269191 23878243990981714605403787)
          ·
            refine ⟨35817365986472571908105681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23878243990981714605403787 35817365986472571908105681)
            ·
              refine ⟨26863024489854428931079261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35817365986472571908105681 26863024489854428931079261)
              ·
                refine ⟨10073634183695410849154723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26863024489854428931079261 10073634183695410849154723)
                ·
                  refine ⟨15110451275543116273732085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10073634183695410849154723 15110451275543116273732085)
                  ·
                    refine ⟨1416604807082167150662383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15110451275543116273732085 1416604807082167150662383)
                    ·
                      rfl

theorem cell23_8276484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_8276484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276484 prefixEnd_8276484 := by exact prefixLift 8276484
  have htrace : WordTrace (prefixWord ++ tailWord_8276484) baseStart_8276484 baseEnd_8276484 := by
    simpa [prefixWord, tailWord_8276484, baseEnd_8276484] using wordTrace_append hprefix tailTrace_8276484
  have hstable : (prefixWord ++ tailWord_8276484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276484).length < 2 ^ (prefixWord ++ tailWord_8276484).sum := by decide
  have hdescent : baseEnd_8276484 < baseStart_8276484 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276534 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_8276534 : Nat := 118140960795 + 8276534 * 2 ^ 59
def prefixEnd_8276534 : Nat := 4983230072969 + 3 ^ 40 * 8276534 * 2
def baseEnd_8276534 : Nat := 4249840095279226256361919

theorem tailTrace_8276534 : CollatzResearch.WordTrace tailWord_8276534 prefixEnd_8276534 4249840095279226256361919 := by
  unfold tailWord_8276534
  simp only [CollatzResearch.WordTrace]
  refine ⟨18866874662346144519767291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201246663065025541544184437 18866874662346144519767291)
  ·
    refine ⟨28300311993519216779650937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18866874662346144519767291 28300311993519216779650937)
    ·
      refine ⟨21225233995139412584738203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28300311993519216779650937 21225233995139412584738203)
      ·
        refine ⟨31837850992709118877107305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21225233995139412584738203 31837850992709118877107305)
        ·
          refine ⟨23878388244531839157830479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31837850992709118877107305 23878388244531839157830479)
          ·
            refine ⟨35817582366797758736745719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23878388244531839157830479 35817582366797758736745719)
            ·
              refine ⟨53726373550196638105118579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35817582366797758736745719 53726373550196638105118579)
              ·
                refine ⟨80589560325294957157677869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53726373550196638105118579 80589560325294957157677869)
                ·
                  refine ⟨30221085121985608934129201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80589560325294957157677869 30221085121985608934129201)
                  ·
                    refine ⟨22665813841489206700596901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30221085121985608934129201 22665813841489206700596901)
                    ·
                      refine ⟨4249840095279226256361919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22665813841489206700596901 4249840095279226256361919)
                      ·
                        rfl

theorem cell23_8276534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_8276534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276534 prefixEnd_8276534 := by exact prefixLift 8276534
  have htrace : WordTrace (prefixWord ++ tailWord_8276534) baseStart_8276534 baseEnd_8276534 := by
    simpa [prefixWord, tailWord_8276534, baseEnd_8276534] using wordTrace_append hprefix tailTrace_8276534
  have hstable : (prefixWord ++ tailWord_8276534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276534).length < 2 ^ (prefixWord ++ tailWord_8276534).sum := by decide
  have hdescent : baseEnd_8276534 < baseStart_8276534 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276605 : List Nat := [1, 4, 1, 1, 6, 1, 1, 2, 2, 1, 3]
def baseStart_8276605 : Nat := 118140960795 + 8276605 * 2 ^ 59
def prefixEnd_8276605 : Nat := 4983230072969 + 3 ^ 40 * 8276605 * 2
def baseEnd_8276605 : Nat := 4249876552405695478574093

theorem tailTrace_8276605 : CollatzResearch.WordTrace tailWord_8276605 prefixEnd_8276605 4249876552405695478574093 := by
  unfold tailWord_8276605
  simp only [CollatzResearch.WordTrace]
  refine ⟨301872584180281091442111269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201248389453520727628074179 301872584180281091442111269)
  ·
    refine ⟨56601109533802704645395863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301872584180281091442111269 56601109533802704645395863)
    ·
      refine ⟨84901664300704056968093795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56601109533802704645395863 84901664300704056968093795)
      ·
        refine ⟨127352496451056085452140693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84901664300704056968093795 127352496451056085452140693)
        ·
          refine ⟨5969648271143254005569095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 127352496451056085452140693 5969648271143254005569095)
          ·
            refine ⟨8954472406714881008353643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5969648271143254005569095 8954472406714881008353643)
            ·
              refine ⟨13431708610072321512530465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8954472406714881008353643 13431708610072321512530465)
              ·
                refine ⟨10073781457554241134397849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13431708610072321512530465 10073781457554241134397849)
                ·
                  refine ⟨7555336093165680850798387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10073781457554241134397849 7555336093165680850798387)
                  ·
                    refine ⟨11333004139748521276197581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7555336093165680850798387 11333004139748521276197581)
                    ·
                      refine ⟨4249876552405695478574093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11333004139748521276197581 4249876552405695478574093)
                      ·
                        rfl

theorem cell23_8276605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 2, 1, 3].length) (baseStart_8276605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276605 prefixEnd_8276605 := by exact prefixLift 8276605
  have htrace : WordTrace (prefixWord ++ tailWord_8276605) baseStart_8276605 baseEnd_8276605 := by
    simpa [prefixWord, tailWord_8276605, baseEnd_8276605] using wordTrace_append hprefix tailTrace_8276605
  have hstable : (prefixWord ++ tailWord_8276605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276605).length < 2 ^ (prefixWord ++ tailWord_8276605).sum := by decide
  have hdescent : baseEnd_8276605 < baseStart_8276605 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276628 : List Nat := [2, 4, 2, 2, 1, 1, 3, 1, 1, 4, 2]
def baseStart_8276628 : Nat := 118140960795 + 8276628 * 2 ^ 59
def prefixEnd_8276628 : Nat := 4983230072969 + 3 ^ 40 * 8276628 * 2
def baseEnd_8276628 : Nat := 4249888362460748888586487

theorem tailTrace_8276628 : CollatzResearch.WordTrace tailWord_8276628 prefixEnd_8276628 4249888362460748888586487 := by
  unfold tailWord_8276628
  simp only [CollatzResearch.WordTrace]
  refine ⟨150936711529598883185099269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201248948706131844246799025 150936711529598883185099269)
  ·
    refine ⟨28300633411799790597206113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150936711529598883185099269 28300633411799790597206113)
    ·
      refine ⟨21225475058849842947904585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28300633411799790597206113 21225475058849842947904585)
      ·
        refine ⟨15919106294137382210928439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21225475058849842947904585 15919106294137382210928439)
        ·
          refine ⟨23878659441206073316392659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15919106294137382210928439 23878659441206073316392659)
          ·
            refine ⟨35817989161809109974588989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23878659441206073316392659 35817989161809109974588989)
            ·
              refine ⟨13431745935678416240470871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35817989161809109974588989 13431745935678416240470871)
              ·
                refine ⟨20147618903517624360706307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13431745935678416240470871 20147618903517624360706307)
                ·
                  refine ⟨30221428355276436541059461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20147618903517624360706307 30221428355276436541059461)
                  ·
                    refine ⟨5666517816614331851448649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30221428355276436541059461 5666517816614331851448649)
                    ·
                      refine ⟨4249888362460748888586487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5666517816614331851448649 4249888362460748888586487)
                      ·
                        rfl

theorem cell23_8276628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_8276628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276628 prefixEnd_8276628 := by exact prefixLift 8276628
  have htrace : WordTrace (prefixWord ++ tailWord_8276628) baseStart_8276628 baseEnd_8276628 := by
    simpa [prefixWord, tailWord_8276628, baseEnd_8276628] using wordTrace_append hprefix tailTrace_8276628
  have hstable : (prefixWord ++ tailWord_8276628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276628).length < 2 ^ (prefixWord ++ tailWord_8276628).sum := by decide
  have hdescent : baseEnd_8276628 < baseStart_8276628 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276727 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 6]
def baseStart_8276727 : Nat := 118140960795 + 8276727 * 2 ^ 59
def prefixEnd_8276727 : Nat := 4983230072969 + 3 ^ 40 * 8276727 * 2
def baseEnd_8276727 : Nat := 4249939197045544001248531

theorem tailTrace_8276727 : CollatzResearch.WordTrace tailWord_8276727 prefixEnd_8276727 4249939197045544001248531 := by
  unfold tailWord_8276727
  simp only [CollatzResearch.WordTrace]
  refine ⟨301877033885839106278052435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201251355923892737518701623 301877033885839106278052435)
  ·
    refine ⟨452815550828758659417078653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301877033885839106278052435 452815550828758659417078653)
    ·
      refine ⟨169805831560784497281404495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452815550828758659417078653 169805831560784497281404495)
      ·
        refine ⟨254708747341176745922106743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169805831560784497281404495 254708747341176745922106743)
        ·
          refine ⟨382063121011765118883160115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254708747341176745922106743 382063121011765118883160115)
          ·
            refine ⟨573094681517647678324740173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382063121011765118883160115 573094681517647678324740173)
            ·
              refine ⟨214910505569117879371777565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 573094681517647678324740173 214910505569117879371777565)
              ·
                refine ⟨80591439588419204764416587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214910505569117879371777565 80591439588419204764416587)
                ·
                  refine ⟨120887159382628807146624881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80591439588419204764416587 120887159382628807146624881)
                  ·
                    refine ⟨90665369536971605359968661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120887159382628807146624881 90665369536971605359968661)
                    ·
                      refine ⟨4249939197045544001248531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90665369536971605359968661 4249939197045544001248531)
                      ·
                        rfl

theorem cell23_8276727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_8276727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276727 prefixEnd_8276727 := by exact prefixLift 8276727
  have htrace : WordTrace (prefixWord ++ tailWord_8276727) baseStart_8276727 baseEnd_8276727 := by
    simpa [prefixWord, tailWord_8276727, baseEnd_8276727] using wordTrace_append hprefix tailTrace_8276727
  have hstable : (prefixWord ++ tailWord_8276727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276727).length < 2 ^ (prefixWord ++ tailWord_8276727).sum := by decide
  have hdescent : baseEnd_8276727 < baseStart_8276727 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276747 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 7]
def baseStart_8276747 : Nat := 118140960795 + 8276747 * 2 ^ 59
def prefixEnd_8276747 : Nat := 4983230072969 + 3 ^ 40 * 8276747 * 2
def baseEnd_8276747 : Nat := 4249949466658633922998439

theorem tailTrace_8276747 : CollatzResearch.WordTrace tailWord_8276747 prefixEnd_8276747 4249949466658633922998439 := by
  unfold tailWord_8276747
  simp only [CollatzResearch.WordTrace]
  refine ⟨301877763345766649693780495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201251842230511099795853663 301877763345766649693780495)
  ·
    refine ⟨452816645018649974540670743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301877763345766649693780495 452816645018649974540670743)
    ·
      refine ⟨679224967527974961811006115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452816645018649974540670743 679224967527974961811006115)
      ·
        refine ⟨1018837451291962442716509173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679224967527974961811006115 1018837451291962442716509173)
        ·
          refine ⟨95516011058621479004672735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1018837451291962442716509173 95516011058621479004672735)
          ·
            refine ⟨143274016587932218507009103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95516011058621479004672735 143274016587932218507009103)
            ·
              refine ⟨214911024881898327760513655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143274016587932218507009103 214911024881898327760513655)
              ·
                refine ⟨322366537322847491640770483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214911024881898327760513655 322366537322847491640770483)
                ·
                  refine ⟨483549805984271237461155725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322366537322847491640770483 483549805984271237461155725)
                  ·
                    refine ⟨181331177244101714047933397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 483549805984271237461155725 181331177244101714047933397)
                    ·
                      refine ⟨4249949466658633922998439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 181331177244101714047933397 4249949466658633922998439)
                      ·
                        rfl

theorem cell23_8276747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 7].length) (baseStart_8276747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276747 prefixEnd_8276747 := by exact prefixLift 8276747
  have htrace : WordTrace (prefixWord ++ tailWord_8276747) baseStart_8276747 baseEnd_8276747 := by
    simpa [prefixWord, tailWord_8276747, baseEnd_8276747] using wordTrace_append hprefix tailTrace_8276747
  have hstable : (prefixWord ++ tailWord_8276747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276747).length < 2 ^ (prefixWord ++ tailWord_8276747).sum := by decide
  have hdescent : baseEnd_8276747 < baseStart_8276747 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276751 : List Nat := [1, 1, 2, 1, 1, 1, 7, 2, 3, 1, 3]
def baseStart_8276751 : Nat := 118140960795 + 8276751 * 2 ^ 59
def prefixEnd_8276751 : Nat := 4983230072969 + 3 ^ 40 * 8276751 * 2
def baseEnd_8276751 : Nat := 4249951520581251907348421

theorem tailTrace_8276751 : CollatzResearch.WordTrace tailWord_8276751 prefixEnd_8276751 4249951520581251907348421 := by
  unfold tailWord_8276751
  simp only [CollatzResearch.WordTrace]
  refine ⟨301877909237752158376926107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201251939491834772251284071 301877909237752158376926107)
  ·
    refine ⟨452816863856628237565389161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301877909237752158376926107 452816863856628237565389161)
    ·
      refine ⟨339612647892471178174041871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452816863856628237565389161 339612647892471178174041871)
      ·
        refine ⟨509418971838706767261062807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339612647892471178174041871 509418971838706767261062807)
        ·
          refine ⟨764128457758060150891594211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509418971838706767261062807 764128457758060150891594211)
          ·
            refine ⟨1146192686637090226337391317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764128457758060150891594211 1146192686637090226337391317)
            ·
              refine ⟨26863891093056802179782609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1146192686637090226337391317 26863891093056802179782609)
              ·
                refine ⟨20147918319792601634836957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26863891093056802179782609 20147918319792601634836957)
                ·
                  refine ⟨7555469369922225613063859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20147918319792601634836957 7555469369922225613063859)
                  ·
                    refine ⟨11333204054883338419595789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7555469369922225613063859 11333204054883338419595789)
                    ·
                      refine ⟨4249951520581251907348421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11333204054883338419595789 4249951520581251907348421)
                      ·
                        rfl

theorem cell23_8276751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3, 1, 3].length) (baseStart_8276751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276751 prefixEnd_8276751 := by exact prefixLift 8276751
  have htrace : WordTrace (prefixWord ++ tailWord_8276751) baseStart_8276751 baseEnd_8276751 := by
    simpa [prefixWord, tailWord_8276751, baseEnd_8276751] using wordTrace_append hprefix tailTrace_8276751
  have hstable : (prefixWord ++ tailWord_8276751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276751).length < 2 ^ (prefixWord ++ tailWord_8276751).sum := by decide
  have hdescent : baseEnd_8276751 < baseStart_8276751 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276761 : List Nat := [1, 2, 1, 2, 1, 1, 1, 7, 2, 3, 2]
def baseStart_8276761 : Nat := 118140960795 + 8276761 * 2 ^ 59
def prefixEnd_8276761 : Nat := 4983230072969 + 3 ^ 40 * 8276761 * 2
def baseEnd_8276761 : Nat := 4249956655387796868223375

theorem tailTrace_8276761 : CollatzResearch.WordTrace tailWord_8276761 prefixEnd_8276761 4249956655387796868223375 := by
  unfold tailWord_8276761
  simp only [CollatzResearch.WordTrace]
  refine ⟨301878273967715930084790137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201252182645143953389860091 301878273967715930084790137)
  ·
    refine ⟨226408705475786947563592603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301878273967715930084790137 226408705475786947563592603)
    ·
      refine ⟨339613058213680421345388905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226408705475786947563592603 339613058213680421345388905)
      ·
        refine ⟨254709793660260316009041679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339613058213680421345388905 254709793660260316009041679)
        ·
          refine ⟨382064690490390474013562519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254709793660260316009041679 382064690490390474013562519)
          ·
            refine ⟨573097035735585711020343779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382064690490390474013562519 573097035735585711020343779)
            ·
              refine ⟨859645553603378566530515669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573097035735585711020343779 859645553603378566530515669)
              ·
                refine ⟨20147942662579185153058961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 859645553603378566530515669 20147942662579185153058961)
                ·
                  refine ⟨15110956996934388864794221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20147942662579185153058961 15110956996934388864794221)
                  ·
                    refine ⟨5666608873850395824297833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15110956996934388864794221 5666608873850395824297833)
                    ·
                      refine ⟨4249956655387796868223375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5666608873850395824297833 4249956655387796868223375)
                      ·
                        rfl

theorem cell23_8276761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 3, 2].length) (baseStart_8276761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276761 prefixEnd_8276761 := by exact prefixLift 8276761
  have htrace : WordTrace (prefixWord ++ tailWord_8276761) baseStart_8276761 baseEnd_8276761 := by
    simpa [prefixWord, tailWord_8276761, baseEnd_8276761] using wordTrace_append hprefix tailTrace_8276761
  have hstable : (prefixWord ++ tailWord_8276761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276761).length < 2 ^ (prefixWord ++ tailWord_8276761).sum := by decide
  have hdescent : baseEnd_8276761 < baseStart_8276761 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276808 : List Nat := [2, 1, 3, 1, 1, 3, 1, 4, 3, 2, 2]
def baseStart_8276808 : Nat := 118140960795 + 8276808 * 2 ^ 59
def prefixEnd_8276808 : Nat := 4983230072969 + 3 ^ 40 * 8276808 * 2
def baseEnd_8276808 : Nat := 4249980788978558184335659

theorem tailTrace_8276808 : CollatzResearch.WordTrace tailWord_8276808 prefixEnd_8276808 4249980788978558184335659 := by
  unfold tailWord_8276808
  simp only [CollatzResearch.WordTrace]
  refine ⟨150939994099272828555875539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201253325465697104741167385 150939994099272828555875539)
  ·
    refine ⟨226409991148909242833813309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150939994099272828555875539 226409991148909242833813309)
    ·
      refine ⟨84903746680840966062679991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226409991148909242833813309 84903746680840966062679991)
      ·
        refine ⟨127355620021261449094019987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84903746680840966062679991 127355620021261449094019987)
        ·
          refine ⟨191033430031892173641029981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127355620021261449094019987 191033430031892173641029981)
          ·
            refine ⟨71637536261959565115386243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191033430031892173641029981 71637536261959565115386243)
            ·
              refine ⟨107456304392939347673079365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71637536261959565115386243 107456304392939347673079365)
              ·
                refine ⟨20148057073676127688702381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107456304392939347673079365 20148057073676127688702381)
                ·
                  refine ⟨7555521402628547883263393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20148057073676127688702381 7555521402628547883263393)
                  ·
                    refine ⟨5666641051971410912447545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7555521402628547883263393 5666641051971410912447545)
                    ·
                      refine ⟨4249980788978558184335659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5666641051971410912447545 4249980788978558184335659)
                      ·
                        rfl

theorem cell23_8276808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 3, 2, 2].length) (baseStart_8276808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276808 prefixEnd_8276808 := by exact prefixLift 8276808
  have htrace : WordTrace (prefixWord ++ tailWord_8276808) baseStart_8276808 baseEnd_8276808 := by
    simpa [prefixWord, tailWord_8276808, baseEnd_8276808] using wordTrace_append hprefix tailTrace_8276808
  have hstable : (prefixWord ++ tailWord_8276808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276808).length < 2 ^ (prefixWord ++ tailWord_8276808).sum := by decide
  have hdescent : baseEnd_8276808 < baseStart_8276808 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276828 : List Nat := [2, 2, 4, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_8276828 : Nat := 118140960795 + 8276828 * 2 ^ 59
def prefixEnd_8276828 : Nat := 4983230072969 + 3 ^ 40 * 8276828 * 2
def baseEnd_8276828 : Nat := 4249991058591648106085567

theorem tailTrace_8276828 : CollatzResearch.WordTrace tailWord_8276828 prefixEnd_8276828 4249991058591648106085567 := by
  unfold tailWord_8276828
  simp only [CollatzResearch.WordTrace]
  refine ⟨150940358829236600263739569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201253811772315467018319425 150940358829236600263739569)
  ·
    refine ⟨113205269121927450197804677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150940358829236600263739569 113205269121927450197804677)
    ·
      refine ⟨21225987960361396912088377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113205269121927450197804677 21225987960361396912088377)
      ·
        refine ⟨15919490970271047684066283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21225987960361396912088377 15919490970271047684066283)
        ·
          refine ⟨23879236455406571526099425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15919490970271047684066283 23879236455406571526099425)
          ·
            refine ⟨17909427341554928644574569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23879236455406571526099425 17909427341554928644574569)
            ·
              refine ⟨13432070506166196483430927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17909427341554928644574569 13432070506166196483430927)
              ·
                refine ⟨20148105759249294725146391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13432070506166196483430927 20148105759249294725146391)
                ·
                  refine ⟨30222158638873942087719587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20148105759249294725146391 30222158638873942087719587)
                  ·
                    refine ⟨45333237958310913131579381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30222158638873942087719587 45333237958310913131579381)
                    ·
                      refine ⟨4249991058591648106085567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45333237958310913131579381 4249991058591648106085567)
                      ·
                        rfl

theorem cell23_8276828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_8276828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276828 prefixEnd_8276828 := by exact prefixLift 8276828
  have htrace : WordTrace (prefixWord ++ tailWord_8276828) baseStart_8276828 baseEnd_8276828 := by
    simpa [prefixWord, tailWord_8276828, baseEnd_8276828] using wordTrace_append hprefix tailTrace_8276828
  have hstable : (prefixWord ++ tailWord_8276828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276828).length < 2 ^ (prefixWord ++ tailWord_8276828).sum := by decide
  have hdescent : baseEnd_8276828 < baseStart_8276828 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276844 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 2, 7]
def baseStart_8276844 : Nat := 118140960795 + 8276844 * 2 ^ 59
def prefixEnd_8276844 : Nat := 4983230072969 + 3 ^ 40 * 8276844 * 2
def baseEnd_8276844 : Nat := 1416666424760706681161831

theorem tailTrace_8276844 : CollatzResearch.WordTrace tailWord_8276844 prefixEnd_8276844 1416666424760706681161831 := by
  unfold tailWord_8276844
  simp only [CollatzResearch.WordTrace]
  refine ⟨150940650613207617630030793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201254200817610156840041057 150940650613207617630030793)
  ·
    refine ⟨113205487959905713222523095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150940650613207617630030793 113205487959905713222523095)
    ·
      refine ⟨169808231939858569833784643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113205487959905713222523095 169808231939858569833784643)
      ·
        refine ⟨254712347909787854750676965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169808231939858569833784643 254712347909787854750676965)
        ·
          refine ⟨47758565233085222765751931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254712347909787854750676965 47758565233085222765751931)
          ·
            refine ⟨71637847849627834148627897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47758565233085222765751931 71637847849627834148627897)
            ·
              refine ⟨53728385887220875611470923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71637847849627834148627897 53728385887220875611470923)
              ·
                refine ⟨80592578830831313417206385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53728385887220875611470923 80592578830831313417206385)
                ·
                  refine ⟨60444434123123485062904789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80592578830831313417206385 60444434123123485062904789)
                  ·
                    refine ⟨1416666424760706681161831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60444434123123485062904789 1416666424760706681161831)
                    ·
                      rfl

theorem cell23_8276844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_8276844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276844 prefixEnd_8276844 := by exact prefixLift 8276844
  have htrace : WordTrace (prefixWord ++ tailWord_8276844) baseStart_8276844 baseEnd_8276844 := by
    simpa [prefixWord, tailWord_8276844, baseEnd_8276844] using wordTrace_append hprefix tailTrace_8276844
  have hstable : (prefixWord ++ tailWord_8276844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276844).length < 2 ^ (prefixWord ++ tailWord_8276844).sum := by decide
  have hdescent : baseEnd_8276844 < baseStart_8276844 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276864 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 4]
def baseStart_8276864 : Nat := 118140960795 + 8276864 * 2 ^ 59
def prefixEnd_8276864 : Nat := 4983230072969 + 3 ^ 40 * 8276864 * 2
def baseEnd_8276864 : Nat := 4250009543895209965235401

theorem tailTrace_8276864 : CollatzResearch.WordTrace tailWord_8276864 prefixEnd_8276864 4250009543895209965235401 := by
  unfold tailWord_8276864
  simp only [CollatzResearch.WordTrace]
  refine ⟨150941015343171389337894823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201254687124228519117193097 150941015343171389337894823)
  ·
    refine ⟨226411523014757084006842235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150941015343171389337894823 226411523014757084006842235)
    ·
      refine ⟨339617284522135626010263353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226411523014757084006842235 339617284522135626010263353)
      ·
        refine ⟨254712963391601719507697515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339617284522135626010263353 254712963391601719507697515)
        ·
          refine ⟨382069445087402579261546273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254712963391601719507697515 382069445087402579261546273)
          ·
            refine ⟨286552083815551934446159705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382069445087402579261546273 286552083815551934446159705)
            ·
              refine ⟨214914062861663950834619779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286552083815551934446159705 214914062861663950834619779)
              ·
                refine ⟨322371094292495926251929669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214914062861663950834619779 322371094292495926251929669)
                ·
                  refine ⟨60444580179842986172236813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 322371094292495926251929669 60444580179842986172236813)
                  ·
                    refine ⟨22666717567441119814588805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60444580179842986172236813 22666717567441119814588805)
                    ·
                      refine ⟨4250009543895209965235401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22666717567441119814588805 4250009543895209965235401)
                      ·
                        rfl

theorem cell23_8276864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_8276864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276864 prefixEnd_8276864 := by exact prefixLift 8276864
  have htrace : WordTrace (prefixWord ++ tailWord_8276864) baseStart_8276864 baseEnd_8276864 := by
    simpa [prefixWord, tailWord_8276864, baseEnd_8276864] using wordTrace_append hprefix tailTrace_8276864
  have hstable : (prefixWord ++ tailWord_8276864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276864).length < 2 ^ (prefixWord ++ tailWord_8276864).sum := by decide
  have hdescent : baseEnd_8276864 < baseStart_8276864 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276892 : List Nat := [2, 2, 3, 3, 2, 1, 2, 2, 2, 1, 3]
def baseStart_8276892 : Nat := 118140960795 + 8276892 * 2 ^ 59
def prefixEnd_8276892 : Nat := 4983230072969 + 3 ^ 40 * 8276892 * 2
def baseEnd_8276892 : Nat := 4250023921353535855685273

theorem tailTrace_8276892 : CollatzResearch.WordTrace tailWord_8276892 prefixEnd_8276892 4250023921353535855685273 := by
  unfold tailWord_8276892
  simp only [CollatzResearch.WordTrace]
  refine ⟨150941525965120669728904465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201255367953494226305205953 150941525965120669728904465)
  ·
    refine ⟨113206144473840502296678349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150941525965120669728904465 113206144473840502296678349)
    ·
      refine ⟨42452304177690188361254381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113206144473840502296678349 42452304177690188361254381)
      ·
        refine ⟨15919614066633820635470393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42452304177690188361254381 15919614066633820635470393)
        ·
          refine ⟨11939710549975365476602795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15919614066633820635470393 11939710549975365476602795)
          ·
            refine ⟨17909565824963048214904193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11939710549975365476602795 17909565824963048214904193)
            ·
              refine ⟨13432174368722286161178145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17909565824963048214904193 13432174368722286161178145)
              ·
                refine ⟨10074130776541714620883609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13432174368722286161178145 10074130776541714620883609)
                ·
                  refine ⟨7555598082406285965662707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10074130776541714620883609 7555598082406285965662707)
                  ·
                    refine ⟨11333397123609428948494061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7555598082406285965662707 11333397123609428948494061)
                    ·
                      refine ⟨4250023921353535855685273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11333397123609428948494061 4250023921353535855685273)
                      ·
                        rfl

theorem cell23_8276892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_8276892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276892 prefixEnd_8276892 := by exact prefixLift 8276892
  have htrace : WordTrace (prefixWord ++ tailWord_8276892) baseStart_8276892 baseEnd_8276892 := by
    simpa [prefixWord, tailWord_8276892, baseEnd_8276892] using wordTrace_append hprefix tailTrace_8276892
  have hstable : (prefixWord ++ tailWord_8276892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276892).length < 2 ^ (prefixWord ++ tailWord_8276892).sum := by decide
  have hdescent : baseEnd_8276892 < baseStart_8276892 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276921 : List Nat := [1, 2, 1, 4, 2, 3, 1, 2, 7]
def baseStart_8276921 : Nat := 118140960795 + 8276921 * 2 ^ 59
def prefixEnd_8276921 : Nat := 4983230072969 + 3 ^ 40 * 8276921 * 2
def baseEnd_8276921 : Nat := 472226534699168471358071

theorem tailTrace_8276921 : CollatzResearch.WordTrace tailWord_8276921 prefixEnd_8276921 472226534699168471358071 := by
  unfold tailWord_8276921
  simp only [CollatzResearch.WordTrace]
  refine ⟨301884109647136277410614617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201256073098090851607076411 301884109647136277410614617)
  ·
    refine ⟨226413082235352208057960963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301884109647136277410614617 226413082235352208057960963)
    ·
      refine ⟨339619623353028312086941445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226413082235352208057960963 339619623353028312086941445)
      ·
        refine ⟨63678679378692808516301521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339619623353028312086941445 63678679378692808516301521)
        ·
          refine ⟨47759009534019606387226141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63678679378692808516301521 47759009534019606387226141)
          ·
            refine ⟨17909628575257352395209803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47759009534019606387226141 17909628575257352395209803)
            ·
              refine ⟨26864442862886028592814705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17909628575257352395209803 26864442862886028592814705)
              ·
                refine ⟨20148332147164521444611029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26864442862886028592814705 20148332147164521444611029)
                ·
                  refine ⟨472226534699168471358071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20148332147164521444611029 472226534699168471358071)
                  ·
                    rfl

theorem cell23_8276921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 7].length) (baseStart_8276921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276921 prefixEnd_8276921 := by exact prefixLift 8276921
  have htrace : WordTrace (prefixWord ++ tailWord_8276921) baseStart_8276921 baseEnd_8276921 := by
    simpa [prefixWord, tailWord_8276921, baseEnd_8276921] using wordTrace_append hprefix tailTrace_8276921
  have hstable : (prefixWord ++ tailWord_8276921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276921).length < 2 ^ (prefixWord ++ tailWord_8276921).sum := by decide
  have hdescent : baseEnd_8276921 < baseStart_8276921 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276948 : List Nat := [2, 4, 1, 2, 1, 2, 1, 2, 2, 3, 3]
def baseStart_8276948 : Nat := 118140960795 + 8276948 * 2 ^ 59
def prefixEnd_8276948 : Nat := 4983230072969 + 3 ^ 40 * 8276948 * 2
def baseEnd_8276948 : Nat := 4250052676270187636585015

theorem tailTrace_8276948 : CollatzResearch.WordTrace tailWord_8276948 prefixEnd_8276948 4250052676270187636585015 := by
  unfold tailWord_8276948
  simp only [CollatzResearch.WordTrace]
  refine ⟨150942547209019230510923749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201256729612025640681231665 150942547209019230510923749)
  ·
    refine ⟨28301727601691105720798203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150942547209019230510923749 28301727601691105720798203)
    ·
      refine ⟨42452591402536658581197305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28301727601691105720798203 42452591402536658581197305)
      ·
        refine ⟨31839443551902493935897979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42452591402536658581197305 31839443551902493935897979)
        ·
          refine ⟨47759165327853740903846969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31839443551902493935897979 47759165327853740903846969)
          ·
            refine ⟨35819373995890305677885227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47759165327853740903846969 35819373995890305677885227)
            ·
              refine ⟨53729060993835458516827841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35819373995890305677885227 53729060993835458516827841)
              ·
                refine ⟨40296795745376593887620881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53729060993835458516827841 40296795745376593887620881)
                ·
                  refine ⟨30222596809032445415715661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40296795745376593887620881 30222596809032445415715661)
                  ·
                    refine ⟨11333473803387167030893373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30222596809032445415715661 11333473803387167030893373)
                    ·
                      refine ⟨4250052676270187636585015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11333473803387167030893373 4250052676270187636585015)
                      ·
                        rfl

theorem cell23_8276948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_8276948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276948 prefixEnd_8276948 := by exact prefixLift 8276948
  have htrace : WordTrace (prefixWord ++ tailWord_8276948) baseStart_8276948 baseEnd_8276948 := by
    simpa [prefixWord, tailWord_8276948, baseEnd_8276948] using wordTrace_append hprefix tailTrace_8276948
  have hstable : (prefixWord ++ tailWord_8276948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276948).length < 2 ^ (prefixWord ++ tailWord_8276948).sum := by decide
  have hdescent : baseEnd_8276948 < baseStart_8276948 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8276949 : List Nat := [1, 3, 2, 3, 3, 2, 1, 2, 2, 2, 2]
def baseStart_8276949 : Nat := 118140960795 + 8276949 * 2 ^ 59
def prefixEnd_8276949 : Nat := 4983230072969 + 3 ^ 40 * 8276949 * 2
def baseEnd_8276949 : Nat := 4250053189750842132672511

theorem tailTrace_8276949 : CollatzResearch.WordTrace tailWord_8276949 prefixEnd_8276949 4250053189750842132672511 := by
  unfold tailWord_8276949
  simp only [CollatzResearch.WordTrace]
  refine ⟨301885130891034838192633901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201256753927356558795089267 301885130891034838192633901)
  ·
    refine ⟨113206924084138064322237713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301885130891034838192633901 113206924084138064322237713)
    ·
      refine ⟨84905193063103548241678285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113206924084138064322237713 84905193063103548241678285)
      ·
        refine ⟨31839447398663830590629357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84905193063103548241678285 31839447398663830590629357)
        ·
          refine ⟨11939792774498936471486009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31839447398663830590629357 11939792774498936471486009)
          ·
            refine ⟨8954844580874202353614507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11939792774498936471486009 8954844580874202353614507)
            ·
              refine ⟨13432266871311303530421761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8954844580874202353614507 13432266871311303530421761)
              ·
                refine ⟨10074200153483477647816321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13432266871311303530421761 10074200153483477647816321)
                ·
                  refine ⟨7555650115112608235862241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10074200153483477647816321 7555650115112608235862241)
                  ·
                    refine ⟨5666737586334456176896681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7555650115112608235862241 5666737586334456176896681)
                    ·
                      refine ⟨4250053189750842132672511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5666737586334456176896681 4250053189750842132672511)
                      ·
                        rfl

theorem cell23_8276949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_8276949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8276949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8276949 prefixEnd_8276949 := by exact prefixLift 8276949
  have htrace : WordTrace (prefixWord ++ tailWord_8276949) baseStart_8276949 baseEnd_8276949 := by
    simpa [prefixWord, tailWord_8276949, baseEnd_8276949] using wordTrace_append hprefix tailTrace_8276949
  have hstable : (prefixWord ++ tailWord_8276949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8276949).length < 2 ^ (prefixWord ++ tailWord_8276949).sum := by decide
  have hdescent : baseEnd_8276949 < baseStart_8276949 := by decide
  rcases family_descends (prefixWord ++ tailWord_8276949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277011 : List Nat := [1, 1, 1, 2, 1, 4, 1, 6, 6]
def baseStart_8277011 : Nat := 118140960795 + 8277011 * 2 ^ 59
def prefixEnd_8277011 : Nat := 4983230072969 + 3 ^ 40 * 8277011 * 2
def baseEnd_8277011 : Nat := 472231669505713432233025

theorem tailTrace_8277011 : CollatzResearch.WordTrace tailWord_8277011 prefixEnd_8277011 472231669505713432233025 := by
  unfold tailWord_8277011
  simp only [CollatzResearch.WordTrace]
  refine ⟨301887392216810222781390887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201258261477873481854260591 301887392216810222781390887)
  ·
    refine ⟨452831088325215334172086331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301887392216810222781390887 452831088325215334172086331)
    ·
      refine ⟨679246632487823001258129497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452831088325215334172086331 679246632487823001258129497)
      ·
        refine ⟨509434974365867250943597123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 679246632487823001258129497 509434974365867250943597123)
        ·
          refine ⟨764152461548800876415395685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509434974365867250943597123 764152461548800876415395685)
          ·
            refine ⟨143278586540400164327886691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 764152461548800876415395685 143278586540400164327886691)
            ·
              refine ⟨214917879810600246491830037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143278586540400164327886691 214917879810600246491830037)
              ·
                refine ⟨10074275616121886554304533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 214917879810600246491830037 10074275616121886554304533)
                ·
                  refine ⟨472231669505713432233025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10074275616121886554304533 472231669505713432233025)
                  ·
                    rfl

theorem cell23_8277011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 6].length) (baseStart_8277011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277011 prefixEnd_8277011 := by exact prefixLift 8277011
  have htrace : WordTrace (prefixWord ++ tailWord_8277011) baseStart_8277011 baseEnd_8277011 := by
    simpa [prefixWord, tailWord_8277011, baseEnd_8277011] using wordTrace_append hprefix tailTrace_8277011
  have hstable : (prefixWord ++ tailWord_8277011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277011).length < 2 ^ (prefixWord ++ tailWord_8277011).sum := by decide
  have hdescent : baseEnd_8277011 < baseStart_8277011 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277015 : List Nat := [1, 1, 3, 5, 1, 1, 3, 1, 3, 4]
def baseStart_8277015 : Nat := 118140960795 + 8277015 * 2 ^ 59
def prefixEnd_8277015 : Nat := 4983230072969 + 3 ^ 40 * 8277015 * 2
def baseEnd_8277015 : Nat := 1416695693158012958149069

theorem tailTrace_8277015 : CollatzResearch.WordTrace tailWord_8277015 prefixEnd_8277015 1416695693158012958149069 := by
  unfold tailWord_8277015
  simp only [CollatzResearch.WordTrace]
  refine ⟨301887538108795731464536499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201258358739197154309690999 301887538108795731464536499)
  ·
    refine ⟨452831307163193597196804749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301887538108795731464536499 452831307163193597196804749)
    ·
      refine ⟨169811740186197598948801781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452831307163193597196804749 169811740186197598948801781)
      ·
        refine ⟨15919850642456024901450167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169811740186197598948801781 15919850642456024901450167)
        ·
          refine ⟨23879775963684037352175251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15919850642456024901450167 23879775963684037352175251)
          ·
            refine ⟨35819663945526056028262877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23879775963684037352175251 35819663945526056028262877)
            ·
              refine ⟨13432373979572271010598579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35819663945526056028262877 13432373979572271010598579)
              ·
                refine ⟨20148560969358406515897869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13432373979572271010598579 20148560969358406515897869)
                ·
                  refine ⟨7555710363509402443461701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20148560969358406515897869 7555710363509402443461701)
                  ·
                    refine ⟨1416695693158012958149069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7555710363509402443461701 1416695693158012958149069)
                    ·
                      rfl

theorem cell23_8277015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3, 4].length) (baseStart_8277015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277015 prefixEnd_8277015 := by exact prefixLift 8277015
  have htrace : WordTrace (prefixWord ++ tailWord_8277015) baseStart_8277015 baseEnd_8277015 := by
    simpa [prefixWord, tailWord_8277015, baseEnd_8277015] using wordTrace_append hprefix tailTrace_8277015
  have hstable : (prefixWord ++ tailWord_8277015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277015).length < 2 ^ (prefixWord ++ tailWord_8277015).sum := by decide
  have hdescent : baseEnd_8277015 < baseStart_8277015 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277062 : List Nat := [6, 1, 1, 1, 1, 3, 2, 2, 6]
def baseStart_8277062 : Nat := 118140960795 + 8277062 * 2 ^ 59
def prefixEnd_8277062 : Nat := 4983230072969 + 3 ^ 40 * 8277062 * 2
def baseEnd_8277062 : Nat := 472234579229422243395499

theorem tailTrace_8277062 : CollatzResearch.WordTrace tailWord_8277062 prefixEnd_8277062 472234579229422243395499 := by
  unfold tailWord_8277062
  simp only [CollatzResearch.WordTrace]
  refine ⟨9434039135613295577859295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 201259501559750305660998293 9434039135613295577859295)
  ·
    refine ⟨14151058703419943366788943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9434039135613295577859295 14151058703419943366788943)
    ·
      refine ⟨21226588055129915050183415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14151058703419943366788943 21226588055129915050183415)
      ·
        refine ⟨31839882082694872575275123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21226588055129915050183415 31839882082694872575275123)
        ·
          refine ⟨47759823124042308862912685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31839882082694872575275123 47759823124042308862912685)
          ·
            refine ⟨17909933671515865823592257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47759823124042308862912685 17909933671515865823592257)
            ·
              refine ⟨13432450253636899367694193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17909933671515865823592257 13432450253636899367694193)
              ·
                refine ⟨10074337690227674525770645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13432450253636899367694193 10074337690227674525770645)
                ·
                  refine ⟨472234579229422243395499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10074337690227674525770645 472234579229422243395499)
                  ·
                    rfl

theorem cell23_8277062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_8277062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277062 prefixEnd_8277062 := by exact prefixLift 8277062
  have htrace : WordTrace (prefixWord ++ tailWord_8277062) baseStart_8277062 baseEnd_8277062 := by
    simpa [prefixWord, tailWord_8277062, baseEnd_8277062] using wordTrace_append hprefix tailTrace_8277062
  have hstable : (prefixWord ++ tailWord_8277062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277062).length < 2 ^ (prefixWord ++ tailWord_8277062).sum := by decide
  have hdescent : baseEnd_8277062 < baseStart_8277062 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277088 : List Nat := [2, 1, 1, 3, 2, 2, 4, 1, 1, 6]
def baseStart_8277088 : Nat := 118140960795 + 8277088 * 2 ^ 59
def prefixEnd_8277088 : Nat := 4983230072969 + 3 ^ 40 * 8277088 * 2
def baseEnd_8277088 : Nat := 1416708187853939029611457

theorem tailTrace_8277088 : CollatzResearch.WordTrace tailWord_8277088 prefixEnd_8277088 1416708187853939029611457 := by
  unfold tailWord_8277088
  simp only [CollatzResearch.WordTrace]
  refine ⟨150945100318765632465971959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201260133758354176621295945 150945100318765632465971959)
  ·
    refine ⟨226417650478148448698957939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150945100318765632465971959 226417650478148448698957939)
    ·
      refine ⟨339626475717222673048436909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226417650478148448698957939 339626475717222673048436909)
      ·
        refine ⟨127359928393958502393163841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339626475717222673048436909 127359928393958502393163841)
        ·
          refine ⟨95519946295468876794872881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127359928393958502393163841 95519946295468876794872881)
          ·
            refine ⟨71639959721601657596154661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95519946295468876794872881 71639959721601657596154661)
            ·
              refine ⟨13432492447800310799278999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71639959721601657596154661 13432492447800310799278999)
              ·
                refine ⟨20148738671700466198918499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13432492447800310799278999 20148738671700466198918499)
                ·
                  refine ⟨30223108007550699298377749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20148738671700466198918499 30223108007550699298377749)
                  ·
                    refine ⟨1416708187853939029611457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30223108007550699298377749 1416708187853939029611457)
                    ·
                      rfl

theorem cell23_8277088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 1, 6].length) (baseStart_8277088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277088 prefixEnd_8277088 := by exact prefixLift 8277088
  have htrace : WordTrace (prefixWord ++ tailWord_8277088) baseStart_8277088 baseEnd_8277088 := by
    simpa [prefixWord, tailWord_8277088, baseEnd_8277088] using wordTrace_append hprefix tailTrace_8277088
  have hstable : (prefixWord ++ tailWord_8277088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277088).length < 2 ^ (prefixWord ++ tailWord_8277088).sum := by decide
  have hdescent : baseEnd_8277088 < baseStart_8277088 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277129 : List Nat := [1, 2, 1, 1, 4, 3, 2, 4, 1, 2, 2]
def baseStart_8277129 : Nat := 118140960795 + 8277129 * 2 ^ 59
def prefixEnd_8277129 : Nat := 4983230072969 + 3 ^ 40 * 8277129 * 2
def baseEnd_8277129 : Nat := 4250145616268651428421683

theorem tailTrace_8277129 : CollatzResearch.WordTrace tailWord_8277129 prefixEnd_8277129 4250145616268651428421683 := by
  unfold tailWord_8277129
  simp only [CollatzResearch.WordTrace]
  refine ⟨301891696030382728934186441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201261130686921819289457627 301891696030382728934186441)
  ·
    refine ⟨226418772022787046700639831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301891696030382728934186441 226418772022787046700639831)
    ·
      refine ⟨339628158034180570050959747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226418772022787046700639831 339628158034180570050959747)
      ·
        refine ⟨509442237051270855076439621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339628158034180570050959747 509442237051270855076439621)
        ·
          refine ⟨95520419447113285326832429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 509442237051270855076439621 95520419447113285326832429)
          ·
            refine ⟨35820157292667481997562161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95520419447113285326832429 35820157292667481997562161)
            ·
              refine ⟨26865117969500611498171621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35820157292667481997562161 26865117969500611498171621)
              ·
                refine ⟨5037209619281364655907179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26865117969500611498171621 5037209619281364655907179)
                ·
                  refine ⟨7555814428922046983860769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5037209619281364655907179 7555814428922046983860769)
                  ·
                    refine ⟨5666860821691535237895577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7555814428922046983860769 5666860821691535237895577)
                    ·
                      refine ⟨4250145616268651428421683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5666860821691535237895577 4250145616268651428421683)
                      ·
                        rfl

theorem cell23_8277129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4, 1, 2, 2].length) (baseStart_8277129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277129 prefixEnd_8277129 := by exact prefixLift 8277129
  have htrace : WordTrace (prefixWord ++ tailWord_8277129) baseStart_8277129 baseEnd_8277129 := by
    simpa [prefixWord, tailWord_8277129, baseEnd_8277129] using wordTrace_append hprefix tailTrace_8277129
  have hstable : (prefixWord ++ tailWord_8277129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277129).length < 2 ^ (prefixWord ++ tailWord_8277129).sum := by decide
  have hdescent : baseEnd_8277129 < baseStart_8277129 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277131 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 1, 9]
def baseStart_8277131 : Nat := 118140960795 + 8277131 * 2 ^ 59
def prefixEnd_8277131 : Nat := 4983230072969 + 3 ^ 40 * 8277131 * 2
def baseEnd_8277131 : Nat := 1416715547743320140198891

theorem tailTrace_8277131 : CollatzResearch.WordTrace tailWord_8277131 prefixEnd_8277131 1416715547743320140198891 := by
  unfold tailWord_8277131
  simp only [CollatzResearch.WordTrace]
  refine ⟨301891768976375483275759247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201261179317583655517172831 301891768976375483275759247)
  ·
    refine ⟨452837653464563224913638871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301891768976375483275759247 452837653464563224913638871)
    ·
      refine ⟨679256480196844837370458307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452837653464563224913638871 679256480196844837370458307)
      ·
        refine ⟨1018884720295267256055687461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679256480196844837370458307 1018884720295267256055687461)
        ·
          refine ⟨191040885055362610510441399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1018884720295267256055687461 191040885055362610510441399)
          ·
            refine ⟨286561327583043915765662099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191040885055362610510441399 286561327583043915765662099)
            ·
              refine ⟨429841991374565873648493149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286561327583043915765662099 429841991374565873648493149)
              ·
                refine ⟨161190746765462202618184931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 429841991374565873648493149 161190746765462202618184931)
                ·
                  refine ⟨241786120148193303927277397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161190746765462202618184931 241786120148193303927277397)
                  ·
                    refine ⟨1416715547743320140198891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 241786120148193303927277397 1416715547743320140198891)
                    ·
                      rfl

theorem cell23_8277131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 9].length) (baseStart_8277131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277131 prefixEnd_8277131 := by exact prefixLift 8277131
  have htrace : WordTrace (prefixWord ++ tailWord_8277131) baseStart_8277131 baseEnd_8277131 := by
    simpa [prefixWord, tailWord_8277131, baseEnd_8277131] using wordTrace_append hprefix tailTrace_8277131
  have hstable : (prefixWord ++ tailWord_8277131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277131).length < 2 ^ (prefixWord ++ tailWord_8277131).sum := by decide
  have hdescent : baseEnd_8277131 < baseStart_8277131 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277155 : List Nat := [1, 1, 1, 4, 1, 1, 1, 5, 3, 3, 2]
def baseStart_8277155 : Nat := 118140960795 + 8277155 * 2 ^ 59
def prefixEnd_8277155 : Nat := 4983230072969 + 3 ^ 40 * 8277155 * 2
def baseEnd_8277155 : Nat := 4250158966765668326696563

theorem tailTrace_8277155 : CollatzResearch.WordTrace tailWord_8277155 prefixEnd_8277155 4250158966765668326696563 := by
  unfold tailWord_8277155
  simp only [CollatzResearch.WordTrace]
  refine ⟨301892644328288535374632919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201261762885525690249755279 301892644328288535374632919)
  ·
    refine ⟨452838966492432803061949379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301892644328288535374632919 452838966492432803061949379)
    ·
      refine ⟨679258449738649204592924069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452838966492432803061949379 679258449738649204592924069)
      ·
        refine ⟨127360959325996725861173263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 679258449738649204592924069 127360959325996725861173263)
        ·
          refine ⟨191041438988995088791759895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127360959325996725861173263 191041438988995088791759895)
          ·
            refine ⟨286562158483492633187639843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191041438988995088791759895 286562158483492633187639843)
            ·
              refine ⟨429843237725238949781459765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286562158483492633187639843 429843237725238949781459765)
              ·
                refine ⟨40297803536741151542011853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 429843237725238949781459765 40297803536741151542011853)
                ·
                  refine ⟨15111676326277931828254445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40297803536741151542011853 15111676326277931828254445)
                  ·
                    refine ⟨5666878622354224435595417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15111676326277931828254445 5666878622354224435595417)
                    ·
                      refine ⟨4250158966765668326696563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5666878622354224435595417 4250158966765668326696563)
                      ·
                        rfl

theorem cell23_8277155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 3, 2].length) (baseStart_8277155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277155 prefixEnd_8277155 := by exact prefixLift 8277155
  have htrace : WordTrace (prefixWord ++ tailWord_8277155) baseStart_8277155 baseEnd_8277155 := by
    simpa [prefixWord, tailWord_8277155, baseEnd_8277155] using wordTrace_append hprefix tailTrace_8277155
  have hstable : (prefixWord ++ tailWord_8277155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277155).length < 2 ^ (prefixWord ++ tailWord_8277155).sum := by decide
  have hdescent : baseEnd_8277155 < baseStart_8277155 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277190 : List Nat := [6, 1, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_8277190 : Nat := 118140960795 + 8277190 * 2 ^ 59
def prefixEnd_8277190 : Nat := 4983230072969 + 3 ^ 40 * 8277190 * 2
def baseEnd_8277190 : Nat := 1416725646196191896586301

theorem tailTrace_8277190 : CollatzResearch.WordTrace tailWord_8277190 prefixEnd_8277190 1416725646196191896586301 := by
  unfold tailWord_8277190
  simp only [CollatzResearch.WordTrace]
  refine ⟨9434185027598804261004907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 201262613922107824234771349 9434185027598804261004907)
  ·
    refine ⟨14151277541398206391507361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9434185027598804261004907 14151277541398206391507361)
    ·
      refine ⟨10613458156048654793630521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14151277541398206391507361 10613458156048654793630521)
      ·
        refine ⟨7960093617036491095222891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10613458156048654793630521 7960093617036491095222891)
        ·
          refine ⟨11940140425554736642834337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7960093617036491095222891 11940140425554736642834337)
          ·
            refine ⟨8955105319166052482125753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11940140425554736642834337 8955105319166052482125753)
            ·
              refine ⟨6716328989374539361594315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8955105319166052482125753 6716328989374539361594315)
              ·
                refine ⟨10074493484061809042391473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6716328989374539361594315 10074493484061809042391473)
                ·
                  refine ⟨7555870113046356781793605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10074493484061809042391473 7555870113046356781793605)
                  ·
                    refine ⟨1416725646196191896586301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7555870113046356781793605 1416725646196191896586301)
                    ·
                      rfl

theorem cell23_8277190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_8277190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277190 prefixEnd_8277190 := by exact prefixLift 8277190
  have htrace : WordTrace (prefixWord ++ tailWord_8277190) baseStart_8277190 baseEnd_8277190 := by
    simpa [prefixWord, tailWord_8277190, baseEnd_8277190] using wordTrace_append hprefix tailTrace_8277190
  have hstable : (prefixWord ++ tailWord_8277190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277190).length < 2 ^ (prefixWord ++ tailWord_8277190).sum := by decide
  have hdescent : baseEnd_8277190 < baseStart_8277190 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277202 : List Nat := [3, 2, 2, 2, 1, 1, 2, 3, 1, 4, 2]
def baseStart_8277202 : Nat := 118140960795 + 8277202 * 2 ^ 59
def prefixEnd_8277202 : Nat := 4983230072969 + 3 ^ 40 * 8277202 * 2
def baseEnd_8277202 : Nat := 4250183100356429642808847

theorem tailTrace_8277202 : CollatzResearch.WordTrace tailWord_8277202 prefixEnd_8277202 4250183100356429642808847 := by
  unfold tailWord_8277202
  simp only [CollatzResearch.WordTrace]
  refine ⟨75473589639779565600398465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201262905706078841601062573 75473589639779565600398465)
  ·
    refine ⟨56605192229834674200298849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75473589639779565600398465 56605192229834674200298849)
    ·
      refine ⟨42453894172376005650224137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56605192229834674200298849 42453894172376005650224137)
      ·
        refine ⟨31840420629282004237668103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42453894172376005650224137 31840420629282004237668103)
        ·
          refine ⟨47760630943923006356502155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31840420629282004237668103 47760630943923006356502155)
          ·
            refine ⟨71640946415884509534753233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47760630943923006356502155 71640946415884509534753233)
            ·
              refine ⟨53730709811913382151064925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71640946415884509534753233 53730709811913382151064925)
              ·
                refine ⟨20149016179467518306649347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53730709811913382151064925 20149016179467518306649347)
                ·
                  refine ⟨30223524269201277459974021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20149016179467518306649347 30223524269201277459974021)
                  ·
                    refine ⟨5666910800475239523745129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30223524269201277459974021 5666910800475239523745129)
                    ·
                      refine ⟨4250183100356429642808847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5666910800475239523745129 4250183100356429642808847)
                      ·
                        rfl

theorem cell23_8277202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_8277202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277202 prefixEnd_8277202 := by exact prefixLift 8277202
  have htrace : WordTrace (prefixWord ++ tailWord_8277202) baseStart_8277202 baseEnd_8277202 := by
    simpa [prefixWord, tailWord_8277202, baseEnd_8277202] using wordTrace_append hprefix tailTrace_8277202
  have hstable : (prefixWord ++ tailWord_8277202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277202).length < 2 ^ (prefixWord ++ tailWord_8277202).sum := by decide
  have hdescent : baseEnd_8277202 < baseStart_8277202 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277205 : List Nat := [1, 3, 2, 4, 1, 1, 1, 2, 2, 1, 5]
def baseStart_8277205 : Nat := 118140960795 + 8277205 * 2 ^ 59
def prefixEnd_8277205 : Nat := 4983230072969 + 3 ^ 40 * 8277205 * 2
def baseEnd_8277205 : Nat := 4250184640798393131071333

theorem tailTrace_8277205 : CollatzResearch.WordTrace tailWord_8277205 prefixEnd_8277205 4250184640798393131071333 := by
  unfold tailWord_8277205
  simp only [CollatzResearch.WordTrace]
  refine ⟨301894467978107393913953069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201262978652071595942635379 301894467978107393913953069)
  ·
    refine ⟨113210425491790272717732401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301894467978107393913953069 113210425491790272717732401)
    ·
      refine ⟨84907819118842704538299301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113210425491790272717732401 84907819118842704538299301)
      ·
        refine ⟨15920216084783007100931119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84907819118842704538299301 15920216084783007100931119)
        ·
          refine ⟨23880324127174510651396679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15920216084783007100931119 23880324127174510651396679)
          ·
            refine ⟨35820486190761765977095019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23880324127174510651396679 35820486190761765977095019)
            ·
              refine ⟨53730729286142648965642529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35820486190761765977095019 53730729286142648965642529)
              ·
                refine ⟨40298046964606986724231897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53730729286142648965642529 40298046964606986724231897)
                ·
                  refine ⟨30223535223455240043173923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40298046964606986724231897 30223535223455240043173923)
                  ·
                    refine ⟨45335302835182860064760885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30223535223455240043173923 45335302835182860064760885)
                    ·
                      refine ⟨4250184640798393131071333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45335302835182860064760885 4250184640798393131071333)
                      ·
                        rfl

theorem cell23_8277205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_8277205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277205 prefixEnd_8277205 := by exact prefixLift 8277205
  have htrace : WordTrace (prefixWord ++ tailWord_8277205) baseStart_8277205 baseEnd_8277205 := by
    simpa [prefixWord, tailWord_8277205, baseEnd_8277205] using wordTrace_append hprefix tailTrace_8277205
  have hstable : (prefixWord ++ tailWord_8277205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277205).length < 2 ^ (prefixWord ++ tailWord_8277205).sum := by decide
  have hdescent : baseEnd_8277205 < baseStart_8277205 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277206 : List Nat := [5, 2, 1, 2, 2, 1, 1, 1, 3, 3, 2]
def baseStart_8277206 : Nat := 118140960795 + 8277206 * 2 ^ 59
def prefixEnd_8277206 : Nat := 4983230072969 + 3 ^ 40 * 8277206 * 2
def baseEnd_8277206 : Nat := 4250185154279047627158829

theorem tailTrace_8277206 : CollatzResearch.WordTrace tailWord_8277206 prefixEnd_8277206 4250185154279047627158829 := by
  unfold tailWord_8277206
  simp only [CollatzResearch.WordTrace]
  refine ⟨18868406528193985692796217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201263002967402514056492981 18868406528193985692796217)
  ·
    refine ⟨14151304896145489269597163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18868406528193985692796217 14151304896145489269597163)
    ·
      refine ⟨21226957344218233904395745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14151304896145489269597163 21226957344218233904395745)
      ·
        refine ⟨15920218008163675428296809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21226957344218233904395745 15920218008163675428296809)
        ·
          refine ⟨11940163506122756571222607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15920218008163675428296809 11940163506122756571222607)
          ·
            refine ⟨17910245259184134856833911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11940163506122756571222607 17910245259184134856833911)
            ·
              refine ⟨26865367888776202285250867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17910245259184134856833911 26865367888776202285250867)
              ·
                refine ⟨40298051833164303427876301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26865367888776202285250867 40298051833164303427876301)
                ·
                  refine ⟨15111769437436613785453613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40298051833164303427876301 15111769437436613785453613)
                  ·
                    refine ⟨5666913539038730169545105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15111769437436613785453613 5666913539038730169545105)
                    ·
                      refine ⟨4250185154279047627158829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5666913539038730169545105 4250185154279047627158829)
                      ·
                        rfl

theorem cell23_8277206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_8277206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277206 prefixEnd_8277206 := by exact prefixLift 8277206
  have htrace : WordTrace (prefixWord ++ tailWord_8277206) baseStart_8277206 baseEnd_8277206 := by
    simpa [prefixWord, tailWord_8277206, baseEnd_8277206] using wordTrace_append hprefix tailTrace_8277206
  have hstable : (prefixWord ++ tailWord_8277206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277206).length < 2 ^ (prefixWord ++ tailWord_8277206).sum := by decide
  have hdescent : baseEnd_8277206 < baseStart_8277206 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277252 : List Nat := [2, 3, 2, 2, 2, 2, 1, 1, 2, 3, 3]
def baseStart_8277252 : Nat := 118140960795 + 8277252 * 2 ^ 59
def prefixEnd_8277252 : Nat := 4983230072969 + 3 ^ 40 * 8277252 * 2
def baseEnd_8277252 : Nat := 4250208774389154447183617

theorem tailTrace_8277252 : CollatzResearch.WordTrace tailWord_8277252 prefixEnd_8277252 4250208774389154447183617 := by
  unfold tailWord_8277252
  simp only [CollatzResearch.WordTrace]
  refine ⟨150948091104468560470457005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201264121472624747293942673 150948091104468560470457005)
  ·
    refine ⟨56605534164175710176421377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150948091104468560470457005 56605534164175710176421377)
    ·
      refine ⟨42454150623131782632316033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56605534164175710176421377 42454150623131782632316033)
      ·
        refine ⟨31840612967348836974237025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42454150623131782632316033 31840612967348836974237025)
        ·
          refine ⟨23880459725511627730677769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31840612967348836974237025 23880459725511627730677769)
          ·
            refine ⟨17910344794133720798008327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23880459725511627730677769 17910344794133720798008327)
            ·
              refine ⟨26865517191200581197012491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17910344794133720798008327 26865517191200581197012491)
              ·
                refine ⟨40298275786800871795518737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26865517191200581197012491 40298275786800871795518737)
                ·
                  refine ⟨30223706840100653846639053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40298275786800871795518737 30223706840100653846639053)
                  ·
                    refine ⟨11333890065037745192489645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30223706840100653846639053 11333890065037745192489645)
                    ·
                      refine ⟨4250208774389154447183617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11333890065037745192489645 4250208774389154447183617)
                      ·
                        rfl

theorem cell23_8277252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_8277252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277252 prefixEnd_8277252 := by exact prefixLift 8277252
  have htrace : WordTrace (prefixWord ++ tailWord_8277252) baseStart_8277252 baseEnd_8277252 := by
    simpa [prefixWord, tailWord_8277252, baseEnd_8277252] using wordTrace_append hprefix tailTrace_8277252
  have hstable : (prefixWord ++ tailWord_8277252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277252).length < 2 ^ (prefixWord ++ tailWord_8277252).sum := by decide
  have hdescent : baseEnd_8277252 < baseStart_8277252 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277272 : List Nat := [2, 1, 2, 3, 1, 5, 1, 1, 2, 5]
def baseStart_8277272 : Nat := 118140960795 + 8277272 * 2 ^ 59
def prefixEnd_8277272 : Nat := 4983230072969 + 3 ^ 40 * 8277272 * 2
def baseEnd_8277272 : Nat := 1416739681334081456311175

theorem tailTrace_8277272 : CollatzResearch.WordTrace tailWord_8277272 prefixEnd_8277272 1416739681334081456311175 := by
  unfold tailWord_8277272
  simp only [CollatzResearch.WordTrace]
  refine ⟨150948455834432332178321035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201264607779243109571094713 150948455834432332178321035)
  ·
    refine ⟨226422683751648498267481553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150948455834432332178321035 226422683751648498267481553)
    ·
      refine ⟨169817012813736373700611165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226422683751648498267481553 169817012813736373700611165)
      ·
        refine ⟨63681379805151140137729187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169817012813736373700611165 63681379805151140137729187)
        ·
          refine ⟨95522069707726710206593781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63681379805151140137729187 95522069707726710206593781)
          ·
            refine ⟨8955194035099379081868167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95522069707726710206593781 8955194035099379081868167)
            ·
              refine ⟨13432791052649068622802251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8955194035099379081868167 13432791052649068622802251)
              ·
                refine ⟨20149186578973602934203377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13432791052649068622802251 20149186578973602934203377)
                ·
                  refine ⟨15111889934230202200652533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20149186578973602934203377 15111889934230202200652533)
                  ·
                    refine ⟨1416739681334081456311175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15111889934230202200652533 1416739681334081456311175)
                    ·
                      rfl

theorem cell23_8277272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 2, 5].length) (baseStart_8277272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277272 prefixEnd_8277272 := by exact prefixLift 8277272
  have htrace : WordTrace (prefixWord ++ tailWord_8277272) baseStart_8277272 baseEnd_8277272 := by
    simpa [prefixWord, tailWord_8277272, baseEnd_8277272] using wordTrace_append hprefix tailTrace_8277272
  have hstable : (prefixWord ++ tailWord_8277272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277272).length < 2 ^ (prefixWord ++ tailWord_8277272).sum := by decide
  have hdescent : baseEnd_8277272 < baseStart_8277272 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277275 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 3, 6, 2]
def baseStart_8277275 : Nat := 118140960795 + 8277275 * 2 ^ 59
def prefixEnd_8277275 : Nat := 4983230072969 + 3 ^ 40 * 8277275 * 2
def baseEnd_8277275 : Nat := 4250220584444207857196011

theorem tailTrace_8277275 : CollatzResearch.WordTrace tailWord_8277275 prefixEnd_8277275 4250220584444207857196011 := by
  unfold tailWord_8277275
  simp only [CollatzResearch.WordTrace]
  refine ⟨301897021087853795869001279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201264680725235863912667519 301897021087853795869001279)
  ·
    refine ⟨452845531631780693803501919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301897021087853795869001279 452845531631780693803501919)
    ·
      refine ⟨679268297447671040705252879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452845531631780693803501919 679268297447671040705252879)
      ·
        refine ⟨1018902446171506561057879319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679268297447671040705252879 1018902446171506561057879319)
        ·
          refine ⟨1528353669257259841586818979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1018902446171506561057879319 1528353669257259841586818979)
          ·
            refine ⟨2292530503885889762380228469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1528353669257259841586818979 2292530503885889762380228469)
            ·
              refine ⟨214924734739302165223146419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2292530503885889762380228469 214924734739302165223146419)
              ·
                refine ⟨322387102108953247834719629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214924734739302165223146419 322387102108953247834719629)
                ·
                  refine ⟨120895163290857467938019861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322387102108953247834719629 120895163290857467938019861)
                  ·
                    refine ⟨5666960779258943809594681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 120895163290857467938019861 5666960779258943809594681)
                    ·
                      refine ⟨4250220584444207857196011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5666960779258943809594681 4250220584444207857196011)
                      ·
                        rfl

theorem cell23_8277275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 6, 2].length) (baseStart_8277275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277275 prefixEnd_8277275 := by exact prefixLift 8277275
  have htrace : WordTrace (prefixWord ++ tailWord_8277275) baseStart_8277275 baseEnd_8277275 := by
    simpa [prefixWord, tailWord_8277275, baseEnd_8277275] using wordTrace_append hprefix tailTrace_8277275
  have hstable : (prefixWord ++ tailWord_8277275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277275).length < 2 ^ (prefixWord ++ tailWord_8277275).sum := by decide
  have hdescent : baseEnd_8277275 < baseStart_8277275 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277295 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 4, 2, 3]
def baseStart_8277295 : Nat := 118140960795 + 8277295 * 2 ^ 59
def prefixEnd_8277295 : Nat := 4983230072969 + 3 ^ 40 * 8277295 * 2
def baseEnd_8277295 : Nat := 4250230854057297778945919

theorem tailTrace_8277295 : CollatzResearch.WordTrace tailWord_8277295 prefixEnd_8277295 4250230854057297778945919 := by
  unfold tailWord_8277295
  simp only [CollatzResearch.WordTrace]
  refine ⟨301897750547781339284729339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201265167031854226189819559 301897750547781339284729339)
  ·
    refine ⟨452846625821672008927094009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301897750547781339284729339 452846625821672008927094009)
    ·
      refine ⟨339634969366254006695320507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452846625821672008927094009 339634969366254006695320507)
      ·
        refine ⟨509452454049381010042980761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339634969366254006695320507 509452454049381010042980761)
        ·
          refine ⟨382089340537035757532235571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 509452454049381010042980761 382089340537035757532235571)
          ·
            refine ⟨573134010805553636298353357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382089340537035757532235571 573134010805553636298353357)
            ·
              refine ⟨214925254052082613611882509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 573134010805553636298353357 214925254052082613611882509)
              ·
                refine ⟨80596970269530980104455941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214925254052082613611882509 80596970269530980104455941)
                ·
                  refine ⟨15111931925537058769585489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80596970269530980104455941 15111931925537058769585489)
                  ·
                    refine ⟨11333948944152794077189117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15111931925537058769585489 11333948944152794077189117)
                    ·
                      refine ⟨4250230854057297778945919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11333948944152794077189117 4250230854057297778945919)
                      ·
                        rfl

theorem cell23_8277295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2, 3].length) (baseStart_8277295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277295 prefixEnd_8277295 := by exact prefixLift 8277295
  have htrace : WordTrace (prefixWord ++ tailWord_8277295) baseStart_8277295 baseEnd_8277295 := by
    simpa [prefixWord, tailWord_8277295, baseEnd_8277295] using wordTrace_append hprefix tailTrace_8277295
  have hstable : (prefixWord ++ tailWord_8277295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277295).length < 2 ^ (prefixWord ++ tailWord_8277295).sum := by decide
  have hdescent : baseEnd_8277295 < baseStart_8277295 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277379 : List Nat := [1, 1, 1, 3, 5, 3, 1, 2, 1, 5]
def baseStart_8277379 : Nat := 118140960795 + 8277379 * 2 ^ 59
def prefixEnd_8277379 : Nat := 4983230072969 + 3 ^ 40 * 8277379 * 2
def baseEnd_8277379 : Nat := 1416757995477425150098511

theorem tailTrace_8277379 : CollatzResearch.WordTrace tailWord_8277379 prefixEnd_8277379 1416757995477425150098511 := by
  unfold tailWord_8277379
  simp only [CollatzResearch.WordTrace]
  refine ⟨301900814279477021630787191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201267209519651347753858127 301900814279477021630787191)
  ·
    refine ⟨452851221419215532446180787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301900814279477021630787191 452851221419215532446180787)
    ·
      refine ⟨679276832128823298669271181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452851221419215532446180787 679276832128823298669271181)
      ·
        refine ⟨254728812048308737000976693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 679276832128823298669271181 254728812048308737000976693)
        ·
          refine ⟨23880826129528944093841565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 254728812048308737000976693 23880826129528944093841565)
          ·
            refine ⟨8955309798573354035190587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23880826129528944093841565 8955309798573354035190587)
            ·
              refine ⟨13432964697860031052785881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8955309798573354035190587 13432964697860031052785881)
              ·
                refine ⟨10074723523395023289589411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13432964697860031052785881 10074723523395023289589411)
                ·
                  refine ⟨15112085285092534934384117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10074723523395023289589411 15112085285092534934384117)
                  ·
                    refine ⟨1416757995477425150098511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15112085285092534934384117 1416757995477425150098511)
                    ·
                      rfl

theorem cell23_8277379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 5].length) (baseStart_8277379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277379 prefixEnd_8277379 := by exact prefixLift 8277379
  have htrace : WordTrace (prefixWord ++ tailWord_8277379) baseStart_8277379 baseEnd_8277379 := by
    simpa [prefixWord, tailWord_8277379, baseEnd_8277379] using wordTrace_append hprefix tailTrace_8277379
  have hstable : (prefixWord ++ tailWord_8277379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277379).length < 2 ^ (prefixWord ++ tailWord_8277379).sum := by decide
  have hdescent : baseEnd_8277379 < baseStart_8277379 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277396 : List Nat := [2, 4, 2, 1, 2, 2, 3, 1, 1, 5]
def baseStart_8277396 : Nat := 118140960795 + 8277396 * 2 ^ 59
def prefixEnd_8277396 : Nat := 4983230072969 + 3 ^ 40 * 8277396 * 2
def baseEnd_8277396 : Nat := 1416760905201133961260985

theorem tailTrace_8277396 : CollatzResearch.WordTrace tailWord_8277396 prefixEnd_8277396 1416760905201133961260985 := by
  unfold tailWord_8277396
  simp only [CollatzResearch.WordTrace]
  refine ⟨150950717160207716767078021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201267622880276955689437361 150950717160207716767078021)
  ·
    refine ⟨28303259467538946893827129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150950717160207716767078021 28303259467538946893827129)
    ·
      refine ⟨21227444600654210170370347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28303259467538946893827129 21227444600654210170370347)
      ·
        refine ⟨31841166900981315255555521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21227444600654210170370347 31841166900981315255555521)
        ·
          refine ⟨23880875175735986441666641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31841166900981315255555521 23880875175735986441666641)
          ·
            refine ⟨17910656381801989831249981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23880875175735986441666641 17910656381801989831249981)
            ·
              refine ⟨6716496143175746186718743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17910656381801989831249981 6716496143175746186718743)
              ·
                refine ⟨10074744214763619280078115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6716496143175746186718743 10074744214763619280078115)
                ·
                  refine ⟨15112116322145428920117173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10074744214763619280078115 15112116322145428920117173)
                  ·
                    refine ⟨1416760905201133961260985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15112116322145428920117173 1416760905201133961260985)
                    ·
                      rfl

theorem cell23_8277396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_8277396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277396 prefixEnd_8277396 := by exact prefixLift 8277396
  have htrace : WordTrace (prefixWord ++ tailWord_8277396) baseStart_8277396 baseEnd_8277396 := by
    simpa [prefixWord, tailWord_8277396, baseEnd_8277396] using wordTrace_append hprefix tailTrace_8277396
  have hstable : (prefixWord ++ tailWord_8277396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277396).length < 2 ^ (prefixWord ++ tailWord_8277396).sum := by decide
  have hdescent : baseEnd_8277396 < baseStart_8277396 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277405 : List Nat := [1, 4, 2, 1, 3, 12]
def baseStart_8277405 : Nat := 118140960795 + 8277405 * 2 ^ 59
def prefixEnd_8277405 : Nat := 4983230072969 + 3 ^ 40 * 8277405 * 2
def baseEnd_8277405 : Nat := 17490894390655524068191

theorem tailTrace_8277405 : CollatzResearch.WordTrace tailWord_8277405 prefixEnd_8277405 17490894390655524068191 := by
  unfold tailWord_8277405
  simp only [CollatzResearch.WordTrace]
  refine ⟨301901762577382828071233669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201267841718255218714155779 301901762577382828071233669)
  ·
    refine ⟨56606580483259280263356313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301901762577382828071233669 56606580483259280263356313)
    ·
      refine ⟨42454935362444460197517235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56606580483259280263356313 42454935362444460197517235)
      ·
        refine ⟨63682403043666690296275853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42454935362444460197517235 63682403043666690296275853)
        ·
          refine ⟨23880901141375008861103445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63682403043666690296275853 23880901141375008861103445)
          ·
            refine ⟨17490894390655524068191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 23880901141375008861103445 17490894390655524068191)
            ·
              rfl

theorem cell23_8277405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 12].length) (baseStart_8277405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277405 prefixEnd_8277405 := by exact prefixLift 8277405
  have htrace : WordTrace (prefixWord ++ tailWord_8277405) baseStart_8277405 baseEnd_8277405 := by
    simpa [prefixWord, tailWord_8277405, baseEnd_8277405] using wordTrace_append hprefix tailTrace_8277405
  have hstable : (prefixWord ++ tailWord_8277405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277405).length < 2 ^ (prefixWord ++ tailWord_8277405).sum := by decide
  have hdescent : baseEnd_8277405 < baseStart_8277405 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277410 : List Nat := [3, 3, 1, 2, 1, 4, 2, 2, 1, 1, 3]
def baseStart_8277410 : Nat := 118140960795 + 8277410 * 2 ^ 59
def prefixEnd_8277410 : Nat := 4983230072969 + 3 ^ 40 * 8277410 * 2
def baseEnd_8277410 : Nat := 4250289904332564829007891

theorem tailTrace_8277410 : CollatzResearch.WordTrace tailWord_8277410 prefixEnd_8277410 4250289904332564829007891 := by
  unfold tailWord_8277410
  simp only [CollatzResearch.WordTrace]
  refine ⟨75475486235591178481291421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201267963294909809283443789 75475486235591178481291421)
  ·
    refine ⟨28303307338346691930484283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75475486235591178481291421 28303307338346691930484283)
    ·
      refine ⟨42454961007520037895726425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28303307338346691930484283 42454961007520037895726425)
      ·
        refine ⟨31841220755640028421794819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42454961007520037895726425 31841220755640028421794819)
        ·
          refine ⟨47761831133460042632692229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31841220755640028421794819 47761831133460042632692229)
          ·
            refine ⟨8955343337523757993629793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47761831133460042632692229 8955343337523757993629793)
            ·
              refine ⟨6716507503142818495222345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8955343337523757993629793 6716507503142818495222345)
              ·
                refine ⟨5037380627357113871416759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6716507503142818495222345 5037380627357113871416759)
                ·
                  refine ⟨7556070941035670807125139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5037380627357113871416759 7556070941035670807125139)
                  ·
                    refine ⟨11334106411553506210687709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7556070941035670807125139 11334106411553506210687709)
                    ·
                      refine ⟨4250289904332564829007891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11334106411553506210687709 4250289904332564829007891)
                      ·
                        rfl

theorem cell23_8277410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_8277410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277410 prefixEnd_8277410 := by exact prefixLift 8277410
  have htrace : WordTrace (prefixWord ++ tailWord_8277410) baseStart_8277410 baseEnd_8277410 := by
    simpa [prefixWord, tailWord_8277410, baseEnd_8277410] using wordTrace_append hprefix tailTrace_8277410
  have hstable : (prefixWord ++ tailWord_8277410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277410).length < 2 ^ (prefixWord ++ tailWord_8277410).sum := by decide
  have hdescent : baseEnd_8277410 < baseStart_8277410 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277429 : List Nat := [1, 3, 3, 2, 2, 2, 2, 1, 1, 2, 4]
def baseStart_8277429 : Nat := 118140960795 + 8277429 * 2 ^ 59
def prefixEnd_8277429 : Nat := 4983230072969 + 3 ^ 40 * 8277429 * 2
def baseEnd_8277429 : Nat := 4250299660465000254670303

theorem tailTrace_8277429 : CollatzResearch.WordTrace tailWord_8277429 prefixEnd_8277429 4250299660465000254670303 := by
  unfold tailWord_8277429
  simp only [CollatzResearch.WordTrace]
  refine ⟨301902637929295880170107341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201268425286197253446738227 301902637929295880170107341)
  ·
    refine ⟨113213489223485955063790253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301902637929295880170107341 113213489223485955063790253)
    ·
      refine ⟨42455058458807233148921345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113213489223485955063790253 42455058458807233148921345)
      ·
        refine ⟨31841293844105424861691009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42455058458807233148921345 31841293844105424861691009)
        ·
          refine ⟨23880970383079068646268257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31841293844105424861691009 23880970383079068646268257)
          ·
            refine ⟨17910727787309301484701193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23880970383079068646268257 17910727787309301484701193)
            ·
              refine ⟨13433045840481976113525895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17910727787309301484701193 13433045840481976113525895)
              ·
                refine ⟨20149568760722964170288843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13433045840481976113525895 20149568760722964170288843)
                ·
                  refine ⟨30224353141084446255433265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20149568760722964170288843 30224353141084446255433265)
                  ·
                    refine ⟨22668264855813334691574949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30224353141084446255433265 22668264855813334691574949)
                    ·
                      refine ⟨4250299660465000254670303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22668264855813334691574949 4250299660465000254670303)
                      ·
                        rfl

theorem cell23_8277429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_8277429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277429 prefixEnd_8277429 := by exact prefixLift 8277429
  have htrace : WordTrace (prefixWord ++ tailWord_8277429) baseStart_8277429 baseEnd_8277429 := by
    simpa [prefixWord, tailWord_8277429, baseEnd_8277429] using wordTrace_append hprefix tailTrace_8277429
  have hstable : (prefixWord ++ tailWord_8277429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277429).length < 2 ^ (prefixWord ++ tailWord_8277429).sum := by decide
  have hdescent : baseEnd_8277429 < baseStart_8277429 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277432 : List Nat := [2, 1, 2, 1, 2, 2, 3, 3, 1, 3, 3]
def baseStart_8277432 : Nat := 118140960795 + 8277432 * 2 ^ 59
def prefixEnd_8277432 : Nat := 4983230072969 + 3 ^ 40 * 8277432 * 2
def baseEnd_8277432 : Nat := 4250301200906963742932789

theorem tailTrace_8277432 : CollatzResearch.WordTrace tailWord_8277432 prefixEnd_8277432 4250301200906963742932789 := by
  unfold tailWord_8277432
  simp only [CollatzResearch.WordTrace]
  refine ⟨150951373674142505841233275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201268498232190007788311033 150951373674142505841233275)
  ·
    refine ⟨226427060511213758761849913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150951373674142505841233275 226427060511213758761849913)
    ·
      refine ⟨169820295383410319071387435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226427060511213758761849913 169820295383410319071387435)
      ·
        refine ⟨254730443075115478607081153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169820295383410319071387435 254730443075115478607081153)
        ·
          refine ⟨191047832306336608955310865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254730443075115478607081153 191047832306336608955310865)
          ·
            refine ⟨143285874229752456716483149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191047832306336608955310865 143285874229752456716483149)
            ·
              refine ⟨53732202836157171268681181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143285874229752456716483149 53732202836157171268681181)
              ·
                refine ⟨20149576063558939225755443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53732202836157171268681181 20149576063558939225755443)
                ·
                  refine ⟨30224364095338408838633165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20149576063558939225755443 30224364095338408838633165)
                  ·
                    refine ⟨11334136535751903314487437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30224364095338408838633165 11334136535751903314487437)
                    ·
                      refine ⟨4250301200906963742932789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11334136535751903314487437 4250301200906963742932789)
                      ·
                        rfl

theorem cell23_8277432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 1, 3, 3].length) (baseStart_8277432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277432 prefixEnd_8277432 := by exact prefixLift 8277432
  have htrace : WordTrace (prefixWord ++ tailWord_8277432) baseStart_8277432 baseEnd_8277432 := by
    simpa [prefixWord, tailWord_8277432, baseEnd_8277432] using wordTrace_append hprefix tailTrace_8277432
  have hstable : (prefixWord ++ tailWord_8277432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277432).length < 2 ^ (prefixWord ++ tailWord_8277432).sum := by decide
  have hdescent : baseEnd_8277432 < baseStart_8277432 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277466 : List Nat := [3, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3]
def baseStart_8277466 : Nat := 118140960795 + 8277466 * 2 ^ 59
def prefixEnd_8277466 : Nat := 4983230072969 + 3 ^ 40 * 8277466 * 2
def baseEnd_8277466 : Nat := 4250318659249216609907633

theorem tailTrace_8277466 : CollatzResearch.WordTrace tailWord_8277466 prefixEnd_8277466 4250318659249216609907633 := by
  unfold tailWord_8277466
  simp only [CollatzResearch.WordTrace]
  refine ⟨75475996857540458872301063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201269324953441223659469501 75475996857540458872301063)
  ·
    refine ⟨113213995286310688308451595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75475996857540458872301063 113213995286310688308451595)
    ·
      refine ⟨169820992929466032462677393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113213995286310688308451595 169820992929466032462677393)
      ·
        refine ⟨127365744697099524347008045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169820992929466032462677393 127365744697099524347008045)
        ·
          refine ⟨47762154261412321630128017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127365744697099524347008045 47762154261412321630128017)
          ·
            refine ⟨35821615696059241222596013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47762154261412321630128017 35821615696059241222596013)
            ·
              refine ⟨13433105886022215458473505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35821615696059241222596013 13433105886022215458473505)
              ·
                refine ⟨10074829414516661593855129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13433105886022215458473505 10074829414516661593855129)
                ·
                  refine ⟨7556122060887496195391347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10074829414516661593855129 7556122060887496195391347)
                  ·
                    refine ⟨11334183091331244293087021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7556122060887496195391347 11334183091331244293087021)
                    ·
                      refine ⟨4250318659249216609907633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11334183091331244293087021 4250318659249216609907633)
                      ·
                        rfl

theorem cell23_8277466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_8277466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277466 prefixEnd_8277466 := by exact prefixLift 8277466
  have htrace : WordTrace (prefixWord ++ tailWord_8277466) baseStart_8277466 baseEnd_8277466 := by
    simpa [prefixWord, tailWord_8277466, baseEnd_8277466] using wordTrace_append hprefix tailTrace_8277466
  have hstable : (prefixWord ++ tailWord_8277466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277466).length < 2 ^ (prefixWord ++ tailWord_8277466).sum := by decide
  have hdescent : baseEnd_8277466 < baseStart_8277466 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277493 : List Nat := [1, 3, 5, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_8277493 : Nat := 118140960795 + 8277493 * 2 ^ 59
def prefixEnd_8277493 : Nat := 4983230072969 + 3 ^ 40 * 8277493 * 2
def baseEnd_8277493 : Nat := 4250332523226888004270009

theorem tailTrace_8277493 : CollatzResearch.WordTrace tailWord_8277493 prefixEnd_8277493 4250332523226888004270009 := by
  unfold tailWord_8277493
  simp only [CollatzResearch.WordTrace]
  refine ⟨301904972201064019100437133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201269981467376012733624755 301904972201064019100437133)
  ·
    refine ⟨113214364575399007162663925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301904972201064019100437133 113214364575399007162663925)
    ·
      refine ⟨10613846678943656921499743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113214364575399007162663925 10613846678943656921499743)
      ·
        refine ⟨15920770018415485382249615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10613846678943656921499743 15920770018415485382249615)
        ·
          refine ⟨23881155027623228073374423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15920770018415485382249615 23881155027623228073374423)
          ·
            refine ⟨35821732541434842110061635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23881155027623228073374423 35821732541434842110061635)
            ·
              refine ⟨53732598812152263165092453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35821732541434842110061635 53732598812152263165092453)
              ·
                refine ⟨10074862277278549343454835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53732598812152263165092453 10074862277278549343454835)
                ·
                  refine ⟨15112293415917824015182253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10074862277278549343454835 15112293415917824015182253)
                  ·
                    refine ⟨5667110030969184005693345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15112293415917824015182253 5667110030969184005693345)
                    ·
                      refine ⟨4250332523226888004270009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5667110030969184005693345 4250332523226888004270009)
                      ·
                        rfl

theorem cell23_8277493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_8277493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277493 prefixEnd_8277493 := by exact prefixLift 8277493
  have htrace : WordTrace (prefixWord ++ tailWord_8277493) baseStart_8277493 baseEnd_8277493 := by
    simpa [prefixWord, tailWord_8277493, baseEnd_8277493] using wordTrace_append hprefix tailTrace_8277493
  have hstable : (prefixWord ++ tailWord_8277493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277493).length < 2 ^ (prefixWord ++ tailWord_8277493).sum := by decide
  have hdescent : baseEnd_8277493 < baseStart_8277493 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277495 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 9]
def baseStart_8277495 : Nat := 118140960795 + 8277495 * 2 ^ 59
def prefixEnd_8277495 : Nat := 4983230072969 + 3 ^ 40 * 8277495 * 2
def baseEnd_8277495 : Nat := 472259283354244110716111

theorem tailTrace_8277495 : CollatzResearch.WordTrace tailWord_8277495 prefixEnd_8277495 472259283354244110716111 := by
  unfold tailWord_8277495
  simp only [CollatzResearch.WordTrace]
  refine ⟨301905045147056773442009939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201270030098037848961339959 301905045147056773442009939)
  ·
    refine ⟨452857567720585160163014909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301905045147056773442009939 452857567720585160163014909)
    ·
      refine ⟨169821587895219435061130591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452857567720585160163014909 169821587895219435061130591)
      ·
        refine ⟨254732381842829152591695887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169821587895219435061130591 254732381842829152591695887)
        ·
          refine ⟨382098572764243728887543831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254732381842829152591695887 382098572764243728887543831)
          ·
            refine ⟨573147859146365593331315747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382098572764243728887543831 573147859146365593331315747)
            ·
              refine ⟨859721788719548389996973621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573147859146365593331315747 859721788719548389996973621)
              ·
                refine ⟨80598917692457661562216277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 859721788719548389996973621 80598917692457661562216277)
                ·
                  refine ⟨472259283354244110716111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80598917692457661562216277 472259283354244110716111)
                  ·
                    rfl

theorem cell23_8277495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 9].length) (baseStart_8277495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277495 prefixEnd_8277495 := by exact prefixLift 8277495
  have htrace : WordTrace (prefixWord ++ tailWord_8277495) baseStart_8277495 baseEnd_8277495 := by
    simpa [prefixWord, tailWord_8277495, baseEnd_8277495] using wordTrace_append hprefix tailTrace_8277495
  have hstable : (prefixWord ++ tailWord_8277495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277495).length < 2 ^ (prefixWord ++ tailWord_8277495).sum := by decide
  have hdescent : baseEnd_8277495 < baseStart_8277495 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277559 : List Nat := [1, 1, 3, 1, 2, 5, 2, 1, 2, 5]
def baseStart_8277559 : Nat := 118140960795 + 8277559 * 2 ^ 59
def prefixEnd_8277559 : Nat := 4983230072969 + 3 ^ 40 * 8277559 * 2
def baseEnd_8277559 : Nat := 1416788804316694915348235

theorem tailTrace_8277559 : CollatzResearch.WordTrace tailWord_8277559 prefixEnd_8277559 1416788804316694915348235 := by
  unfold tailWord_8277559
  simp only [CollatzResearch.WordTrace]
  refine ⟨301907379418824912372339731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201271586279216608248226487 301907379418824912372339731)
  ·
    refine ⟨452861069128237368558509597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301907379418824912372339731 452861069128237368558509597)
    ·
      refine ⟨169822900923089013209441099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452861069128237368558509597 169822900923089013209441099)
      ·
        refine ⟨254734351384633519814161649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169822900923089013209441099 254734351384633519814161649)
        ·
          refine ⟨191050763538475139860621237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254734351384633519814161649 191050763538475139860621237)
          ·
            refine ⟨17911009081732044361933241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 191050763538475139860621237 17911009081732044361933241)
            ·
              refine ⟨13433256811299033271449931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17911009081732044361933241 13433256811299033271449931)
              ·
                refine ⟨20149885216948549907174897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13433256811299033271449931 20149885216948549907174897)
                ·
                  refine ⟨15112413912711412430381173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20149885216948549907174897 15112413912711412430381173)
                  ·
                    refine ⟨1416788804316694915348235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15112413912711412430381173 1416788804316694915348235)
                    ·
                      rfl

theorem cell23_8277559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 5].length) (baseStart_8277559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277559 prefixEnd_8277559 := by exact prefixLift 8277559
  have htrace : WordTrace (prefixWord ++ tailWord_8277559) baseStart_8277559 baseEnd_8277559 := by
    simpa [prefixWord, tailWord_8277559, baseEnd_8277559] using wordTrace_append hprefix tailTrace_8277559
  have hstable : (prefixWord ++ tailWord_8277559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277559).length < 2 ^ (prefixWord ++ tailWord_8277559).sum := by decide
  have hdescent : baseEnd_8277559 < baseStart_8277559 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277579 : List Nat := [1, 1, 1, 1, 3, 1, 3, 4, 2, 4, 2]
def baseStart_8277579 : Nat := 118140960795 + 8277579 * 2 ^ 59
def prefixEnd_8277579 : Nat := 4983230072969 + 3 ^ 40 * 8277579 * 2
def baseEnd_8277579 : Nat := 4250376682563174667794613

theorem tailTrace_8277579 : CollatzResearch.WordTrace tailWord_8277579 prefixEnd_8277579 4250376682563174667794613 := by
  unfold tailWord_8277579
  simp only [CollatzResearch.WordTrace]
  refine ⟨301908108878752455788067791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201272072585834970525378527 301908108878752455788067791)
  ·
    refine ⟨452862163318128683682101687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301908108878752455788067791 452862163318128683682101687)
    ·
      refine ⟨679293244977193025523152531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452862163318128683682101687 679293244977193025523152531)
      ·
        refine ⟨1018939867465789538284728797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679293244977193025523152531 1018939867465789538284728797)
        ·
          refine ⟨382102450299671076856773299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1018939867465789538284728797 382102450299671076856773299)
          ·
            refine ⟨573153675449506615285159949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382102450299671076856773299 573153675449506615285159949)
            ·
              refine ⟨214932628293564980731934981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 573153675449506615285159949 214932628293564980731934981)
              ·
                refine ⟨40299867805043433887237809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214932628293564980731934981 40299867805043433887237809)
                ·
                  refine ⟨30224900853782575415428357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40299867805043433887237809 30224900853782575415428357)
                  ·
                    refine ⟨5667168910084232890392817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30224900853782575415428357 5667168910084232890392817)
                    ·
                      refine ⟨4250376682563174667794613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5667168910084232890392817 4250376682563174667794613)
                      ·
                        rfl

theorem cell23_8277579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 4, 2].length) (baseStart_8277579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277579 prefixEnd_8277579 := by exact prefixLift 8277579
  have htrace : WordTrace (prefixWord ++ tailWord_8277579) baseStart_8277579 baseEnd_8277579 := by
    simpa [prefixWord, tailWord_8277579, baseEnd_8277579] using wordTrace_append hprefix tailTrace_8277579
  have hstable : (prefixWord ++ tailWord_8277579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277579).length < 2 ^ (prefixWord ++ tailWord_8277579).sum := by decide
  have hdescent : baseEnd_8277579 < baseStart_8277579 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277582 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5]
def baseStart_8277582 : Nat := 118140960795 + 8277582 * 2 ^ 59
def prefixEnd_8277582 : Nat := 4983230072969 + 3 ^ 40 * 8277582 * 2
def baseEnd_8277582 : Nat := 4250378223005138156057099

theorem tailTrace_8277582 : CollatzResearch.WordTrace tailWord_8277582 prefixEnd_8277582 4250378223005138156057099 := by
  unfold tailWord_8277582
  simp only [CollatzResearch.WordTrace]
  refine ⟨37738527287217698412553375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201272145531827724866951333 37738527287217698412553375)
  ·
    refine ⟨56607790930826547618830063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37738527287217698412553375 56607790930826547618830063)
    ·
      refine ⟨84911686396239821428245095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56607790930826547618830063 84911686396239821428245095)
      ·
        refine ⟨127367529594359732142367643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84911686396239821428245095 127367529594359732142367643)
        ·
          refine ⟨191051294391539598213551465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127367529594359732142367643 191051294391539598213551465)
          ·
            refine ⟨143288470793654698660163599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191051294391539598213551465 143288470793654698660163599)
            ·
              refine ⟨214932706190482047990245399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143288470793654698660163599 214932706190482047990245399)
              ·
                refine ⟨322399059285723071985368099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214932706190482047990245399 322399059285723071985368099)
                ·
                  refine ⟨483598588928584607978052149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322399059285723071985368099 483598588928584607978052149)
                  ·
                    refine ⟨45337367712054806997942389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 483598588928584607978052149 45337367712054806997942389)
                    ·
                      refine ⟨4250378223005138156057099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45337367712054806997942389 4250378223005138156057099)
                      ·
                        rfl

theorem cell23_8277582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_8277582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277582 prefixEnd_8277582 := by exact prefixLift 8277582
  have htrace : WordTrace (prefixWord ++ tailWord_8277582) baseStart_8277582 baseEnd_8277582 := by
    simpa [prefixWord, tailWord_8277582, baseEnd_8277582] using wordTrace_append hprefix tailTrace_8277582
  have hstable : (prefixWord ++ tailWord_8277582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277582).length < 2 ^ (prefixWord ++ tailWord_8277582).sum := by decide
  have hdescent : baseEnd_8277582 < baseStart_8277582 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277589 : List Nat := [1, 3, 2, 2, 1, 1, 1, 5, 3, 4]
def baseStart_8277589 : Nat := 118140960795 + 8277589 * 2 ^ 59
def prefixEnd_8277589 : Nat := 4983230072969 + 3 ^ 40 * 8277589 * 2
def baseEnd_8277589 : Nat := 1416793939123239876223189

theorem tailTrace_8277589 : CollatzResearch.WordTrace tailWord_8277589 prefixEnd_8277589 1416793939123239876223189 := by
  unfold tailWord_8277589
  simp only [CollatzResearch.WordTrace]
  refine ⟨301908473608716227495931821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201272315739144151663954547 301908473608716227495931821)
  ·
    refine ⟨113215677603268585310974433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301908473608716227495931821 113215677603268585310974433)
    ·
      refine ⟨84911758202451438983230825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113215677603268585310974433 84911758202451438983230825)
      ·
        refine ⟨63683818651838579237423119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84911758202451438983230825 63683818651838579237423119)
        ·
          refine ⟨95525727977757868856134679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63683818651838579237423119 95525727977757868856134679)
          ·
            refine ⟨143288591966636803284202019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95525727977757868856134679 143288591966636803284202019)
            ·
              refine ⟨214932887949955204926303029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143288591966636803284202019 214932887949955204926303029)
              ·
                refine ⟨20149958245308300461840909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 214932887949955204926303029 20149958245308300461840909)
                ·
                  refine ⟨7556234341990612673190341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20149958245308300461840909 7556234341990612673190341)
                  ·
                    refine ⟨1416793939123239876223189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7556234341990612673190341 1416793939123239876223189)
                    ·
                      rfl

theorem cell23_8277589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_8277589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277589 prefixEnd_8277589 := by exact prefixLift 8277589
  have htrace : WordTrace (prefixWord ++ tailWord_8277589) baseStart_8277589 baseEnd_8277589 := by
    simpa [prefixWord, tailWord_8277589, baseEnd_8277589] using wordTrace_append hprefix tailTrace_8277589
  have hstable : (prefixWord ++ tailWord_8277589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277589).length < 2 ^ (prefixWord ++ tailWord_8277589).sum := by decide
  have hdescent : baseEnd_8277589 < baseStart_8277589 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277590 : List Nat := [5, 2, 2, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_8277590 : Nat := 118140960795 + 8277590 * 2 ^ 59
def prefixEnd_8277590 : Nat := 4983230072969 + 3 ^ 40 * 8277590 * 2
def baseEnd_8277590 : Nat := 4250382330850374124757063

theorem tailTrace_8277590 : CollatzResearch.WordTrace tailWord_8277590 prefixEnd_8277590 4250382330850374124757063 := by
  unfold tailWord_8277590
  simp only [CollatzResearch.WordTrace]
  refine ⟨18869281880107037791669889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201272340054475069777812149 18869281880107037791669889)
  ·
    refine ⟨14151961410080278343752417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18869281880107037791669889 14151961410080278343752417)
    ·
      refine ⟨10613971057560208757814313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14151961410080278343752417 10613971057560208757814313)
      ·
        refine ⟨7960478293170156568360735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10613971057560208757814313 7960478293170156568360735)
        ·
          refine ⟨11940717439755234852541103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7960478293170156568360735 11940717439755234852541103)
          ·
            refine ⟨17911076159632852278811655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11940717439755234852541103 17911076159632852278811655)
            ·
              refine ⟨26866614239449278418217483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17911076159632852278811655 26866614239449278418217483)
              ·
                refine ⟨40299921359173917627326225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26866614239449278418217483 40299921359173917627326225)
                ·
                  refine ⟨30224941019380438220494669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40299921359173917627326225 30224941019380438220494669)
                  ·
                    refine ⟨11334352882267664332685501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30224941019380438220494669 11334352882267664332685501)
                    ·
                      refine ⟨4250382330850374124757063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11334352882267664332685501 4250382330850374124757063)
                      ·
                        rfl

theorem cell23_8277590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_8277590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277590 prefixEnd_8277590 := by exact prefixLift 8277590
  have htrace : WordTrace (prefixWord ++ tailWord_8277590) baseStart_8277590 baseEnd_8277590 := by
    simpa [prefixWord, tailWord_8277590, baseEnd_8277590] using wordTrace_append hprefix tailTrace_8277590
  have hstable : (prefixWord ++ tailWord_8277590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277590).length < 2 ^ (prefixWord ++ tailWord_8277590).sum := by decide
  have hdescent : baseEnd_8277590 < baseStart_8277590 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277592 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 2, 4, 4]
def baseStart_8277592 : Nat := 118140960795 + 8277592 * 2 ^ 59
def prefixEnd_8277592 : Nat := 4983230072969 + 3 ^ 40 * 8277592 * 2
def baseEnd_8277592 : Nat := 4250383357811683116932053

theorem tailTrace_8277592 : CollatzResearch.WordTrace tailWord_8277592 prefixEnd_8277592 4250383357811683116932053 := by
  unfold tailWord_8277592
  simp only [CollatzResearch.WordTrace]
  refine ⟨150954291513852679504145515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201272388685136906005527353 150954291513852679504145515)
  ·
    refine ⟨226431437270779019256218273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150954291513852679504145515 226431437270779019256218273)
    ·
      refine ⟨169823577953084264442163705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226431437270779019256218273 169823577953084264442163705)
      ·
        refine ⟨127367683464813198331622779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169823577953084264442163705 127367683464813198331622779)
        ·
          refine ⟨191051525197219797497434169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127367683464813198331622779 191051525197219797497434169)
          ·
            refine ⟨143288643897914848123075627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191051525197219797497434169 143288643897914848123075627)
            ·
              refine ⟨214932965846872272184613441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143288643897914848123075627 214932965846872272184613441)
              ·
                refine ⟨161199724385154204138460081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214932965846872272184613441 161199724385154204138460081)
                ·
                  refine ⟨120899793288865653103845061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161199724385154204138460081 120899793288865653103845061)
                  ·
                    refine ⟨22668711241662309956970949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120899793288865653103845061 22668711241662309956970949)
                    ·
                      refine ⟨4250383357811683116932053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22668711241662309956970949 4250383357811683116932053)
                      ·
                        rfl

theorem cell23_8277592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_8277592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277592 prefixEnd_8277592 := by exact prefixLift 8277592
  have htrace : WordTrace (prefixWord ++ tailWord_8277592) baseStart_8277592 baseEnd_8277592 := by
    simpa [prefixWord, tailWord_8277592, baseEnd_8277592] using wordTrace_append hprefix tailTrace_8277592
  have hstable : (prefixWord ++ tailWord_8277592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277592).length < 2 ^ (prefixWord ++ tailWord_8277592).sum := by decide
  have hdescent : baseEnd_8277592 < baseStart_8277592 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277596 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 1, 6, 2]
def baseStart_8277596 : Nat := 118140960795 + 8277596 * 2 ^ 59
def prefixEnd_8277596 : Nat := 4983230072969 + 3 ^ 40 * 8277596 * 2
def baseEnd_8277596 : Nat := 4250385411734301101282035

theorem tailTrace_8277596 : CollatzResearch.WordTrace tailWord_8277596 prefixEnd_8277596 4250385411734301101282035 := by
  unfold tailWord_8277596
  simp only [CollatzResearch.WordTrace]
  refine ⟨150954364459845433845718321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201272485946460578460957761 150954364459845433845718321)
  ·
    refine ⟨113215773344884075384288741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150954364459845433845718321 113215773344884075384288741)
    ·
      refine ⟨21227957502165764134554139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113215773344884075384288741 21227957502165764134554139)
      ·
        refine ⟨31841936253248646201831209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21227957502165764134554139 31841936253248646201831209)
        ·
          refine ⟨23881452189936484651373407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31841936253248646201831209 23881452189936484651373407)
          ·
            refine ⟨35822178284904726977060111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23881452189936484651373407 35822178284904726977060111)
            ·
              refine ⟨53733267427357090465590167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35822178284904726977060111 53733267427357090465590167)
              ·
                refine ⟨80599901141035635698385251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53733267427357090465590167 80599901141035635698385251)
                ·
                  refine ⟨120899851711553453547577877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80599901141035635698385251 120899851711553453547577877)
                  ·
                    refine ⟨5667180548979068135042713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 120899851711553453547577877 5667180548979068135042713)
                    ·
                      refine ⟨4250385411734301101282035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5667180548979068135042713 4250385411734301101282035)
                      ·
                        rfl

theorem cell23_8277596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_8277596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277596 prefixEnd_8277596 := by exact prefixLift 8277596
  have htrace : WordTrace (prefixWord ++ tailWord_8277596) baseStart_8277596 baseEnd_8277596 := by
    simpa [prefixWord, tailWord_8277596, baseEnd_8277596] using wordTrace_append hprefix tailTrace_8277596
  have hstable : (prefixWord ++ tailWord_8277596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277596).length < 2 ^ (prefixWord ++ tailWord_8277596).sum := by decide
  have hdescent : baseEnd_8277596 < baseStart_8277596 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277613 : List Nat := [1, 5, 1, 1, 4, 2, 1, 1, 2, 1, 4]
def baseStart_8277613 : Nat := 118140960795 + 8277613 * 2 ^ 59
def prefixEnd_8277613 : Nat := 4983230072969 + 3 ^ 40 * 8277613 * 2
def baseEnd_8277613 : Nat := 4250394140905427534769457

theorem tailTrace_8277613 : CollatzResearch.WordTrace tailWord_8277613 prefixEnd_8277613 4250394140905427534769457 := by
  unfold tailWord_8277613
  simp only [CollatzResearch.WordTrace]
  refine ⟨301909348960629279594805493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201272899307086186396536995 301909348960629279594805493)
  ·
    refine ⟨28304001465058994962013015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 301909348960629279594805493 28304001465058994962013015)
    ·
      refine ⟨42456002197588492443019523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28304001465058994962013015 42456002197588492443019523)
      ·
        refine ⟨63684003296382738664529285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42456002197588492443019523 63684003296382738664529285)
        ·
          refine ⟨11940750618071763499599241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63684003296382738664529285 11940750618071763499599241)
          ·
            refine ⟨8955562963553822624699431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11940750618071763499599241 8955562963553822624699431)
            ·
              refine ⟨13433344445330733937049147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8955562963553822624699431 13433344445330733937049147)
              ·
                refine ⟨20150016667996100905573721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13433344445330733937049147 20150016667996100905573721)
                ·
                  refine ⟨15112512500997075679180291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20150016667996100905573721 15112512500997075679180291)
                  ·
                    refine ⟨22668768751495613518770437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15112512500997075679180291 22668768751495613518770437)
                    ·
                      refine ⟨4250394140905427534769457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22668768751495613518770437 4250394140905427534769457)
                      ·
                        rfl

theorem cell23_8277613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_8277613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277613 prefixEnd_8277613 := by exact prefixLift 8277613
  have htrace : WordTrace (prefixWord ++ tailWord_8277613) baseStart_8277613 baseEnd_8277613 := by
    simpa [prefixWord, tailWord_8277613, baseEnd_8277613] using wordTrace_append hprefix tailTrace_8277613
  have hstable : (prefixWord ++ tailWord_8277613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277613).length < 2 ^ (prefixWord ++ tailWord_8277613).sum := by decide
  have hdescent : baseEnd_8277613 < baseStart_8277613 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277616 : List Nat := [2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 3]
def baseStart_8277616 : Nat := 118140960795 + 8277616 * 2 ^ 59
def prefixEnd_8277616 : Nat := 4983230072969 + 3 ^ 40 * 8277616 * 2
def baseEnd_8277616 : Nat := 4250395681347391023031943

theorem tailTrace_8277616 : CollatzResearch.WordTrace tailWord_8277616 prefixEnd_8277616 4250395681347391023031943 := by
  unfold tailWord_8277616
  simp only [CollatzResearch.WordTrace]
  refine ⟨150954729189809205553582351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201272972253078940738109801 150954729189809205553582351)
  ·
    refine ⟨226432093784713808330373527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150954729189809205553582351 226432093784713808330373527)
    ·
      refine ⟨339648140677070712495560291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226432093784713808330373527 339648140677070712495560291)
      ·
        refine ⟨509472211015606068743340437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339648140677070712495560291 509472211015606068743340437)
        ·
          refine ⟨23881509891356534472344083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 509472211015606068743340437 23881509891356534472344083)
          ·
            refine ⟨35822264837034801708516125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23881509891356534472344083 35822264837034801708516125)
            ·
              refine ⟨13433349313888050640693547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35822264837034801708516125 13433349313888050640693547)
              ·
                refine ⟨20150023970832075961040321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13433349313888050640693547 20150023970832075961040321)
                ·
                  refine ⟨15112517978124056970780241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20150023970832075961040321 15112517978124056970780241)
                  ·
                    refine ⟨11334388483593042728085181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15112517978124056970780241 11334388483593042728085181)
                    ·
                      refine ⟨4250395681347391023031943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11334388483593042728085181 4250395681347391023031943)
                      ·
                        rfl

theorem cell23_8277616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 3].length) (baseStart_8277616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277616 prefixEnd_8277616 := by exact prefixLift 8277616
  have htrace : WordTrace (prefixWord ++ tailWord_8277616) baseStart_8277616 baseEnd_8277616 := by
    simpa [prefixWord, tailWord_8277616, baseEnd_8277616] using wordTrace_append hprefix tailTrace_8277616
  have hstable : (prefixWord ++ tailWord_8277616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277616).length < 2 ^ (prefixWord ++ tailWord_8277616).sum := by decide
  have hdescent : baseEnd_8277616 < baseStart_8277616 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277656 : List Nat := [2, 1, 2, 4, 1, 2, 1, 2, 1, 5, 2]
def baseStart_8277656 : Nat := 118140960795 + 8277656 * 2 ^ 59
def prefixEnd_8277656 : Nat := 4983230072969 + 3 ^ 40 * 8277656 * 2
def baseEnd_8277656 : Nat := 4250416220573570866531759

theorem tailTrace_8277656 : CollatzResearch.WordTrace tailWord_8277656 prefixEnd_8277656 4250416220573570866531759 := by
  unfold tailWord_8277656
  simp only [CollatzResearch.WordTrace]
  refine ⟨150955458649736748969310411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201273944866315665292413881 150955458649736748969310411)
  ·
    refine ⟨226433187974605123453965617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150955458649736748969310411 226433187974605123453965617)
    ·
      refine ⟨169824890980953842590474213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226433187974605123453965617 169824890980953842590474213)
      ·
        refine ⟨31842167058928845485713915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169824890980953842590474213 31842167058928845485713915)
        ·
          refine ⟨47763250588393268228570873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31842167058928845485713915 47763250588393268228570873)
          ·
            refine ⟨35822437941294951171428155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47763250588393268228570873 35822437941294951171428155)
            ·
              refine ⟨53733656911942426757142233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35822437941294951171428155 53733656911942426757142233)
              ·
                refine ⟨40300242683956820067856675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53733656911942426757142233 40300242683956820067856675)
                ·
                  refine ⟨60450364025935230101785013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40300242683956820067856675 60450364025935230101785013)
                  ·
                    refine ⟨5667221627431427822042345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60450364025935230101785013 5667221627431427822042345)
                    ·
                      refine ⟨4250416220573570866531759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5667221627431427822042345 4250416220573570866531759)
                      ·
                        rfl

theorem cell23_8277656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_8277656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277656 prefixEnd_8277656 := by exact prefixLift 8277656
  have htrace : WordTrace (prefixWord ++ tailWord_8277656) baseStart_8277656 baseEnd_8277656 := by
    simpa [prefixWord, tailWord_8277656, baseEnd_8277656] using wordTrace_append hprefix tailTrace_8277656
  have hstable : (prefixWord ++ tailWord_8277656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277656).length < 2 ^ (prefixWord ++ tailWord_8277656).sum := by decide
  have hdescent : baseEnd_8277656 < baseStart_8277656 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277669 : List Nat := [1, 3, 1, 2, 1, 2, 2, 3, 3, 1, 4]
def baseStart_8277669 : Nat := 118140960795 + 8277669 * 2 ^ 59
def prefixEnd_8277669 : Nat := 4983230072969 + 3 ^ 40 * 8277669 * 2
def baseEnd_8277669 : Nat := 4250422895822079315669199

theorem tailTrace_8277669 : CollatzResearch.WordTrace tailWord_8277669 prefixEnd_8277669 4250422895822079315669199 := by
  unfold tailWord_8277669
  simp only [CollatzResearch.WordTrace]
  refine ⟨301911391448426401158844061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201274260965617600772562707 301911391448426401158844061)
  ·
    refine ⟨113216771793159900434566523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301911391448426401158844061 113216771793159900434566523)
    ·
      refine ⟨169825157689739850651849785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113216771793159900434566523 169825157689739850651849785)
      ·
        refine ⟨127368868267304887988887339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169825157689739850651849785 127368868267304887988887339)
        ·
          refine ⟨191053302400957331983331009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127368868267304887988887339 191053302400957331983331009)
          ·
            refine ⟨143289976800717998987498257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191053302400957331983331009 143289976800717998987498257)
            ·
              refine ⟨107467482600538499240623693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143289976800717998987498257 107467482600538499240623693)
              ·
                refine ⟨40300305975201937215233885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107467482600538499240623693 40300305975201937215233885)
                ·
                  refine ⟨15112614740700726455712707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40300305975201937215233885 15112614740700726455712707)
                  ·
                    refine ⟨22668922111051089683569061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15112614740700726455712707 22668922111051089683569061)
                    ·
                      refine ⟨4250422895822079315669199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22668922111051089683569061 4250422895822079315669199)
                      ·
                        rfl

theorem cell23_8277669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_8277669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277669 prefixEnd_8277669 := by exact prefixLift 8277669
  have htrace : WordTrace (prefixWord ++ tailWord_8277669) baseStart_8277669 baseEnd_8277669 := by
    simpa [prefixWord, tailWord_8277669, baseEnd_8277669] using wordTrace_append hprefix tailTrace_8277669
  have hstable : (prefixWord ++ tailWord_8277669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277669).length < 2 ^ (prefixWord ++ tailWord_8277669).sum := by decide
  have hdescent : baseEnd_8277669 < baseStart_8277669 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277679 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 6, 4]
def baseStart_8277679 : Nat := 118140960795 + 8277679 * 2 ^ 59
def prefixEnd_8277679 : Nat := 4983230072969 + 3 ^ 40 * 8277679 * 2
def baseEnd_8277679 : Nat := 1416809343542874758848051

theorem tailTrace_8277679 : CollatzResearch.WordTrace tailWord_8277679 prefixEnd_8277679 1416809343542874758848051 := by
  unfold tailWord_8277679
  simp only [CollatzResearch.WordTrace]
  refine ⟨301911756178390172866708091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201274504118926781911138727 301911756178390172866708091)
  ·
    refine ⟨452867634267585259300062137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301911756178390172866708091 452867634267585259300062137)
    ·
      refine ⟨339650725700688944475046603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452867634267585259300062137 339650725700688944475046603)
      ·
        refine ⟨509476088551033416712569905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339650725700688944475046603 509476088551033416712569905)
        ·
          refine ⟨382107066413275062534427429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 509476088551033416712569905 382107066413275062534427429)
          ·
            refine ⟨71645074952489074225205143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 382107066413275062534427429 71645074952489074225205143)
            ·
              refine ⟨107467612428733611337807715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71645074952489074225205143 107467612428733611337807715)
              ·
                refine ⟨161201418643100417006711573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107467612428733611337807715 161201418643100417006711573)
                ·
                  refine ⟨7556316498895332047189605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 161201418643100417006711573 7556316498895332047189605)
                  ·
                    refine ⟨1416809343542874758848051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7556316498895332047189605 1416809343542874758848051)
                    ·
                      rfl

theorem cell23_8277679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6, 4].length) (baseStart_8277679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277679 prefixEnd_8277679 := by exact prefixLift 8277679
  have htrace : WordTrace (prefixWord ++ tailWord_8277679) baseStart_8277679 baseEnd_8277679 := by
    simpa [prefixWord, tailWord_8277679, baseEnd_8277679] using wordTrace_append hprefix tailTrace_8277679
  have hstable : (prefixWord ++ tailWord_8277679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277679).length < 2 ^ (prefixWord ++ tailWord_8277679).sum := by decide
  have hdescent : baseEnd_8277679 < baseStart_8277679 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277689 : List Nat := [1, 2, 1, 4, 1, 1, 3, 3, 1, 1, 5]
def baseStart_8277689 : Nat := 118140960795 + 8277689 * 2 ^ 59
def prefixEnd_8277689 : Nat := 4983230072969 + 3 ^ 40 * 8277689 * 2
def baseEnd_8277689 : Nat := 4250433165435169237419107

theorem tailTrace_8277689 : CollatzResearch.WordTrace tailWord_8277689 prefixEnd_8277689 4250433165435169237419107 := by
  unfold tailWord_8277689
  simp only [CollatzResearch.WordTrace]
  refine ⟨301912120908353944574572121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201274747272235963049714747 301912120908353944574572121)
  ·
    refine ⟨226434090681265458430929091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301912120908353944574572121 226434090681265458430929091)
    ·
      refine ⟨339651136021898187646393637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226434090681265458430929091 339651136021898187646393637)
      ·
        refine ⟨63684588004105910183698807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339651136021898187646393637 63684588004105910183698807)
        ·
          refine ⟨95526882006158865275548211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63684588004105910183698807 95526882006158865275548211)
          ·
            refine ⟨143290323009238297913322317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95526882006158865275548211 143290323009238297913322317)
            ·
              refine ⟨53733871128464361717495869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143290323009238297913322317 53733871128464361717495869)
              ·
                refine ⟨20150201673174135644060951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53733871128464361717495869 20150201673174135644060951)
                ·
                  refine ⟨30225302509761203466091427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20150201673174135644060951 30225302509761203466091427)
                  ·
                    refine ⟨45337953764641805199137141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30225302509761203466091427 45337953764641805199137141)
                    ·
                      refine ⟨4250433165435169237419107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45337953764641805199137141 4250433165435169237419107)
                      ·
                        rfl

theorem cell23_8277689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_8277689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277689 prefixEnd_8277689 := by exact prefixLift 8277689
  have htrace : WordTrace (prefixWord ++ tailWord_8277689) baseStart_8277689 baseEnd_8277689 := by
    simpa [prefixWord, tailWord_8277689, baseEnd_8277689] using wordTrace_append hprefix tailTrace_8277689
  have hstable : (prefixWord ++ tailWord_8277689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277689).length < 2 ^ (prefixWord ++ tailWord_8277689).sum := by decide
  have hdescent : baseEnd_8277689 < baseStart_8277689 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277696 : List Nat := [2, 1, 1, 2, 4, 1, 2, 4, 2, 4]
def baseStart_8277696 : Nat := 118140960795 + 8277696 * 2 ^ 59
def prefixEnd_8277696 : Nat := 4983230072969 + 3 ^ 40 * 8277696 * 2
def baseEnd_8277696 : Nat := 1416812253266583570010525

theorem tailTrace_8277696 : CollatzResearch.WordTrace tailWord_8277696 prefixEnd_8277696 1416812253266583570010525 := by
  unfold tailWord_8277696
  simp only [CollatzResearch.WordTrace]
  refine ⟨150956188109664292385038471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201274917479552389846717961 150956188109664292385038471)
  ·
    refine ⟨226434282164496438577557707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150956188109664292385038471 226434282164496438577557707)
    ·
      refine ⟨339651423246744657866336561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226434282164496438577557707 339651423246744657866336561)
      ·
        refine ⟨254738567435058493399752421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339651423246744657866336561 254738567435058493399752421)
        ·
          refine ⟨47763481394073467512453579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254738567435058493399752421 47763481394073467512453579)
          ·
            refine ⟨71645222091110201268680369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47763481394073467512453579 71645222091110201268680369)
            ·
              refine ⟨53733916568332650951510277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71645222091110201268680369 53733916568332650951510277)
              ·
                refine ⟨10075109356562372053408177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53733916568332650951510277 10075109356562372053408177)
                ·
                  refine ⟨7556332017421779040056133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10075109356562372053408177 7556332017421779040056133)
                  ·
                    refine ⟨1416812253266583570010525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7556332017421779040056133 1416812253266583570010525)
                    ·
                      rfl

theorem cell23_8277696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 2, 4].length) (baseStart_8277696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277696 prefixEnd_8277696 := by exact prefixLift 8277696
  have htrace : WordTrace (prefixWord ++ tailWord_8277696) baseStart_8277696 baseEnd_8277696 := by
    simpa [prefixWord, tailWord_8277696, baseEnd_8277696] using wordTrace_append hprefix tailTrace_8277696
  have hstable : (prefixWord ++ tailWord_8277696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277696).length < 2 ^ (prefixWord ++ tailWord_8277696).sum := by decide
  have hdescent : baseEnd_8277696 < baseStart_8277696 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277713 : List Nat := [1, 2, 2, 1, 2, 4, 4, 1, 2, 4]
def baseStart_8277713 : Nat := 118140960795 + 8277713 * 2 ^ 59
def prefixEnd_8277713 : Nat := 4983230072969 + 3 ^ 40 * 8277713 * 2
def baseEnd_8277713 : Nat := 1416815162990292381172999

theorem tailTrace_8277713 : CollatzResearch.WordTrace tailWord_8277713 prefixEnd_8277713 1416815162990292381172999 := by
  unfold tailWord_8277713
  simp only [CollatzResearch.WordTrace]
  refine ⟨301912996260266996673445793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201275330840177997782297195 301912996260266996673445793)
  ·
    refine ⟨226434747195200247505084345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301912996260266996673445793 226434747195200247505084345)
    ·
      refine ⟨169826060396400185628813259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226434747195200247505084345 169826060396400185628813259)
      ·
        refine ⟨254739090594600278443219889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169826060396400185628813259 254739090594600278443219889)
        ·
          refine ⟨191054317945950208832414917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254739090594600278443219889 191054317945950208832414917)
          ·
            refine ⟨35822684614865664156077797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191054317945950208832414917 35822684614865664156077797)
            ·
              refine ⟨6716753365287312029264587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35822684614865664156077797 6716753365287312029264587)
              ·
                refine ⟨10075130047930968043896881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6716753365287312029264587 10075130047930968043896881)
                ·
                  refine ⟨7556347535948226032922661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10075130047930968043896881 7556347535948226032922661)
                  ·
                    refine ⟨1416815162990292381172999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7556347535948226032922661 1416815162990292381172999)
                    ·
                      rfl

theorem cell23_8277713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 2, 4].length) (baseStart_8277713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277713 prefixEnd_8277713 := by exact prefixLift 8277713
  have htrace : WordTrace (prefixWord ++ tailWord_8277713) baseStart_8277713 baseEnd_8277713 := by
    simpa [prefixWord, tailWord_8277713, baseEnd_8277713] using wordTrace_append hprefix tailTrace_8277713
  have hstable : (prefixWord ++ tailWord_8277713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277713).length < 2 ^ (prefixWord ++ tailWord_8277713).sum := by decide
  have hdescent : baseEnd_8277713 < baseStart_8277713 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277716 : List Nat := [2, 4, 1, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_8277716 : Nat := 118140960795 + 8277716 * 2 ^ 59
def prefixEnd_8277716 : Nat := 4983230072969 + 3 ^ 40 * 8277716 * 2
def baseEnd_8277716 : Nat := 4250447029412840631781483

theorem tailTrace_8277716 : CollatzResearch.WordTrace tailWord_8277716 prefixEnd_8277716 4250447029412840631781483 := by
  unfold tailWord_8277716
  simp only [CollatzResearch.WordTrace]
  refine ⟨150956552839628064092902501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201275403786170752123870001 150956552839628064092902501)
  ·
    refine ⟨28304353657430262017419219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150956552839628064092902501 28304353657430262017419219)
    ·
      refine ⟨42456530486145393026128829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28304353657430262017419219 42456530486145393026128829)
      ·
        refine ⟨15921198932304522384798311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42456530486145393026128829 15921198932304522384798311)
        ·
          refine ⟨23881798398456783577197467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15921198932304522384798311 23881798398456783577197467)
          ·
            refine ⟨35822697597685175365796201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23881798398456783577197467 35822697597685175365796201)
            ·
              refine ⟨26867023198263881524347151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35822697597685175365796201 26867023198263881524347151)
              ·
                refine ⟨40300534797395822286520727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26867023198263881524347151 40300534797395822286520727)
                ·
                  refine ⟨60450802196093733429781091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40300534797395822286520727 60450802196093733429781091)
                  ·
                    refine ⟨90676203294140600144671637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60450802196093733429781091 90676203294140600144671637)
                    ·
                      refine ⟨4250447029412840631781483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90676203294140600144671637 4250447029412840631781483)
                      ·
                        rfl

theorem cell23_8277716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_8277716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277716 prefixEnd_8277716 := by exact prefixLift 8277716
  have htrace : WordTrace (prefixWord ++ tailWord_8277716) baseStart_8277716 baseEnd_8277716 := by
    simpa [prefixWord, tailWord_8277716, baseEnd_8277716] using wordTrace_append hprefix tailTrace_8277716
  have hstable : (prefixWord ++ tailWord_8277716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277716).length < 2 ^ (prefixWord ++ tailWord_8277716).sum := by decide
  have hdescent : baseEnd_8277716 < baseStart_8277716 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277736 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 3, 3, 3]
def baseStart_8277736 : Nat := 118140960795 + 8277736 * 2 ^ 59
def prefixEnd_8277736 : Nat := 4983230072969 + 3 ^ 40 * 8277736 * 2
def baseEnd_8277736 : Nat := 4250457299025930553531391

theorem tailTrace_8277736 : CollatzResearch.WordTrace tailWord_8277736 prefixEnd_8277736 4250457299025930553531391 := by
  unfold tailWord_8277736
  simp only [CollatzResearch.WordTrace]
  refine ⟨150956917569591835800766531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201275890092789114401022041 150956917569591835800766531)
  ·
    refine ⟨226435376354387753701149797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150956917569591835800766531 226435376354387753701149797)
    ·
      refine ⟨42456633066447703818965587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226435376354387753701149797 42456633066447703818965587)
      ·
        refine ⟨63684949599671555728448381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42456633066447703818965587 63684949599671555728448381)
        ·
          refine ⟨23881856099876833398168143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63684949599671555728448381 23881856099876833398168143)
          ·
            refine ⟨35822784149815250097252215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23881856099876833398168143 35822784149815250097252215)
            ·
              refine ⟨53734176224722875145878323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35822784149815250097252215 53734176224722875145878323)
              ·
                refine ⟨80601264337084312718817485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53734176224722875145878323 80601264337084312718817485)
                ·
                  refine ⟨30225474126406617269556557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80601264337084312718817485 30225474126406617269556557)
                  ·
                    refine ⟨11334552797402481476083709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30225474126406617269556557 11334552797402481476083709)
                    ·
                      refine ⟨4250457299025930553531391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11334552797402481476083709 4250457299025930553531391)
                      ·
                        rfl

theorem cell23_8277736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_8277736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277736 prefixEnd_8277736 := by exact prefixLift 8277736
  have htrace : WordTrace (prefixWord ++ tailWord_8277736) baseStart_8277736 baseEnd_8277736 := by
    simpa [prefixWord, tailWord_8277736, baseEnd_8277736] using wordTrace_append hprefix tailTrace_8277736
  have hstable : (prefixWord ++ tailWord_8277736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277736).length < 2 ^ (prefixWord ++ tailWord_8277736).sum := by decide
  have hdescent : baseEnd_8277736 < baseStart_8277736 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277759 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 4]
def baseStart_8277759 : Nat := 118140960795 + 8277759 * 2 ^ 59
def prefixEnd_8277759 : Nat := 4983230072969 + 3 ^ 40 * 8277759 * 2
def baseEnd_8277759 : Nat := 4250469109080983963543785

theorem tailTrace_8277759 : CollatzResearch.WordTrace tailWord_8277759 prefixEnd_8277759 4250469109080983963543785 := by
  unfold tailWord_8277759
  simp only [CollatzResearch.WordTrace]
  refine ⟨301914674018100346529620331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201276449345400231019746887 301914674018100346529620331)
  ·
    refine ⟨452872011027150519794430497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301914674018100346529620331 452872011027150519794430497)
    ·
      refine ⟨339654008270362889845822873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452872011027150519794430497 339654008270362889845822873)
      ·
        refine ⟨254740506202772167384367155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339654008270362889845822873 254740506202772167384367155)
        ·
          refine ⟨382110759304158251076550733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254740506202772167384367155 382110759304158251076550733)
          ·
            refine ⟨143291534739059344153706525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382110759304158251076550733 143291534739059344153706525)
            ·
              refine ⟨53734325527147254057639947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143291534739059344153706525 53734325527147254057639947)
              ·
                refine ⟨80601488290720881086459921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53734325527147254057639947 80601488290720881086459921)
                ·
                  refine ⟨60451116218040660814844941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80601488290720881086459921 60451116218040660814844941)
                  ·
                    refine ⟨22669168581765247805566853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60451116218040660814844941 22669168581765247805566853)
                    ·
                      refine ⟨4250469109080983963543785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22669168581765247805566853 4250469109080983963543785)
                      ·
                        rfl

theorem cell23_8277759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_8277759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277759 prefixEnd_8277759 := by exact prefixLift 8277759
  have htrace : WordTrace (prefixWord ++ tailWord_8277759) baseStart_8277759 baseEnd_8277759 := by
    simpa [prefixWord, tailWord_8277759, baseEnd_8277759] using wordTrace_append hprefix tailTrace_8277759
  have hstable : (prefixWord ++ tailWord_8277759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277759).length < 2 ^ (prefixWord ++ tailWord_8277759).sum := by decide
  have hdescent : baseEnd_8277759 < baseStart_8277759 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277779 : List Nat := [1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 5]
def baseStart_8277779 : Nat := 118140960795 + 8277779 * 2 ^ 59
def prefixEnd_8277779 : Nat := 4983230072969 + 3 ^ 40 * 8277779 * 2
def baseEnd_8277779 : Nat := 4250479378694073885293693

theorem tailTrace_8277779 : CollatzResearch.WordTrace tailWord_8277779 prefixEnd_8277779 4250479378694073885293693 := by
  unfold tailWord_8277779
  simp only [CollatzResearch.WordTrace]
  refine ⟨301915403478027889945348391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201276935652018593296898927 301915403478027889945348391)
  ·
    refine ⟨452873105217041834918022587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301915403478027889945348391 452873105217041834918022587)
    ·
      refine ⟨679309657825562752377033881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452873105217041834918022587 679309657825562752377033881)
      ·
        refine ⟨509482243369172064282775411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 679309657825562752377033881 509482243369172064282775411)
        ·
          refine ⟨764223365053758096424163117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509482243369172064282775411 764223365053758096424163117)
          ·
            refine ⟨286583761895159286159061169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 764223365053758096424163117 286583761895159286159061169)
            ·
              refine ⟨214937821421369464619295877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286583761895159286159061169 214937821421369464619295877)
              ·
                refine ⟨40300841516506774616117977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214937821421369464619295877 40300841516506774616117977)
                ·
                  refine ⟨30225631137380080962088483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40300841516506774616117977 30225631137380080962088483)
                  ·
                    refine ⟨45338446706070121443132725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30225631137380080962088483 45338446706070121443132725)
                    ·
                      refine ⟨4250479378694073885293693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45338446706070121443132725 4250479378694073885293693)
                      ·
                        rfl

theorem cell23_8277779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 5].length) (baseStart_8277779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277779 prefixEnd_8277779 := by exact prefixLift 8277779
  have htrace : WordTrace (prefixWord ++ tailWord_8277779) baseStart_8277779 baseEnd_8277779 := by
    simpa [prefixWord, tailWord_8277779, baseEnd_8277779] using wordTrace_append hprefix tailTrace_8277779
  have hstable : (prefixWord ++ tailWord_8277779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277779).length < 2 ^ (prefixWord ++ tailWord_8277779).sum := by decide
  have hdescent : baseEnd_8277779 < baseStart_8277779 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277793 : List Nat := [1, 2, 3, 2, 1, 3, 2, 2, 1, 4, 2]
def baseStart_8277793 : Nat := 118140960795 + 8277793 * 2 ^ 59
def prefixEnd_8277793 : Nat := 4983230072969 + 3 ^ 40 * 8277793 * 2
def baseEnd_8277793 : Nat := 4250486567423236830518629

theorem tailTrace_8277793 : CollatzResearch.WordTrace tailWord_8277793 prefixEnd_8277793 4250486567423236830518629 := by
  unfold tailWord_8277793
  simp only [CollatzResearch.WordTrace]
  refine ⟨301915914099977170336358033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201277276066651446890905355 301915914099977170336358033)
  ·
    refine ⟨226436935574982877752268525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301915914099977170336358033 226436935574982877752268525)
    ·
      refine ⟨84913850840618579157100697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226436935574982877752268525 84913850840618579157100697)
      ·
        refine ⟨63685388130463934367825523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84913850840618579157100697 63685388130463934367825523)
        ·
          refine ⟨95528082195695901551738285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63685388130463934367825523 95528082195695901551738285)
          ·
            refine ⟨35823030823385963081901857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95528082195695901551738285 35823030823385963081901857)
            ·
              refine ⟨26867273117539472311426393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35823030823385963081901857 26867273117539472311426393)
              ·
                refine ⟨20150454838154604233569795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26867273117539472311426393 20150454838154604233569795)
                ·
                  refine ⟨30225682257231906350354693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20150454838154604233569795 30225682257231906350354693)
                  ·
                    refine ⟨5667315423230982440691505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30225682257231906350354693 5667315423230982440691505)
                    ·
                      refine ⟨4250486567423236830518629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5667315423230982440691505 4250486567423236830518629)
                      ·
                        rfl

theorem cell23_8277793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_8277793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277793 prefixEnd_8277793 := by exact prefixLift 8277793
  have htrace : WordTrace (prefixWord ++ tailWord_8277793) baseStart_8277793 baseEnd_8277793 := by
    simpa [prefixWord, tailWord_8277793, baseEnd_8277793] using wordTrace_append hprefix tailTrace_8277793
  have hstable : (prefixWord ++ tailWord_8277793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277793).length < 2 ^ (prefixWord ++ tailWord_8277793).sum := by decide
  have hdescent : baseEnd_8277793 < baseStart_8277793 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277797 : List Nat := [1, 3, 1, 2, 3, 4, 2, 1, 1, 3, 2]
def baseStart_8277797 : Nat := 118140960795 + 8277797 * 2 ^ 59
def prefixEnd_8277797 : Nat := 4983230072969 + 3 ^ 40 * 8277797 * 2
def baseEnd_8277797 : Nat := 4250488621345854814868611

theorem tailTrace_8277797 : CollatzResearch.WordTrace tailWord_8277797 prefixEnd_8277797 4250488621345854814868611 := by
  unfold tailWord_8277797
  simp only [CollatzResearch.WordTrace]
  refine ⟨301916059991962679019503645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201277373327975119346335763 301916059991962679019503645)
  ·
    refine ⟨113218522496986004632313867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301916059991962679019503645 113218522496986004632313867)
    ·
      refine ⟨169827783745479006948470801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113218522496986004632313867 169827783745479006948470801)
      ·
        refine ⟨127370837809109255211353101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169827783745479006948470801 127370837809109255211353101)
        ·
          refine ⟨47764064178415970704257413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127370837809109255211353101 47764064178415970704257413)
          ·
            refine ⟨8955762033452994507048265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47764064178415970704257413 8955762033452994507048265)
            ·
              refine ⟨6716821525089745880286199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8955762033452994507048265 6716821525089745880286199)
              ·
                refine ⟨10075232287634618820429299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6716821525089745880286199 10075232287634618820429299)
                ·
                  refine ⟨15112848431451928230643949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10075232287634618820429299 15112848431451928230643949)
                  ·
                    refine ⟨5667318161794473086491481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15112848431451928230643949 5667318161794473086491481)
                    ·
                      refine ⟨4250488621345854814868611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5667318161794473086491481 4250488621345854814868611)
                      ·
                        rfl

theorem cell23_8277797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 1, 3, 2].length) (baseStart_8277797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277797 prefixEnd_8277797 := by exact prefixLift 8277797
  have htrace : WordTrace (prefixWord ++ tailWord_8277797) baseStart_8277797 baseEnd_8277797 := by
    simpa [prefixWord, tailWord_8277797, baseEnd_8277797] using wordTrace_append hprefix tailTrace_8277797
  have hstable : (prefixWord ++ tailWord_8277797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277797).length < 2 ^ (prefixWord ++ tailWord_8277797).sum := by decide
  have hdescent : baseEnd_8277797 < baseStart_8277797 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277810 : List Nat := [3, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2]
def baseStart_8277810 : Nat := 118140960795 + 8277810 * 2 ^ 59
def prefixEnd_8277810 : Nat := 4983230072969 + 3 ^ 40 * 8277810 * 2
def baseEnd_8277810 : Nat := 4250495296594363264006051

theorem tailTrace_8277810 : CollatzResearch.WordTrace tailWord_8277810 prefixEnd_8277810 4250495296594363264006051 := by
  unfold tailWord_8277810
  simp only [CollatzResearch.WordTrace]
  refine ⟨75479133535228895559931721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201277689427277054826484589 75479133535228895559931721)
  ·
    refine ⟨56609350151421671669948791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75479133535228895559931721 56609350151421671669948791)
    ·
      refine ⟨84914025227132507504923187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56609350151421671669948791 84914025227132507504923187)
      ·
        refine ⟨127371037840698761257384781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84914025227132507504923187 127371037840698761257384781)
        ·
          refine ⟨47764139190262035471519293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127371037840698761257384781 47764139190262035471519293)
          ·
            refine ⟨17911552196348263301819735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47764139190262035471519293 17911552196348263301819735)
            ·
              refine ⟨26867328294522394952729603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17911552196348263301819735 26867328294522394952729603)
              ·
                refine ⟨40300992441783592429094405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26867328294522394952729603 40300992441783592429094405)
                ·
                  refine ⟨7556436082834423580455201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40300992441783592429094405 7556436082834423580455201)
                  ·
                    refine ⟨5667327062125817685341401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7556436082834423580455201 5667327062125817685341401)
                    ·
                      refine ⟨4250495296594363264006051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5667327062125817685341401 4250495296594363264006051)
                      ·
                        rfl

theorem cell23_8277810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2].length) (baseStart_8277810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277810 prefixEnd_8277810 := by exact prefixLift 8277810
  have htrace : WordTrace (prefixWord ++ tailWord_8277810) baseStart_8277810 baseEnd_8277810 := by
    simpa [prefixWord, tailWord_8277810, baseEnd_8277810] using wordTrace_append hprefix tailTrace_8277810
  have hstable : (prefixWord ++ tailWord_8277810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277810).length < 2 ^ (prefixWord ++ tailWord_8277810).sum := by decide
  have hdescent : baseEnd_8277810 < baseStart_8277810 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277816 : List Nat := [2, 1, 2, 1, 3, 4, 2, 1, 7]
def baseStart_8277816 : Nat := 118140960795 + 8277816 * 2 ^ 59
def prefixEnd_8277816 : Nat := 4983230072969 + 3 ^ 40 * 8277816 * 2
def baseEnd_8277816 : Nat := 472277597497587804503447

theorem tailTrace_8277816 : CollatzResearch.WordTrace tailWord_8277816 prefixEnd_8277816 472277597497587804503447 := by
  unfold tailWord_8277816
  simp only [CollatzResearch.WordTrace]
  refine ⟨150958376489446922632222651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201277835319262563509630201 150958376489446922632222651)
  ·
    refine ⟨226437564734170383948333977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150958376489446922632222651 226437564734170383948333977)
    ·
      refine ⟨169828173550627787961250483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226437564734170383948333977 169828173550627787961250483)
      ·
        refine ⟨254742260325941681941875725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169828173550627787961250483 254742260325941681941875725)
        ·
          refine ⟨95528347622228130728203397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254742260325941681941875725 95528347622228130728203397)
          ·
            refine ⟨17911565179167774511538137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95528347622228130728203397 17911565179167774511538137)
            ·
              refine ⟨13433673884375830883653603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17911565179167774511538137 13433673884375830883653603)
              ·
                refine ⟨20150510826563746325480405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13433673884375830883653603 20150510826563746325480405)
                ·
                  refine ⟨472277597497587804503447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20150510826563746325480405 472277597497587804503447)
                  ·
                    rfl

theorem cell23_8277816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 7].length) (baseStart_8277816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277816 prefixEnd_8277816 := by exact prefixLift 8277816
  have htrace : WordTrace (prefixWord ++ tailWord_8277816) baseStart_8277816 baseEnd_8277816 := by
    simpa [prefixWord, tailWord_8277816, baseEnd_8277816] using wordTrace_append hprefix tailTrace_8277816
  have hstable : (prefixWord ++ tailWord_8277816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277816).length < 2 ^ (prefixWord ++ tailWord_8277816).sum := by decide
  have hdescent : baseEnd_8277816 < baseStart_8277816 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277827 : List Nat := [1, 1, 1, 3, 1, 6, 3, 1, 2, 2, 2]
def baseStart_8277827 : Nat := 118140960795 + 8277827 * 2 ^ 59
def prefixEnd_8277827 : Nat := 4983230072969 + 3 ^ 40 * 8277827 * 2
def baseEnd_8277827 : Nat := 4250504025765489697493473

theorem tailTrace_8277827 : CollatzResearch.WordTrace tailWord_8277827 prefixEnd_8277827 4250504025765489697493473 := by
  unfold tailWord_8277827
  simp only [CollatzResearch.WordTrace]
  refine ⟨301917154181853994143095735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201278102787902662762063823 301917154181853994143095735)
  ·
    refine ⟨452875731272780991214643603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301917154181853994143095735 452875731272780991214643603)
    ·
      refine ⟨679313596909171486821965405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452875731272780991214643603 679313596909171486821965405)
      ·
        refine ⟨254742598840939307558237027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 679313596909171486821965405 254742598840939307558237027)
        ·
          refine ⟨382113898261408961337355541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254742598840939307558237027 382113898261408961337355541)
          ·
            refine ⟨17911588981003545062688541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 382113898261408961337355541 17911588981003545062688541)
            ·
              refine ⟨6716845867876329398508203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17911588981003545062688541 6716845867876329398508203)
              ·
                refine ⟨10075268801814494097762305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6716845867876329398508203 10075268801814494097762305)
                ·
                  refine ⟨7556451601360870573321729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10075268801814494097762305 7556451601360870573321729)
                  ·
                    refine ⟨5667338701020652929991297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7556451601360870573321729 5667338701020652929991297)
                    ·
                      refine ⟨4250504025765489697493473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5667338701020652929991297 4250504025765489697493473)
                      ·
                        rfl

theorem cell23_8277827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 2, 2, 2].length) (baseStart_8277827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277827 prefixEnd_8277827 := by exact prefixLift 8277827
  have htrace : WordTrace (prefixWord ++ tailWord_8277827) baseStart_8277827 baseEnd_8277827 := by
    simpa [prefixWord, tailWord_8277827, baseEnd_8277827] using wordTrace_append hprefix tailTrace_8277827
  have hstable : (prefixWord ++ tailWord_8277827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277827).length < 2 ^ (prefixWord ++ tailWord_8277827).sum := by decide
  have hdescent : baseEnd_8277827 < baseStart_8277827 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277829 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 3, 7]
def baseStart_8277829 : Nat := 118140960795 + 8277829 * 2 ^ 59
def prefixEnd_8277829 : Nat := 4983230072969 + 3 ^ 40 * 8277829 * 2
def baseEnd_8277829 : Nat := 1416835017575599563222821

theorem tailTrace_8277829 : CollatzResearch.WordTrace tailWord_8277829 prefixEnd_8277829 1416835017575599563222821 := by
  unfold tailWord_8277829
  simp only [CollatzResearch.WordTrace]
  refine ⟨301917227127846748484668541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201278151418564498989779027 301917227127846748484668541)
  ·
    refine ⟨113218960172942530681750703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301917227127846748484668541 113218960172942530681750703)
    ·
      refine ⟨169828440259413796022626055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113218960172942530681750703 169828440259413796022626055)
      ·
        refine ⟨254742660389120694033939083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169828440259413796022626055 254742660389120694033939083)
        ·
          refine ⟨382113990583681041050908625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254742660389120694033939083 382113990583681041050908625)
          ·
            refine ⟨286585492937760780788181469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382113990583681041050908625 286585492937760780788181469)
            ·
              refine ⟨107469559851660292795568051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286585492937760780788181469 107469559851660292795568051)
              ·
                refine ⟨161204339777490439193352077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107469559851660292795568051 161204339777490439193352077)
                ·
                  refine ⟨60451627416558914697507029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161204339777490439193352077 60451627416558914697507029)
                  ·
                    refine ⟨1416835017575599563222821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60451627416558914697507029 1416835017575599563222821)
                    ·
                      rfl

theorem cell23_8277829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_8277829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277829 prefixEnd_8277829 := by exact prefixLift 8277829
  have htrace : WordTrace (prefixWord ++ tailWord_8277829) baseStart_8277829 baseEnd_8277829 := by
    simpa [prefixWord, tailWord_8277829, baseEnd_8277829] using wordTrace_append hprefix tailTrace_8277829
  have hstable : (prefixWord ++ tailWord_8277829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277829).length < 2 ^ (prefixWord ++ tailWord_8277829).sum := by decide
  have hdescent : baseEnd_8277829 < baseStart_8277829 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277878 : List Nat := [5, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2]
def baseStart_8277878 : Nat := 118140960795 + 8277878 * 2 ^ 59
def prefixEnd_8277878 : Nat := 4983230072969 + 3 ^ 40 * 8277878 * 2
def baseEnd_8277878 : Nat := 4250530213278868997955739

theorem tailTrace_8277878 : CollatzResearch.WordTrace tailWord_8277878 prefixEnd_8277878 4250530213278868997955739 := by
  unfold tailWord_8277878
  simp only [CollatzResearch.WordTrace]
  refine ⟨18869938394041826865825143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201279342869779486568801525 18869938394041826865825143)
  ·
    refine ⟨28304907591062740298737715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18869938394041826865825143 28304907591062740298737715)
    ·
      refine ⟨42457361386594110448106573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28304907591062740298737715 42457361386594110448106573)
      ·
        refine ⟨15921510519972791418039965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42457361386594110448106573 15921510519972791418039965)
        ·
          refine ⟨5970566444989796781764987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15921510519972791418039965 5970566444989796781764987)
          ·
            refine ⟨8955849667484695172647481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5970566444989796781764987 8955849667484695172647481)
            ·
              refine ⟨6716887250613521379485611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8955849667484695172647481 6716887250613521379485611)
              ·
                refine ⟨10075330875920282069228417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6716887250613521379485611 10075330875920282069228417)
                ·
                  refine ⟨7556498156940211551921313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10075330875920282069228417 7556498156940211551921313)
                  ·
                    refine ⟨5667373617705158663940985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7556498156940211551921313 5667373617705158663940985)
                    ·
                      refine ⟨4250530213278868997955739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5667373617705158663940985 4250530213278868997955739)
                      ·
                        rfl

theorem cell23_8277878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_8277878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277878 prefixEnd_8277878 := by exact prefixLift 8277878
  have htrace : WordTrace (prefixWord ++ tailWord_8277878) baseStart_8277878 baseEnd_8277878 := by
    simpa [prefixWord, tailWord_8277878, baseEnd_8277878] using wordTrace_append hprefix tailTrace_8277878
  have hstable : (prefixWord ++ tailWord_8277878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277878).length < 2 ^ (prefixWord ++ tailWord_8277878).sum := by decide
  have hdescent : baseEnd_8277878 < baseStart_8277878 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277927 : List Nat := [1, 1, 6, 1, 2, 2, 1, 4, 1, 4]
def baseStart_8277927 : Nat := 118140960795 + 8277927 * 2 ^ 59
def prefixEnd_8277927 : Nat := 4983230072969 + 3 ^ 40 * 8277927 * 2
def baseEnd_8277927 : Nat := 1416851791276979768747671

theorem tailTrace_8277927 : CollatzResearch.WordTrace tailWord_8277927 prefixEnd_8277927 1416851791276979768747671 := by
  unfold tailWord_8277927
  simp only [CollatzResearch.WordTrace]
  refine ⟨301920801481491711221736035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201280534320994474147824023 301920801481491711221736035)
  ·
    refine ⟨452881202222237566832604053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301920801481491711221736035 452881202222237566832604053)
    ·
      refine ⟨21228806354167385945278315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 452881202222237566832604053 21228806354167385945278315)
      ·
        refine ⟨31843209531251078917917473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21228806354167385945278315 31843209531251078917917473)
        ·
          refine ⟨23882407148438309188438105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31843209531251078917917473 23882407148438309188438105)
          ·
            refine ⟨17911805361328731891328579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23882407148438309188438105 17911805361328731891328579)
            ·
              refine ⟨26867708041993097836992869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17911805361328731891328579 26867708041993097836992869)
              ·
                refine ⟨5037695257873705844436163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26867708041993097836992869 5037695257873705844436163)
                ·
                  refine ⟨7556542886810558766654245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5037695257873705844436163 7556542886810558766654245)
                  ·
                    refine ⟨1416851791276979768747671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7556542886810558766654245 1416851791276979768747671)
                    ·
                      rfl

theorem cell23_8277927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_8277927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277927 prefixEnd_8277927 := by exact prefixLift 8277927
  have htrace : WordTrace (prefixWord ++ tailWord_8277927) baseStart_8277927 baseEnd_8277927 := by
    simpa [prefixWord, tailWord_8277927, baseEnd_8277927] using wordTrace_append hprefix tailTrace_8277927
  have hstable : (prefixWord ++ tailWord_8277927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277927).length < 2 ^ (prefixWord ++ tailWord_8277927).sum := by decide
  have hdescent : baseEnd_8277927 < baseStart_8277927 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277943 : List Nat := [1, 1, 3, 1, 3, 1, 1, 4, 1, 5, 2]
def baseStart_8277943 : Nat := 118140960795 + 8277943 * 2 ^ 59
def prefixEnd_8277943 : Nat := 4983230072969 + 3 ^ 40 * 8277943 * 2
def baseEnd_8277943 : Nat := 4250563589521411243642939

theorem tailTrace_8277943 : CollatzResearch.WordTrace tailWord_8277943 prefixEnd_8277943 4250563589521411243642939 := by
  unfold tailWord_8277943
  simp only [CollatzResearch.WordTrace]
  refine ⟨301921385049433745954318483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201280923366289163969545655 301921385049433745954318483)
  ·
    refine ⟨452882077574150618931477725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301921385049433745954318483 452882077574150618931477725)
    ·
      refine ⟨169830779090306482099304147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452882077574150618931477725 169830779090306482099304147)
      ·
        refine ⟨254746168635459723148956221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169830779090306482099304147 254746168635459723148956221)
        ·
          refine ⟨95529813238297396180858583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254746168635459723148956221 95529813238297396180858583)
          ·
            refine ⟨143294719857446094271287875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95529813238297396180858583 143294719857446094271287875)
            ·
              refine ⟨214942079786169141406931813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143294719857446094271287875 214942079786169141406931813)
              ·
                refine ⟨40301639959906714013799715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214942079786169141406931813 40301639959906714013799715)
                ·
                  refine ⟨60452459939860071020699573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40301639959906714013799715 60452459939860071020699573)
                  ·
                    refine ⟨5667418119361881658190585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60452459939860071020699573 5667418119361881658190585)
                    ·
                      refine ⟨4250563589521411243642939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5667418119361881658190585 4250563589521411243642939)
                      ·
                        rfl

theorem cell23_8277943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 5, 2].length) (baseStart_8277943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277943 prefixEnd_8277943 := by exact prefixLift 8277943
  have htrace : WordTrace (prefixWord ++ tailWord_8277943) baseStart_8277943 baseEnd_8277943 := by
    simpa [prefixWord, tailWord_8277943, baseEnd_8277943] using wordTrace_append hprefix tailTrace_8277943
  have hstable : (prefixWord ++ tailWord_8277943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277943).length < 2 ^ (prefixWord ++ tailWord_8277943).sum := by decide
  have hdescent : baseEnd_8277943 < baseStart_8277943 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277950 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3]
def baseStart_8277950 : Nat := 118140960795 + 8277950 * 2 ^ 59
def prefixEnd_8277950 : Nat := 4983230072969 + 3 ^ 40 * 8277950 * 2
def baseEnd_8277950 : Nat := 4250567183885992716255407

theorem tailTrace_8277950 : CollatzResearch.WordTrace tailWord_8277950 prefixEnd_8277950 4250567183885992716255407 := by
  unfold tailWord_8277950
  simp only [CollatzResearch.WordTrace]
  refine ⟨37740205045051048268727913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201281093573605590766548869 37740205045051048268727913)
  ·
    refine ⟨28305153783788286201545935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37740205045051048268727913 28305153783788286201545935)
    ·
      refine ⟨42457730675682429302318903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28305153783788286201545935 42457730675682429302318903)
      ·
        refine ⟨63686596013523643953478355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42457730675682429302318903 63686596013523643953478355)
        ·
          refine ⟨95529894020285465930217533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63686596013523643953478355 95529894020285465930217533)
          ·
            refine ⟨35823710257607049723831575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95529894020285465930217533 35823710257607049723831575)
            ·
              refine ⟨53735565386410574585747363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35823710257607049723831575 53735565386410574585747363)
              ·
                refine ⟨80603348079615861878621045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53735565386410574585747363 80603348079615861878621045)
                ·
                  refine ⟨7556563882463987051120723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80603348079615861878621045 7556563882463987051120723)
                  ·
                    refine ⟨11334845823695980576681085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7556563882463987051120723 11334845823695980576681085)
                    ·
                      refine ⟨4250567183885992716255407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11334845823695980576681085 4250567183885992716255407)
                      ·
                        rfl

theorem cell23_8277950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_8277950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277950 prefixEnd_8277950 := by exact prefixLift 8277950
  have htrace : WordTrace (prefixWord ++ tailWord_8277950) baseStart_8277950 baseEnd_8277950 := by
    simpa [prefixWord, tailWord_8277950, baseEnd_8277950] using wordTrace_append hprefix tailTrace_8277950
  have hstable : (prefixWord ++ tailWord_8277950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277950).length < 2 ^ (prefixWord ++ tailWord_8277950).sum := by decide
  have hdescent : baseEnd_8277950 < baseStart_8277950 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277960 : List Nat := [2, 1, 3, 1, 4, 2, 1, 1, 1, 5, 2]
def baseStart_8277960 : Nat := 118140960795 + 8277960 * 2 ^ 59
def prefixEnd_8277960 : Nat := 4983230072969 + 3 ^ 40 * 8277960 * 2
def baseEnd_8277960 : Nat := 4250572318692537677130361

theorem tailTrace_8277960 : CollatzResearch.WordTrace tailWord_8277960 prefixEnd_8277960 4250572318692537677130361 := by
  unfold tailWord_8277960
  simp only [CollatzResearch.WordTrace]
  refine ⟨150961002545186078928843667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201281336726914771905124889 150961002545186078928843667)
  ·
    refine ⟨226441503817779118393265501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150961002545186078928843667 226441503817779118393265501)
    ·
      refine ⟨84915563931667169397474563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226441503817779118393265501 84915563931667169397474563)
      ·
        refine ⟨127373345897500754096211845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84915563931667169397474563 127373345897500754096211845)
        ·
          refine ⟨23882502355781391393039721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127373345897500754096211845 23882502355781391393039721)
          ·
            refine ⟨17911876766836043544779791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23882502355781391393039721 17911876766836043544779791)
            ·
              refine ⟨26867815150254065317169687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17911876766836043544779791 26867815150254065317169687)
              ·
                refine ⟨40301722725381097975754531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26867815150254065317169687 40301722725381097975754531)
                ·
                  refine ⟨60452584088071646963631797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40301722725381097975754531 60452584088071646963631797)
                  ·
                    refine ⟨5667429758256716902840481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60452584088071646963631797 5667429758256716902840481)
                    ·
                      refine ⟨4250572318692537677130361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5667429758256716902840481 4250572318692537677130361)
                      ·
                        rfl

theorem cell23_8277960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 1, 5, 2].length) (baseStart_8277960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277960 prefixEnd_8277960 := by exact prefixLift 8277960
  have htrace : WordTrace (prefixWord ++ tailWord_8277960) baseStart_8277960 baseEnd_8277960 := by
    simpa [prefixWord, tailWord_8277960, baseEnd_8277960] using wordTrace_append hprefix tailTrace_8277960
  have hstable : (prefixWord ++ tailWord_8277960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277960).length < 2 ^ (prefixWord ++ tailWord_8277960).sum := by decide
  have hdescent : baseEnd_8277960 < baseStart_8277960 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277967 : List Nat := [1, 1, 2, 1, 1, 5, 4, 3, 1, 1, 3]
def baseStart_8277967 : Nat := 118140960795 + 8277967 * 2 ^ 59
def prefixEnd_8277967 : Nat := 4983230072969 + 3 ^ 40 * 8277967 * 2
def baseEnd_8277967 : Nat := 4250575913057119149742829

theorem tailTrace_8277967 : CollatzResearch.WordTrace tailWord_8277967 prefixEnd_8277967 4250575913057119149742829 := by
  unfold tailWord_8277967
  simp only [CollatzResearch.WordTrace]
  refine ⟨301922260401346798053192155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201281506934231198702128103 301922260401346798053192155)
  ·
    refine ⟨452883390602020197079788233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301922260401346798053192155 452883390602020197079788233)
    ·
      refine ⟨339662542951515147809841175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452883390602020197079788233 339662542951515147809841175)
      ·
        refine ⟨509493814427272721714761763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339662542951515147809841175 509493814427272721714761763)
        ·
          refine ⟨764240721640909082572142645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509493814427272721714761763 764240721640909082572142645)
          ·
            refine ⟨71647567653835226491138373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 764240721640909082572142645 71647567653835226491138373)
            ·
              refine ⟨13433918935094104967088445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71647567653835226491138373 13433918935094104967088445)
              ·
                refine ⟨5037719600660289362658167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13433918935094104967088445 5037719600660289362658167)
                ·
                  refine ⟨7556579400990434043987251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5037719600660289362658167 7556579400990434043987251)
                  ·
                    refine ⟨11334869101485651065980877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7556579400990434043987251 11334869101485651065980877)
                    ·
                      refine ⟨4250575913057119149742829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11334869101485651065980877 4250575913057119149742829)
                      ·
                        rfl

theorem cell23_8277967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3, 1, 1, 3].length) (baseStart_8277967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277967 prefixEnd_8277967 := by exact prefixLift 8277967
  have htrace : WordTrace (prefixWord ++ tailWord_8277967) baseStart_8277967 baseEnd_8277967 := by
    simpa [prefixWord, tailWord_8277967, baseEnd_8277967] using wordTrace_append hprefix tailTrace_8277967
  have hstable : (prefixWord ++ tailWord_8277967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277967).length < 2 ^ (prefixWord ++ tailWord_8277967).sum := by decide
  have hdescent : baseEnd_8277967 < baseStart_8277967 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8277974 : List Nat := [5, 2, 1, 1, 4, 1, 1, 2, 6]
def baseStart_8277974 : Nat := 118140960795 + 8277974 * 2 ^ 59
def prefixEnd_8277974 : Nat := 4983230072969 + 3 ^ 40 * 8277974 * 2
def baseEnd_8277974 : Nat := 472286611935744513595033

theorem tailTrace_8277974 : CollatzResearch.WordTrace tailWord_8277974 prefixEnd_8277974 472286611935744513595033 := by
  unfold tailWord_8277974
  simp only [CollatzResearch.WordTrace]
  refine ⟨18870157232020089890543561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201281677141547625499131317 18870157232020089890543561)
  ·
    refine ⟨14152617924015067417907671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18870157232020089890543561 14152617924015067417907671)
    ·
      refine ⟨21228926886022601126861507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14152617924015067417907671 21228926886022601126861507)
      ·
        refine ⟨31843390329033901690292261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21228926886022601126861507 31843390329033901690292261)
        ·
          refine ⟨5970635686693856566929799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31843390329033901690292261 5970635686693856566929799)
          ·
            refine ⟨8955953530040784850394699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5970635686693856566929799 8955953530040784850394699)
            ·
              refine ⟨13433930295061177275592049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8955953530040784850394699 13433930295061177275592049)
              ·
                refine ⟨10075447721295882956694037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13433930295061177275592049 10075447721295882956694037)
                ·
                  refine ⟨472286611935744513595033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10075447721295882956694037 472286611935744513595033)
                  ·
                    rfl

theorem cell23_8277974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_8277974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8277974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8277974 prefixEnd_8277974 := by exact prefixLift 8277974
  have htrace : WordTrace (prefixWord ++ tailWord_8277974) baseStart_8277974 baseEnd_8277974 := by
    simpa [prefixWord, tailWord_8277974, baseEnd_8277974] using wordTrace_append hprefix tailTrace_8277974
  have hstable : (prefixWord ++ tailWord_8277974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8277974).length < 2 ^ (prefixWord ++ tailWord_8277974).sum := by decide
  have hdescent : baseEnd_8277974 < baseStart_8277974 := by decide
  rcases family_descends (prefixWord ++ tailWord_8277974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278013 : List Nat := [1, 4, 1, 1, 1, 2, 6, 7]
def baseStart_8278013 : Nat := 118140960795 + 8278013 * 2 ^ 59
def prefixEnd_8278013 : Nat := 4983230072969 + 3 ^ 40 * 8278013 * 2
def baseEnd_8278013 : Nat := 157429612339526887769171

theorem tailTrace_8278013 : CollatzResearch.WordTrace tailWord_8278013 prefixEnd_8278013 157429612339526887769171 := by
  unfold tailWord_8278013
  simp only [CollatzResearch.WordTrace]
  refine ⟨301923938159180147909366693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201282625439453431939577795 301923938159180147909366693)
  ·
    refine ⟨56610738404846277733006255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301923938159180147909366693 56610738404846277733006255)
    ·
      refine ⟨84916107607269416599509383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56610738404846277733006255 84916107607269416599509383)
      ·
        refine ⟨127374161410904124899264075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84916107607269416599509383 127374161410904124899264075)
        ·
          refine ⟨191061242116356187348896113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127374161410904124899264075 191061242116356187348896113)
          ·
            refine ⟨143295931587267140511672085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191061242116356187348896113 143295931587267140511672085)
            ·
              refine ⟨6716996793153147211484629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 143295931587267140511672085 6716996793153147211484629)
              ·
                refine ⟨157429612339526887769171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6716996793153147211484629 157429612339526887769171)
                ·
                  rfl

theorem cell23_8278013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 7].length) (baseStart_8278013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278013 prefixEnd_8278013 := by exact prefixLift 8278013
  have htrace : WordTrace (prefixWord ++ tailWord_8278013) baseStart_8278013 baseEnd_8278013 := by
    simpa [prefixWord, tailWord_8278013, baseEnd_8278013] using wordTrace_append hprefix tailTrace_8278013
  have hstable : (prefixWord ++ tailWord_8278013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278013).length < 2 ^ (prefixWord ++ tailWord_8278013).sum := by decide
  have hdescent : baseEnd_8278013 < baseStart_8278013 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278040 : List Nat := [2, 1, 2, 3, 2, 1, 1, 3, 4, 1, 3]
def baseStart_8278040 : Nat := 118140960795 + 8278040 * 2 ^ 59
def prefixEnd_8278040 : Nat := 4983230072969 + 3 ^ 40 * 8278040 * 2
def baseEnd_8278040 : Nat := 4250613397144897364129993

theorem tailTrace_8278040 : CollatzResearch.WordTrace tailWord_8278040 prefixEnd_8278040 4250613397144897364129993 := by
  unfold tailWord_8278040
  simp only [CollatzResearch.WordTrace]
  refine ⟨150962461465041165760299787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201283281953388221013733049 150962461465041165760299787)
  ·
    refine ⟨226443692197561748640449681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150962461465041165760299787 226443692197561748640449681)
    ·
      refine ⟨169832769148171311480337261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226443692197561748640449681 169832769148171311480337261)
      ·
        refine ⟨63687288430564241805126473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169832769148171311480337261 63687288430564241805126473)
        ·
          refine ⟨47765466322923181353844855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63687288430564241805126473 47765466322923181353844855)
          ·
            refine ⟨71648199484384772030767283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47765466322923181353844855 71648199484384772030767283)
            ·
              refine ⟨107472299226577158046150925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71648199484384772030767283 107472299226577158046150925)
              ·
                refine ⟨40302112209966434267306597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107472299226577158046150925 40302112209966434267306597)
                ·
                  refine ⟨7556646039368706425119987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40302112209966434267306597 7556646039368706425119987)
                  ·
                    refine ⟨11334969059053059637679981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7556646039368706425119987 11334969059053059637679981)
                    ·
                      refine ⟨4250613397144897364129993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11334969059053059637679981 4250613397144897364129993)
                      ·
                        rfl

theorem cell23_8278040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_8278040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278040 prefixEnd_8278040 := by exact prefixLift 8278040
  have htrace : WordTrace (prefixWord ++ tailWord_8278040) baseStart_8278040 baseEnd_8278040 := by
    simpa [prefixWord, tailWord_8278040, baseEnd_8278040] using wordTrace_append hprefix tailTrace_8278040
  have hstable : (prefixWord ++ tailWord_8278040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278040).length < 2 ^ (prefixWord ++ tailWord_8278040).sum := by decide
  have hdescent : baseEnd_8278040 < baseStart_8278040 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278067 : List Nat := [1, 1, 1, 2, 4, 1, 5, 2, 1, 3, 2]
def baseStart_8278067 : Nat := 118140960795 + 8278067 * 2 ^ 59
def prefixEnd_8278067 : Nat := 4983230072969 + 3 ^ 40 * 8278067 * 2
def baseEnd_8278067 : Nat := 4250627261122568758492369

theorem tailTrace_8278067 : CollatzResearch.WordTrace tailWord_8278067 prefixEnd_8278067 4250627261122568758492369 := by
  unfold tailWord_8278067
  simp only [CollatzResearch.WordTrace]
  refine ⟨301925907700984515131832455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201283938467323010087888303 301925907700984515131832455)
  ·
    refine ⟨452888861551476772697748683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301925907700984515131832455 452888861551476772697748683)
    ·
      refine ⟨679333292327215159046623025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452888861551476772697748683 679333292327215159046623025)
      ·
        refine ⟨509499969245411369284967269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 679333292327215159046623025 509499969245411369284967269)
        ·
          refine ⟨95531244233514631740931363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 509499969245411369284967269 95531244233514631740931363)
          ·
            refine ⟨143296866350271947611397045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95531244233514631740931363 143296866350271947611397045)
            ·
              refine ⟨13434081220337995088568473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143296866350271947611397045 13434081220337995088568473)
              ·
                refine ⟨10075560915253496316426355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13434081220337995088568473 10075560915253496316426355)
                ·
                  refine ⟨15113341372880244474639533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10075560915253496316426355 15113341372880244474639533)
                  ·
                    refine ⟨5667503014830091677989825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15113341372880244474639533 5667503014830091677989825)
                    ·
                      refine ⟨4250627261122568758492369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5667503014830091677989825 4250627261122568758492369)
                      ·
                        rfl

theorem cell23_8278067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 3, 2].length) (baseStart_8278067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278067 prefixEnd_8278067 := by exact prefixLift 8278067
  have htrace : WordTrace (prefixWord ++ tailWord_8278067) baseStart_8278067 baseEnd_8278067 := by
    simpa [prefixWord, tailWord_8278067, baseEnd_8278067] using wordTrace_append hprefix tailTrace_8278067
  have hstable : (prefixWord ++ tailWord_8278067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278067).length < 2 ^ (prefixWord ++ tailWord_8278067).sum := by decide
  have hdescent : baseEnd_8278067 < baseStart_8278067 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278080 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 3, 4, 2]
def baseStart_8278080 : Nat := 118140960795 + 8278080 * 2 ^ 59
def prefixEnd_8278080 : Nat := 4983230072969 + 3 ^ 40 * 8278080 * 2
def baseEnd_8278080 : Nat := 4250633936371077207629809

theorem tailTrace_8278080 : CollatzResearch.WordTrace tailWord_8278080 prefixEnd_8278080 4250633936371077207629809 := by
  unfold tailWord_8278080
  simp only [CollatzResearch.WordTrace]
  refine ⟨150963190924968709176027847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201284254566624945568037129 150963190924968709176027847)
  ·
    refine ⟨226444786387453063764041771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150963190924968709176027847 226444786387453063764041771)
    ·
      refine ⟨339667179581179595646062657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226444786387453063764041771 339667179581179595646062657)
      ·
        refine ⟨254750384685884696734546993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339667179581179595646062657 254750384685884696734546993)
        ·
          refine ⟨191062788514413522550910245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254750384685884696734546993 191062788514413522550910245)
          ·
            refine ⟨35824272846452535478295671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191062788514413522550910245 35824272846452535478295671)
            ·
              refine ⟨53736409269678803217443507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35824272846452535478295671 53736409269678803217443507)
              ·
                refine ⟨80604613904518204826165261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53736409269678803217443507 80604613904518204826165261)
                ·
                  refine ⟨30226730214194326809811973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80604613904518204826165261 30226730214194326809811973)
                  ·
                    refine ⟨5667511915161436276839745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30226730214194326809811973 5667511915161436276839745)
                    ·
                      refine ⟨4250633936371077207629809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5667511915161436276839745 4250633936371077207629809)
                      ·
                        rfl

theorem cell23_8278080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 3, 4, 2].length) (baseStart_8278080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278080 prefixEnd_8278080 := by exact prefixLift 8278080
  have htrace : WordTrace (prefixWord ++ tailWord_8278080) baseStart_8278080 baseEnd_8278080 := by
    simpa [prefixWord, tailWord_8278080, baseEnd_8278080] using wordTrace_append hprefix tailTrace_8278080
  have hstable : (prefixWord ++ tailWord_8278080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278080).length < 2 ^ (prefixWord ++ tailWord_8278080).sum := by decide
  have hdescent : baseEnd_8278080 < baseStart_8278080 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278137 : List Nat := [1, 2, 1, 3, 4, 2, 2, 3, 5]
def baseStart_8278137 : Nat := 118140960795 + 8278137 * 2 ^ 59
def prefixEnd_8278137 : Nat := 4983230072969 + 3 ^ 40 * 8278137 * 2
def baseEnd_8278137 : Nat := 472295911640931498290783

theorem tailTrace_8278137 : CollatzResearch.WordTrace tailWord_8278137 prefixEnd_8278137 472295911640931498290783 := by
  unfold tailWord_8278137
  simp only [CollatzResearch.WordTrace]
  refine ⟨301928460810730917086880665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201285640540487278057920443 301928460810730917086880665)
  ·
    refine ⟨226446345608048187815160499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301928460810730917086880665 226446345608048187815160499)
    ·
      refine ⟨339669518412072281722740749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226446345608048187815160499 339669518412072281722740749)
      ·
        refine ⟨127376069404527105646027781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339669518412072281722740749 127376069404527105646027781)
        ·
          refine ⟨23883013013348832308630209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127376069404527105646027781 23883013013348832308630209)
          ·
            refine ⟨17912259760011624231472657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23883013013348832308630209 17912259760011624231472657)
            ·
              refine ⟨13434194820008718173604493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17912259760011624231472657 13434194820008718173604493)
              ·
                refine ⟨5037823057503269315101685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13434194820008718173604493 5037823057503269315101685)
                ·
                  refine ⟨472295911640931498290783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5037823057503269315101685 472295911640931498290783)
                  ·
                    rfl

theorem cell23_8278137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3, 5].length) (baseStart_8278137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278137 prefixEnd_8278137 := by exact prefixLift 8278137
  have htrace : WordTrace (prefixWord ++ tailWord_8278137) baseStart_8278137 baseEnd_8278137 := by
    simpa [prefixWord, tailWord_8278137, baseEnd_8278137] using wordTrace_append hprefix tailTrace_8278137
  have hstable : (prefixWord ++ tailWord_8278137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278137).length < 2 ^ (prefixWord ++ tailWord_8278137).sum := by decide
  have hdescent : baseEnd_8278137 < baseStart_8278137 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278213 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 1, 1, 8]
def baseStart_8278213 : Nat := 118140960795 + 8278213 * 2 ^ 59
def prefixEnd_8278213 : Nat := 4983230072969 + 3 ^ 40 * 8278213 * 2
def baseEnd_8278213 : Nat := 4250702229298125187266697

theorem tailTrace_8278213 : CollatzResearch.WordTrace tailWord_8278213 prefixEnd_8278213 4250702229298125187266697 := by
  unfold tailWord_8278213
  simp only [CollatzResearch.WordTrace]
  refine ⟨301931232758455582066647293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201287488505637054711098195 301931232758455582066647293)
  ·
    refine ⟨113224212284420843274992735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301931232758455582066647293 113224212284420843274992735)
    ·
      refine ⟨169836318426631264912489103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113224212284420843274992735 169836318426631264912489103)
      ·
        refine ⟨254754477639946897368733655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169836318426631264912489103 254754477639946897368733655)
        ·
          refine ⟨382131716459920346053100483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254754477639946897368733655 382131716459920346053100483)
          ·
            refine ⟨573197574689880519079650725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382131716459920346053100483 573197574689880519079650725)
            ·
              refine ⟨107474545254352597327434511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 573197574689880519079650725 107474545254352597327434511)
              ·
                refine ⟨161211817881528895991151767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107474545254352597327434511 161211817881528895991151767)
                ·
                  refine ⟨241817726822293343986727651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161211817881528895991151767 241817726822293343986727651)
                  ·
                    refine ⟨362726590233440015980091477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 241817726822293343986727651 362726590233440015980091477)
                    ·
                      refine ⟨4250702229298125187266697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 362726590233440015980091477 4250702229298125187266697)
                      ·
                        rfl

theorem cell23_8278213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_8278213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278213 prefixEnd_8278213 := by exact prefixLift 8278213
  have htrace : WordTrace (prefixWord ++ tailWord_8278213) baseStart_8278213 baseEnd_8278213 := by
    simpa [prefixWord, tailWord_8278213, baseEnd_8278213] using wordTrace_append hprefix tailTrace_8278213
  have hstable : (prefixWord ++ tailWord_8278213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278213).length < 2 ^ (prefixWord ++ tailWord_8278213).sum := by decide
  have hdescent : baseEnd_8278213 < baseStart_8278213 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278240 : List Nat := [2, 1, 1, 3, 1, 3, 3, 1, 3, 5]
def baseStart_8278240 : Nat := 118140960795 + 8278240 * 2 ^ 59
def prefixEnd_8278240 : Nat := 4983230072969 + 3 ^ 40 * 8278240 * 2
def baseEnd_8278240 : Nat := 1416905364425265527209691

theorem tailTrace_8278240 : CollatzResearch.WordTrace tailWord_8278240 prefixEnd_8278240 1416905364425265527209691 := by
  unfold tailWord_8278240
  simp only [CollatzResearch.WordTrace]
  refine ⟨150966108764678882838940087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201288145019571843785253449 150966108764678882838940087)
  ·
    refine ⟨226449163147018324258410131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150966108764678882838940087 226449163147018324258410131)
    ·
      refine ⟨339673744720527486387615197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226449163147018324258410131 339673744720527486387615197)
      ·
        refine ⟨127377654270197807395355699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339673744720527486387615197 127377654270197807395355699)
        ·
          refine ⟨191066481405296711093033549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127377654270197807395355699 191066481405296711093033549)
          ·
            refine ⟨71649930526986266659887581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191066481405296711093033549 71649930526986266659887581)
            ·
              refine ⟨26868723947619849997457843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71649930526986266659887581 26868723947619849997457843)
              ·
                refine ⟨40303085921429774996186765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26868723947619849997457843 40303085921429774996186765)
                ·
                  refine ⟨15113657220536165623570037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40303085921429774996186765 15113657220536165623570037)
                  ·
                    refine ⟨1416905364425265527209691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15113657220536165623570037 1416905364425265527209691)
                    ·
                      rfl

theorem cell23_8278240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 3, 5].length) (baseStart_8278240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278240 prefixEnd_8278240 := by exact prefixLift 8278240
  have htrace : WordTrace (prefixWord ++ tailWord_8278240) baseStart_8278240 baseEnd_8278240 := by
    simpa [prefixWord, tailWord_8278240, baseEnd_8278240] using wordTrace_append hprefix tailTrace_8278240
  have hstable : (prefixWord ++ tailWord_8278240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278240).length < 2 ^ (prefixWord ++ tailWord_8278240).sum := by decide
  have hdescent : baseEnd_8278240 < baseStart_8278240 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278298 : List Nat := [3, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2]
def baseStart_8278298 : Nat := 118140960795 + 8278298 * 2 ^ 59
def prefixEnd_8278298 : Nat := 4983230072969 + 3 ^ 40 * 8278298 * 2
def baseEnd_8278298 : Nat := 4250745875153757354703807

theorem tailTrace_8278298 : CollatzResearch.WordTrace tailWord_8278298 prefixEnd_8278298 4250745875153757354703807 := by
  unfold tailWord_8278298
  simp only [CollatzResearch.WordTrace]
  refine ⟨75483583240786910395872887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201289555308765094388994365 75483583240786910395872887)
  ·
    refine ⟨113225374861180365593809331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75483583240786910395872887 113225374861180365593809331)
    ·
      refine ⟨169838062291770548390713997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113225374861180365593809331 169838062291770548390713997)
      ·
        refine ⟨63689273359413955646517749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169838062291770548390713997 63689273359413955646517749)
        ·
          refine ⟨5970869377445058341861039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63689273359413955646517749 5970869377445058341861039)
          ·
            refine ⟨8956304066167587512791559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5970869377445058341861039 8956304066167587512791559)
            ·
              refine ⟨13434456099251381269187339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8956304066167587512791559 13434456099251381269187339)
              ·
                refine ⟨20151684148877071903781009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13434456099251381269187339 20151684148877071903781009)
                ·
                  refine ⟨15113763111657803927835757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20151684148877071903781009 15113763111657803927835757)
                  ·
                    refine ⟨5667661166871676472938409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15113763111657803927835757 5667661166871676472938409)
                    ·
                      refine ⟨4250745875153757354703807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5667661166871676472938409 4250745875153757354703807)
                      ·
                        rfl

theorem cell23_8278298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_8278298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278298 prefixEnd_8278298 := by exact prefixLift 8278298
  have htrace : WordTrace (prefixWord ++ tailWord_8278298) baseStart_8278298 baseEnd_8278298 := by
    simpa [prefixWord, tailWord_8278298, baseEnd_8278298] using wordTrace_append hprefix tailTrace_8278298
  have hstable : (prefixWord ++ tailWord_8278298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278298).length < 2 ^ (prefixWord ++ tailWord_8278298).sum := by decide
  have hdescent : baseEnd_8278298 < baseStart_8278298 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278321 : List Nat := [1, 2, 2, 3, 4, 2, 1, 2, 2, 4]
def baseStart_8278321 : Nat := 118140960795 + 8278321 * 2 ^ 59
def prefixEnd_8278321 : Nat := 4983230072969 + 3 ^ 40 * 8278321 * 2
def baseEnd_8278321 : Nat := 1416919228402936921572067

theorem tailTrace_8278321 : CollatzResearch.WordTrace tailWord_8278321 prefixEnd_8278321 1416919228402936921572067 := by
  unfold tailWord_8278321
  simp only [CollatzResearch.WordTrace]
  refine ⟨301935171842064316511578817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201290114561376211007719211 301935171842064316511578817)
  ·
    refine ⟨226451378881548237383684113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301935171842064316511578817 226451378881548237383684113)
    ·
      refine ⟨169838534161161178037763085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226451378881548237383684113 169838534161161178037763085)
      ·
        refine ⟨63689450310435441764161157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169838534161161178037763085 63689450310435441764161157)
        ·
          refine ⟨11941771933206645330780217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63689450310435441764161157 11941771933206645330780217)
          ·
            refine ⟨8956328949904983998085163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11941771933206645330780217 8956328949904983998085163)
            ·
              refine ⟨13434493424857475997127745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8956328949904983998085163 13434493424857475997127745)
              ·
                refine ⟨10075870068643106997845809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13434493424857475997127745 10075870068643106997845809)
                ·
                  refine ⟨7556902551482330248384357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10075870068643106997845809 7556902551482330248384357)
                  ·
                    refine ⟨1416919228402936921572067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7556902551482330248384357 1416919228402936921572067)
                    ·
                      rfl

theorem cell23_8278321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2, 4].length) (baseStart_8278321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278321 prefixEnd_8278321 := by exact prefixLift 8278321
  have htrace : WordTrace (prefixWord ++ tailWord_8278321) baseStart_8278321 baseEnd_8278321 := by
    simpa [prefixWord, tailWord_8278321, baseEnd_8278321] using wordTrace_append hprefix tailTrace_8278321
  have hstable : (prefixWord ++ tailWord_8278321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278321).length < 2 ^ (prefixWord ++ tailWord_8278321).sum := by decide
  have hdescent : baseEnd_8278321 < baseStart_8278321 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278344 : List Nat := [2, 1, 3, 1, 1, 2, 2, 5, 2, 1, 3]
def baseStart_8278344 : Nat := 118140960795 + 8278344 * 2 ^ 59
def prefixEnd_8278344 : Nat := 4983230072969 + 3 ^ 40 * 8278344 * 2
def baseEnd_8278344 : Nat := 4250769495263864174728595

theorem tailTrace_8278344 : CollatzResearch.WordTrace tailWord_8278344 prefixEnd_8278344 4250769495263864174728595 := by
  unfold tailWord_8278344
  simp only [CollatzResearch.WordTrace]
  refine ⟨150968005360490495719833043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201290673813987327626444057 150968005360490495719833043)
  ·
    refine ⟨226452008040735743579749565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150968005360490495719833043 226452008040735743579749565)
    ·
      refine ⟨84919503015275903842406087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226452008040735743579749565 84919503015275903842406087)
      ·
        refine ⟨127379254522913855763609131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84919503015275903842406087 127379254522913855763609131)
        ·
          refine ⟨191068881784370783645413697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127379254522913855763609131 191068881784370783645413697)
          ·
            refine ⟨143301661338278087734060273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191068881784370783645413697 143301661338278087734060273)
            ·
              refine ⟨107476246003708565800545205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143301661338278087734060273 107476246003708565800545205)
              ·
                refine ⟨10075898062847678043801113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107476246003708565800545205 10075898062847678043801113)
                ·
                  refine ⟨7556923547135758532850835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10075898062847678043801113 7556923547135758532850835)
                  ·
                    refine ⟨11335385320703637799276253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7556923547135758532850835 11335385320703637799276253)
                    ·
                      refine ⟨4250769495263864174728595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11335385320703637799276253 4250769495263864174728595)
                      ·
                        rfl

theorem cell23_8278344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_8278344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278344 prefixEnd_8278344 := by exact prefixLift 8278344
  have htrace : WordTrace (prefixWord ++ tailWord_8278344) baseStart_8278344 baseEnd_8278344 := by
    simpa [prefixWord, tailWord_8278344, baseEnd_8278344] using wordTrace_append hprefix tailTrace_8278344
  have hstable : (prefixWord ++ tailWord_8278344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278344).length < 2 ^ (prefixWord ++ tailWord_8278344).sum := by decide
  have hdescent : baseEnd_8278344 < baseStart_8278344 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278350 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8]
def baseStart_8278350 : Nat := 118140960795 + 8278350 * 2 ^ 59
def prefixEnd_8278350 : Nat := 4983230072969 + 3 ^ 40 * 8278350 * 2
def baseEnd_8278350 : Nat := 4250772576147791151253567

theorem tailTrace_8278350 : CollatzResearch.WordTrace tailWord_8278350 prefixEnd_8278350 4250772576147791151253567 := by
  unfold tailWord_8278350
  simp only [CollatzResearch.WordTrace]
  refine ⟨37742028694869906808048063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201290819705972836309589669 37742028694869906808048063)
  ·
    refine ⟨56613043042304860212072095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37742028694869906808048063 56613043042304860212072095)
    ·
      refine ⟨84919564563457290318108143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56613043042304860212072095 84919564563457290318108143)
      ·
        refine ⟨127379346845185935477162215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84919564563457290318108143 127379346845185935477162215)
        ·
          refine ⟨191069020267778903215743323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127379346845185935477162215 191069020267778903215743323)
          ·
            refine ⟨286603530401668354823614985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191069020267778903215743323 286603530401668354823614985)
            ·
              refine ⟨214952647801251266117711239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286603530401668354823614985 214952647801251266117711239)
              ·
                refine ⟨322428971701876899176566859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214952647801251266117711239 322428971701876899176566859)
                ·
                  refine ⟨483643457552815348764850289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322428971701876899176566859 483643457552815348764850289)
                  ·
                    refine ⟨362732593164611511573637717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 483643457552815348764850289 362732593164611511573637717)
                    ·
                      refine ⟨4250772576147791151253567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 362732593164611511573637717 4250772576147791151253567)
                      ·
                        rfl

theorem cell23_8278350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_8278350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278350 prefixEnd_8278350 := by exact prefixLift 8278350
  have htrace : WordTrace (prefixWord ++ tailWord_8278350) baseStart_8278350 baseEnd_8278350 := by
    simpa [prefixWord, tailWord_8278350, baseEnd_8278350] using wordTrace_append hprefix tailTrace_8278350
  have hstable : (prefixWord ++ tailWord_8278350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278350).length < 2 ^ (prefixWord ++ tailWord_8278350).sum := by decide
  have hdescent : baseEnd_8278350 < baseStart_8278350 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278354 : List Nat := [3, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2]
def baseStart_8278354 : Nat := 118140960795 + 8278354 * 2 ^ 59
def prefixEnd_8278354 : Nat := 4983230072969 + 3 ^ 40 * 8278354 * 2
def baseEnd_8278354 : Nat := 4250774630070409135603549

theorem tailTrace_8278354 : CollatzResearch.WordTrace tailWord_8278354 prefixEnd_8278354 4250774630070409135603549 := by
  unfold tailWord_8278354
  simp only [CollatzResearch.WordTrace]
  refine ⟨75484093862736190786882529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201290916967296508765020077 75484093862736190786882529)
  ·
    refine ⟨56613070397052143090161897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75484093862736190786882529 56613070397052143090161897)
    ·
      refine ⟨42459802797789107317621423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56613070397052143090161897 42459802797789107317621423)
      ·
        refine ⟨63689704196683660976432135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42459802797789107317621423 63689704196683660976432135)
        ·
          refine ⟨95534556295025491464648203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63689704196683660976432135 95534556295025491464648203)
          ·
            refine ⟨143301834442538237196972305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95534556295025491464648203 143301834442538237196972305)
            ·
              refine ⟨107476375831903677897729229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143301834442538237196972305 107476375831903677897729229)
              ·
                refine ⟨40303640936963879211648461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107476375831903677897729229 40303640936963879211648461)
                ·
                  refine ⟨15113865351361454704368173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40303640936963879211648461 15113865351361454704368173)
                  ·
                    refine ⟨5667699506760545514138065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15113865351361454704368173 5667699506760545514138065)
                    ·
                      refine ⟨4250774630070409135603549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5667699506760545514138065 4250774630070409135603549)
                      ·
                        rfl

theorem cell23_8278354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_8278354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278354 prefixEnd_8278354 := by exact prefixLift 8278354
  have htrace : WordTrace (prefixWord ++ tailWord_8278354) baseStart_8278354 baseEnd_8278354 := by
    simpa [prefixWord, tailWord_8278354, baseEnd_8278354] using wordTrace_append hprefix tailTrace_8278354
  have hstable : (prefixWord ++ tailWord_8278354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278354).length < 2 ^ (prefixWord ++ tailWord_8278354).sum := by decide
  have hdescent : baseEnd_8278354 < baseStart_8278354 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278360 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 4, 6]
def baseStart_8278360 : Nat := 118140960795 + 8278360 * 2 ^ 59
def prefixEnd_8278360 : Nat := 4983230072969 + 3 ^ 40 * 8278360 * 2
def baseEnd_8278360 : Nat := 1416925903651445370709507

theorem tailTrace_8278360 : CollatzResearch.WordTrace tailWord_8278360 prefixEnd_8278360 1416925903651445370709507 := by
  unfold tailWord_8278360
  simp only [CollatzResearch.WordTrace]
  refine ⟨150968297144461513086124267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201291062859282017448165689 150968297144461513086124267)
  ·
    refine ⟨226452445716692269629186401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150968297144461513086124267 226452445716692269629186401)
    ·
      refine ⟨169839334287519202221889801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226452445716692269629186401 169839334287519202221889801)
      ·
        refine ⟨127379500715639401666417351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169839334287519202221889801 127379500715639401666417351)
        ·
          refine ⟨191069251073459102499626027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127379500715639401666417351 191069251073459102499626027)
          ·
            refine ⟨286603876610188653749439041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191069251073459102499626027 286603876610188653749439041)
            ·
              refine ⟨214952907457641490312079281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286603876610188653749439041 214952907457641490312079281)
              ·
                refine ⟨161214680593231117734059461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214952907457641490312079281 161214680593231117734059461)
                ·
                  refine ⟨30227752611230834575136149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161214680593231117734059461 30227752611230834575136149)
                  ·
                    refine ⟨1416925903651445370709507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30227752611230834575136149 1416925903651445370709507)
                    ·
                      rfl

theorem cell23_8278360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 4, 6].length) (baseStart_8278360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278360 prefixEnd_8278360 := by exact prefixLift 8278360
  have htrace : WordTrace (prefixWord ++ tailWord_8278360) baseStart_8278360 baseEnd_8278360 := by
    simpa [prefixWord, tailWord_8278360, baseEnd_8278360] using wordTrace_append hprefix tailTrace_8278360
  have hstable : (prefixWord ++ tailWord_8278360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278360).length < 2 ^ (prefixWord ++ tailWord_8278360).sum := by decide
  have hdescent : baseEnd_8278360 < baseStart_8278360 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278434 : List Nat := [3, 3, 1, 2, 1, 1, 2, 2, 2, 3, 3]
def baseStart_8278434 : Nat := 118140960795 + 8278434 * 2 ^ 59
def prefixEnd_8278434 : Nat := 4983230072969 + 3 ^ 40 * 8278434 * 2
def baseEnd_8278434 : Nat := 4250815708522768822603181

theorem tailTrace_8278434 : CollatzResearch.WordTrace tailWord_8278434 prefixEnd_8278434 4250815708522768822603181 := by
  unfold tailWord_8278434
  simp only [CollatzResearch.WordTrace]
  refine ⟨75484823322663734202610589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201292862193769957873628237 75484823322663734202610589)
  ·
    refine ⟨28306808745998900325978971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75484823322663734202610589 28306808745998900325978971)
    ·
      refine ⟨42460213118998350488968457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28306808745998900325978971 42460213118998350488968457)
      ·
        refine ⟨31845159839248762866726343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42460213118998350488968457 31845159839248762866726343)
        ·
          refine ⟨47767739758873144300089515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31845159839248762866726343 47767739758873144300089515)
          ·
            refine ⟨71651609638309716450134273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47767739758873144300089515 71651609638309716450134273)
            ·
              refine ⟨53738707228732287337600705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71651609638309716450134273 53738707228732287337600705)
              ·
                refine ⟨40304030421549215503200529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53738707228732287337600705 40304030421549215503200529)
                ·
                  refine ⟨30228022816161911627400397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40304030421549215503200529 30228022816161911627400397)
                  ·
                    refine ⟨11335508556060716860275149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30228022816161911627400397 11335508556060716860275149)
                    ·
                      refine ⟨4250815708522768822603181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11335508556060716860275149 4250815708522768822603181)
                      ·
                        rfl

theorem cell23_8278434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_8278434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278434 prefixEnd_8278434 := by exact prefixLift 8278434
  have htrace : WordTrace (prefixWord ++ tailWord_8278434) baseStart_8278434 baseEnd_8278434 := by
    simpa [prefixWord, tailWord_8278434, baseEnd_8278434] using wordTrace_append hprefix tailTrace_8278434
  have hstable : (prefixWord ++ tailWord_8278434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278434).length < 2 ^ (prefixWord ++ tailWord_8278434).sum := by decide
  have hdescent : baseEnd_8278434 < baseStart_8278434 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278437 : List Nat := [1, 3, 1, 2, 1, 1, 3, 4, 2, 5]
def baseStart_8278437 : Nat := 118140960795 + 8278437 * 2 ^ 59
def prefixEnd_8278437 : Nat := 4983230072969 + 3 ^ 40 * 8278437 * 2
def baseEnd_8278437 : Nat := 1416939082988244103621889

theorem tailTrace_8278437 : CollatzResearch.WordTrace tailWord_8278437 prefixEnd_8278437 1416939082988244103621889 := by
  unfold tailWord_8278437
  simp only [CollatzResearch.WordTrace]
  refine ⟨301939402709644068322801565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201292935139762712215201043 301939402709644068322801565)
  ·
    refine ⟨113227276016116525621050587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301939402709644068322801565 113227276016116525621050587)
    ·
      refine ⟨169840914024174788431575881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113227276016116525621050587 169840914024174788431575881)
      ·
        refine ⟨127380685518131091323681911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169840914024174788431575881 127380685518131091323681911)
        ·
          refine ⟨191071028277196636985522867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127380685518131091323681911 191071028277196636985522867)
          ·
            refine ⟨286606542415794955478284301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191071028277196636985522867 286606542415794955478284301)
            ·
              refine ⟨107477453405923108304356613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286606542415794955478284301 107477453405923108304356613)
              ·
                refine ⟨20152022513610582807066865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107477453405923108304356613 20152022513610582807066865)
                ·
                  refine ⟨15114016885207937105300149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20152022513610582807066865 15114016885207937105300149)
                  ·
                    refine ⟨1416939082988244103621889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15114016885207937105300149 1416939082988244103621889)
                    ·
                      rfl

theorem cell23_8278437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 5].length) (baseStart_8278437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278437 prefixEnd_8278437 := by exact prefixLift 8278437
  have htrace : WordTrace (prefixWord ++ tailWord_8278437) baseStart_8278437 baseEnd_8278437 := by
    simpa [prefixWord, tailWord_8278437, baseEnd_8278437] using wordTrace_append hprefix tailTrace_8278437
  have hstable : (prefixWord ++ tailWord_8278437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278437).length < 2 ^ (prefixWord ++ tailWord_8278437).sum := by decide
  have hdescent : baseEnd_8278437 < baseStart_8278437 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278474 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 1, 6, 2]
def baseStart_8278474 : Nat := 118140960795 + 8278474 * 2 ^ 59
def prefixEnd_8278474 : Nat := 4983230072969 + 3 ^ 40 * 8278474 * 2
def baseEnd_8278474 : Nat := 4250836247748948666102997

theorem tailTrace_8278474 : CollatzResearch.WordTrace tailWord_8278474 prefixEnd_8278474 4250836247748948666102997 := by
  unfold tailWord_8278474
  simp only [CollatzResearch.WordTrace]
  refine ⟨75485188052627505910474619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201293834807006682427932317 75485188052627505910474619)
  ·
    refine ⟨113227782078941258865711929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75485188052627505910474619 113227782078941258865711929)
    ·
      refine ⟨84920836559205944149283947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113227782078941258865711929 84920836559205944149283947)
      ·
        refine ⟨127381254838808916223925921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84920836559205944149283947 127381254838808916223925921)
        ·
          refine ⟨95535941129106687167944441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127381254838808916223925921 95535941129106687167944441)
          ·
            refine ⟨71651955846830015375958331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95535941129106687167944441 71651955846830015375958331)
            ·
              refine ⟨107477933770245023063937497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71651955846830015375958331 107477933770245023063937497)
              ·
                refine ⟨80608450327683767297953123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107477933770245023063937497 80608450327683767297953123)
                ·
                  refine ⟨120912675491525650946929685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80608450327683767297953123 120912675491525650946929685)
                  ·
                    refine ⟨5667781663665264888137329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 120912675491525650946929685 5667781663665264888137329)
                    ·
                      refine ⟨4250836247748948666102997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5667781663665264888137329 4250836247748948666102997)
                      ·
                        rfl

theorem cell23_8278474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 1, 6, 2].length) (baseStart_8278474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278474 prefixEnd_8278474 := by exact prefixLift 8278474
  have htrace : WordTrace (prefixWord ++ tailWord_8278474) baseStart_8278474 baseEnd_8278474 := by
    simpa [prefixWord, tailWord_8278474, baseEnd_8278474] using wordTrace_append hprefix tailTrace_8278474
  have hstable : (prefixWord ++ tailWord_8278474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278474).length < 2 ^ (prefixWord ++ tailWord_8278474).sum := by decide
  have hdescent : baseEnd_8278474 < baseStart_8278474 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278497 : List Nat := [1, 2, 3, 1, 2, 2, 3, 1, 8]
def baseStart_8278497 : Nat := 118140960795 + 8278497 * 2 ^ 59
def prefixEnd_8278497 : Nat := 4983230072969 + 3 ^ 40 * 8278497 * 2
def baseEnd_8278497 : Nat := 472316450867111341790599

theorem tailTrace_8278497 : CollatzResearch.WordTrace tailWord_8278497 prefixEnd_8278497 472316450867111341790599 := by
  unfold tailWord_8278497
  simp only [CollatzResearch.WordTrace]
  refine ⟨301941591089426698569985745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201294394059617799046657163 301941591089426698569985745)
  ·
    refine ⟨226456193317070023927489309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301941591089426698569985745 226456193317070023927489309)
    ·
      refine ⟨84921072493901258972808491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226456193317070023927489309 84921072493901258972808491)
      ·
        refine ⟨127381608740851888459212737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84921072493901258972808491 127381608740851888459212737)
        ·
          refine ⟨95536206555638916344409553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127381608740851888459212737 95536206555638916344409553)
          ·
            refine ⟨71652154916729187258307165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95536206555638916344409553 71652154916729187258307165)
            ·
              refine ⟨26869558093773445221865187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71652154916729187258307165 26869558093773445221865187)
              ·
                refine ⟨40304337140660167832797781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26869558093773445221865187 40304337140660167832797781)
                ·
                  refine ⟨472316450867111341790599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40304337140660167832797781 472316450867111341790599)
                  ·
                    rfl

theorem cell23_8278497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 8].length) (baseStart_8278497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278497 prefixEnd_8278497 := by exact prefixLift 8278497
  have htrace : WordTrace (prefixWord ++ tailWord_8278497) baseStart_8278497 baseEnd_8278497 := by
    simpa [prefixWord, tailWord_8278497, baseEnd_8278497] using wordTrace_append hprefix tailTrace_8278497
  have hstable : (prefixWord ++ tailWord_8278497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278497).length < 2 ^ (prefixWord ++ tailWord_8278497).sum := by decide
  have hdescent : baseEnd_8278497 < baseStart_8278497 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278535 : List Nat := [1, 1, 4, 3, 3, 2, 1, 3, 1, 4]
def baseStart_8278535 : Nat := 118140960795 + 8278535 * 2 ^ 59
def prefixEnd_8278535 : Nat := 4983230072969 + 3 ^ 40 * 8278535 * 2
def baseEnd_8278535 : Nat := 1416955856689624309146739

theorem tailTrace_8278535 : CollatzResearch.WordTrace tailWord_8278535 prefixEnd_8278535 1416955856689624309146739 := by
  unfold tailWord_8278535
  simp only [CollatzResearch.WordTrace]
  refine ⟨301942977063289031059869059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201295318042192687373246039 301942977063289031059869059)
  ·
    refine ⟨452914465594933546589803589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301942977063289031059869059 452914465594933546589803589)
    ·
      refine ⟨84921462299050039985588173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 452914465594933546589803589 84921462299050039985588173)
      ·
        refine ⟨31845548362143764994595565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84921462299050039985588173 31845548362143764994595565)
        ·
          refine ⟨11942080635803911872973337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31845548362143764994595565 11942080635803911872973337)
          ·
            refine ⟨8956560476852933904730003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11942080635803911872973337 8956560476852933904730003)
            ·
              refine ⟨13434840715279400857095005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8956560476852933904730003 13434840715279400857095005)
              ·
                refine ⟨5038065268229775321410627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13434840715279400857095005 5038065268229775321410627)
                ·
                  refine ⟨7557097902344662982115941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5038065268229775321410627 7557097902344662982115941)
                  ·
                    refine ⟨1416955856689624309146739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7557097902344662982115941 1416955856689624309146739)
                    ·
                      rfl

theorem cell23_8278535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_8278535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278535 prefixEnd_8278535 := by exact prefixLift 8278535
  have htrace : WordTrace (prefixWord ++ tailWord_8278535) baseStart_8278535 baseEnd_8278535 := by
    simpa [prefixWord, tailWord_8278535, baseEnd_8278535] using wordTrace_append hprefix tailTrace_8278535
  have hstable : (prefixWord ++ tailWord_8278535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278535).length < 2 ^ (prefixWord ++ tailWord_8278535).sum := by decide
  have hdescent : baseEnd_8278535 < baseStart_8278535 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278615 : List Nat := [1, 1, 3, 2, 2, 2, 3, 4, 1, 2, 2]
def baseStart_8278615 : Nat := 118140960795 + 8278615 * 2 ^ 59
def prefixEnd_8278615 : Nat := 4983230072969 + 3 ^ 40 * 8278615 * 2
def baseEnd_8278615 : Nat := 4250908648521232614439849

theorem tailTrace_8278615 : CollatzResearch.WordTrace tailWord_8278615 prefixEnd_8278615 4250908648521232614439849 := by
  unfold tailWord_8278615
  simp only [CollatzResearch.WordTrace]
  refine ⟨301945894902999204722781299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201297263268666136481854199 301945894902999204722781299)
  ·
    refine ⟨452918842354498807084171949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301945894902999204722781299 452918842354498807084171949)
    ·
      refine ⟨169844565882937052656564481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452918842354498807084171949 169844565882937052656564481)
      ·
        refine ⟨127383424412202789492423361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169844565882937052656564481 127383424412202789492423361)
        ·
          refine ⟨95537568309152092119317521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127383424412202789492423361 95537568309152092119317521)
          ·
            refine ⟨71653176231864069089488141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95537568309152092119317521 71653176231864069089488141)
            ·
              refine ⟨26869941086949025908558053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71653176231864069089488141 26869941086949025908558053)
              ·
                refine ⟨5038113953802942357854635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26869941086949025908558053 5038113953802942357854635)
                ·
                  refine ⟨7557170930704413536781953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5038113953802942357854635 7557170930704413536781953)
                  ·
                    refine ⟨5667878198028310152586465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7557170930704413536781953 5667878198028310152586465)
                    ·
                      refine ⟨4250908648521232614439849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5667878198028310152586465 4250908648521232614439849)
                      ·
                        rfl

theorem cell23_8278615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4, 1, 2, 2].length) (baseStart_8278615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278615 prefixEnd_8278615 := by exact prefixLift 8278615
  have htrace : WordTrace (prefixWord ++ tailWord_8278615) baseStart_8278615 baseEnd_8278615 := by
    simpa [prefixWord, tailWord_8278615, baseEnd_8278615] using wordTrace_append hprefix tailTrace_8278615
  have hstable : (prefixWord ++ tailWord_8278615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278615).length < 2 ^ (prefixWord ++ tailWord_8278615).sum := by decide
  have hdescent : baseEnd_8278615 < baseStart_8278615 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278631 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 6, 1, 3]
def baseStart_8278631 : Nat := 118140960795 + 8278631 * 2 ^ 59
def prefixEnd_8278631 : Nat := 4983230072969 + 3 ^ 40 * 8278631 * 2
def baseEnd_8278631 : Nat := 4250916864211704551839775

theorem tailTrace_8278631 : CollatzResearch.WordTrace tailWord_8278631 prefixEnd_8278631 4250916864211704551839775 := by
  unfold tailWord_8278631
  simp only [CollatzResearch.WordTrace]
  refine ⟨301946478470941239455363747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201297652313960826303575831 301946478470941239455363747)
  ·
    refine ⟨452919717706411859183045621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301946478470941239455363747 452919717706411859183045621)
    ·
      refine ⟨42461223534976111798410527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 452919717706411859183045621 42461223534976111798410527)
      ·
        refine ⟨63691835302464167697615791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42461223534976111798410527 63691835302464167697615791)
        ·
          refine ⟨95537752953696251546423687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63691835302464167697615791 95537752953696251546423687)
          ·
            refine ⟨143306629430544377319635531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95537752953696251546423687 143306629430544377319635531)
            ·
              refine ⟨214959944145816565979453297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143306629430544377319635531 214959944145816565979453297)
              ·
                refine ⟨161219958109362424484589973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214959944145816565979453297 161219958109362424484589973)
                ·
                  refine ⟨7557185536376363647715155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 161219958109362424484589973 7557185536376363647715155)
                  ·
                    refine ⟨11335778304564545471572733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7557185536376363647715155 11335778304564545471572733)
                    ·
                      refine ⟨4250916864211704551839775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11335778304564545471572733 4250916864211704551839775)
                      ·
                        rfl

theorem cell23_8278631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_8278631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278631 prefixEnd_8278631 := by exact prefixLift 8278631
  have htrace : WordTrace (prefixWord ++ tailWord_8278631) baseStart_8278631 baseEnd_8278631 := by
    simpa [prefixWord, tailWord_8278631, baseEnd_8278631] using wordTrace_append hprefix tailTrace_8278631
  have hstable : (prefixWord ++ tailWord_8278631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278631).length < 2 ^ (prefixWord ++ tailWord_8278631).sum := by decide
  have hdescent : baseEnd_8278631 < baseStart_8278631 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278634 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 2, 7]
def baseStart_8278634 : Nat := 118140960795 + 8278634 * 2 ^ 59
def prefixEnd_8278634 : Nat := 4983230072969 + 3 ^ 40 * 8278634 * 2
def baseEnd_8278634 : Nat := 1416972801551222680034087

theorem tailTrace_8278634 : CollatzResearch.WordTrace tailWord_8278634 prefixEnd_8278634 1416972801551222680034087 := by
  unfold tailWord_8278634
  simp only [CollatzResearch.WordTrace]
  refine ⟨75486646972482592741930739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201297725259953580645148637 75486646972482592741930739)
  ·
    refine ⟨113229970458723889112896109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75486646972482592741930739 113229970458723889112896109)
    ·
      refine ⟨42461238922021458417336041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113229970458723889112896109 42461238922021458417336041)
      ·
        refine ⟨31845929191516093813002031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42461238922021458417336041 31845929191516093813002031)
        ·
          refine ⟨47768893787274140719503047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31845929191516093813002031 47768893787274140719503047)
          ·
            refine ⟨71653340680911211079254571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47768893787274140719503047 71653340680911211079254571)
            ·
              refine ⟨107480011021366816618881857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71653340680911211079254571 107480011021366816618881857)
              ·
                refine ⟨80610008266025112464161393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107480011021366816618881857 80610008266025112464161393)
                ·
                  refine ⟨60457506199518834348121045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80610008266025112464161393 60457506199518834348121045)
                  ·
                    refine ⟨1416972801551222680034087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60457506199518834348121045 1416972801551222680034087)
                    ·
                      rfl

theorem cell23_8278634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_8278634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278634 prefixEnd_8278634 := by exact prefixLift 8278634
  have htrace : WordTrace (prefixWord ++ tailWord_8278634) baseStart_8278634 baseEnd_8278634 := by
    simpa [prefixWord, tailWord_8278634, baseEnd_8278634] using wordTrace_append hprefix tailTrace_8278634
  have hstable : (prefixWord ++ tailWord_8278634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278634).length < 2 ^ (prefixWord ++ tailWord_8278634).sum := by decide
  have hdescent : baseEnd_8278634 < baseStart_8278634 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278682 : List Nat := [3, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3]
def baseStart_8278682 : Nat := 118140960795 + 8278682 * 2 ^ 59
def prefixEnd_8278682 : Nat := 4983230072969 + 3 ^ 40 * 8278682 * 2
def baseEnd_8278682 : Nat := 4250943051725083852302041

theorem tailTrace_8278682 : CollatzResearch.WordTrace tailWord_8278682 prefixEnd_8278682 4250943051725083852302041 := by
  unfold tailWord_8278682
  simp only [CollatzResearch.WordTrace]
  refine ⟨75487084648439118791367575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201298892395837650110313533 75487084648439118791367575)
  ·
    refine ⟨113230626972658678187051363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75487084648439118791367575 113230626972658678187051363)
    ·
      refine ⟨169845940458988017280577045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113230626972658678187051363 169845940458988017280577045)
      ·
        refine ⟨7961528459015063310027049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 169845940458988017280577045 7961528459015063310027049)
        ·
          refine ⟨5971146344261297482520287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7961528459015063310027049 5971146344261297482520287)
          ·
            refine ⟨8956719516391946223780431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5971146344261297482520287 8956719516391946223780431)
            ·
              refine ⟨13435079274587919335670647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8956719516391946223780431 13435079274587919335670647)
              ·
                refine ⟨20152618911881879003505971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13435079274587919335670647 20152618911881879003505971)
                ·
                  refine ⟨30228928367822818505258957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20152618911881879003505971 30228928367822818505258957)
                  ·
                    refine ⟨11335848137933556939472109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30228928367822818505258957 11335848137933556939472109)
                    ·
                      refine ⟨4250943051725083852302041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11335848137933556939472109 4250943051725083852302041)
                      ·
                        rfl

theorem cell23_8278682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_8278682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278682 prefixEnd_8278682 := by exact prefixLift 8278682
  have htrace : WordTrace (prefixWord ++ tailWord_8278682) baseStart_8278682 baseEnd_8278682 := by
    simpa [prefixWord, tailWord_8278682, baseEnd_8278682] using wordTrace_append hprefix tailTrace_8278682
  have hstable : (prefixWord ++ tailWord_8278682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278682).length < 2 ^ (prefixWord ++ tailWord_8278682).sum := by decide
  have hdescent : baseEnd_8278682 < baseStart_8278682 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278761 : List Nat := [1, 2, 1, 1, 1, 2, 5, 3, 2, 1, 4]
def baseStart_8278761 : Nat := 118140960795 + 8278761 * 2 ^ 59
def prefixEnd_8278761 : Nat := 4983230072969 + 3 ^ 40 * 8278761 * 2
def baseEnd_8278761 : Nat := 4250983616696789043214177

theorem tailTrace_8278761 : CollatzResearch.WordTrace tailWord_8278761 prefixEnd_8278761 4250983616696789043214177 := by
  unfold tailWord_8278761
  simp only [CollatzResearch.WordTrace]
  refine ⟨301951219960470271657596137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201300813306980181105064091 301951219960470271657596137)
  ·
    refine ⟨226463414970352703743197103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301951219960470271657596137 226463414970352703743197103)
    ·
      refine ⟨339695122455529055614795655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226463414970352703743197103 339695122455529055614795655)
      ·
        refine ⟨509542683683293583422193483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339695122455529055614795655 509542683683293583422193483)
        ·
          refine ⟨764314025524940375133290225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509542683683293583422193483 764314025524940375133290225)
          ·
            refine ⟨573235519143705281349967669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 764314025524940375133290225 573235519143705281349967669)
            ·
              refine ⟨53740829919722370126559469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 573235519143705281349967669 53740829919722370126559469)
              ·
                refine ⟨20152811219895888797459801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53740829919722370126559469 20152811219895888797459801)
                ·
                  refine ⟨15114608414921916598094851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20152811219895888797459801 15114608414921916598094851)
                  ·
                    refine ⟨22671912622382874897142277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15114608414921916598094851 22671912622382874897142277)
                    ·
                      refine ⟨4250983616696789043214177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22671912622382874897142277 4250983616696789043214177)
                      ·
                        rfl

theorem cell23_8278761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 1, 4].length) (baseStart_8278761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278761 prefixEnd_8278761 := by exact prefixLift 8278761
  have htrace : WordTrace (prefixWord ++ tailWord_8278761) baseStart_8278761 baseEnd_8278761 := by
    simpa [prefixWord, tailWord_8278761, baseEnd_8278761] using wordTrace_append hprefix tailTrace_8278761
  have hstable : (prefixWord ++ tailWord_8278761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278761).length < 2 ^ (prefixWord ++ tailWord_8278761).sum := by decide
  have hdescent : baseEnd_8278761 < baseStart_8278761 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278788 : List Nat := [2, 3, 2, 2, 1, 1, 2, 3, 3, 4]
def baseStart_8278788 : Nat := 118140960795 + 8278788 * 2 ^ 59
def prefixEnd_8278788 : Nat := 4983230072969 + 3 ^ 40 * 8278788 * 2
def baseEnd_8278788 : Nat := 1416999160224820145858851

theorem tailTrace_8278788 : CollatzResearch.WordTrace tailWord_8278788 prefixEnd_8278788 1416999160224820145858851 := by
  unfold tailWord_8278788
  simp only [CollatzResearch.WordTrace]
  refine ⟨150976102365686227634414509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201301469820914970179219345 150976102365686227634414509)
  ·
    refine ⟨56616038387132335362905441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150976102365686227634414509 56616038387132335362905441)
    ·
      refine ⟨42462028790349251522179081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56616038387132335362905441 42462028790349251522179081)
      ·
        refine ⟨31846521592761938641634311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42462028790349251522179081 31846521592761938641634311)
        ·
          refine ⟨47769782389142907962451467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31846521592761938641634311 47769782389142907962451467)
          ·
            refine ⟨71654673583714361943677201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47769782389142907962451467 71654673583714361943677201)
            ·
              refine ⟨53741005187785771457757901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71654673583714361943677201 53741005187785771457757901)
              ·
                refine ⟨20152876945419664296659213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53741005187785771457757901 20152876945419664296659213)
                ·
                  refine ⟨7557328854532374111247205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20152876945419664296659213 7557328854532374111247205)
                  ·
                    refine ⟨1416999160224820145858851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7557328854532374111247205 1416999160224820145858851)
                    ·
                      rfl

theorem cell23_8278788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_8278788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278788 prefixEnd_8278788 := by exact prefixLift 8278788
  have htrace : WordTrace (prefixWord ++ tailWord_8278788) baseStart_8278788 baseEnd_8278788 := by
    simpa [prefixWord, tailWord_8278788, baseEnd_8278788] using wordTrace_append hprefix tailTrace_8278788
  have hstable : (prefixWord ++ tailWord_8278788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278788).length < 2 ^ (prefixWord ++ tailWord_8278788).sum := by decide
  have hdescent : baseEnd_8278788 < baseStart_8278788 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278801 : List Nat := [1, 2, 2, 1, 1, 3, 4, 3, 6]
def baseStart_8278801 : Nat := 118140960795 + 8278801 * 2 ^ 59
def prefixEnd_8278801 : Nat := 4983230072969 + 3 ^ 40 * 8278801 * 2
def baseEnd_8278801 : Nat := 472333795102552098523777

theorem tailTrace_8278801 : CollatzResearch.WordTrace tailWord_8278801 prefixEnd_8278801 472333795102552098523777 := by
  unfold tailWord_8278801
  simp only [CollatzResearch.WordTrace]
  refine ⟨301952678880325358489052257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201301785920216905659368171 301952678880325358489052257)
  ·
    refine ⟨226464509160244018866789193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301952678880325358489052257 226464509160244018866789193)
    ·
      refine ⟨169848381870183014150091895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226464509160244018866789193 169848381870183014150091895)
      ·
        refine ⟨254772572805274521225137843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169848381870183014150091895 254772572805274521225137843)
        ·
          refine ⟨382158859207911781837706765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254772572805274521225137843 382158859207911781837706765)
          ·
            refine ⟨143309572202966918189140037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382158859207911781837706765 143309572202966918189140037)
            ·
              refine ⟨26870544788056297160463757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143309572202966918189140037 26870544788056297160463757)
              ·
                refine ⟨10076454295521111435173909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26870544788056297160463757 10076454295521111435173909)
                ·
                  refine ⟨472333795102552098523777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10076454295521111435173909 472333795102552098523777)
                  ·
                    rfl

theorem cell23_8278801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 6].length) (baseStart_8278801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278801 prefixEnd_8278801 := by exact prefixLift 8278801
  have htrace : WordTrace (prefixWord ++ tailWord_8278801) baseStart_8278801 baseEnd_8278801 := by
    simpa [prefixWord, tailWord_8278801, baseEnd_8278801] using wordTrace_append hprefix tailTrace_8278801
  have hstable : (prefixWord ++ tailWord_8278801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278801).length < 2 ^ (prefixWord ++ tailWord_8278801).sum := by decide
  have hdescent : baseEnd_8278801 < baseStart_8278801 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278815 : List Nat := [1, 1, 2, 4, 2, 4, 1, 1, 2, 2, 3]
def baseStart_8278815 : Nat := 118140960795 + 8278815 * 2 ^ 59
def prefixEnd_8278815 : Nat := 4983230072969 + 3 ^ 40 * 8278815 * 2
def baseEnd_8278815 : Nat := 4251011344652131831938929

theorem tailTrace_8278815 : CollatzResearch.WordTrace tailWord_8278815 prefixEnd_8278815 4251011344652131831938929 := by
  unfold tailWord_8278815
  simp only [CollatzResearch.WordTrace]
  refine ⟨301953189502274638880061899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201302126334849759253374599 301953189502274638880061899)
  ·
    refine ⟨452929784253411958320092849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301953189502274638880061899 452929784253411958320092849)
    ·
      refine ⟨339697338190058968740069637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452929784253411958320092849 339697338190058968740069637)
      ·
        refine ⟨63693250910636056638763057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339697338190058968740069637 63693250910636056638763057)
        ·
          refine ⟨47769938182977042479072293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63693250910636056638763057 47769938182977042479072293)
          ·
            refine ⟨8956863409308195464826055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47769938182977042479072293 8956863409308195464826055)
            ·
              refine ⟨13435295113962293197239083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8956863409308195464826055 13435295113962293197239083)
              ·
                refine ⟨20152942670943439795858625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13435295113962293197239083 20152942670943439795858625)
                ·
                  refine ⟨15114707003207579846893969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20152942670943439795858625 15114707003207579846893969)
                  ·
                    refine ⟨11336030252405684885170477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15114707003207579846893969 11336030252405684885170477)
                    ·
                      refine ⟨4251011344652131831938929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11336030252405684885170477 4251011344652131831938929)
                      ·
                        rfl

theorem cell23_8278815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_8278815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278815 prefixEnd_8278815 := by exact prefixLift 8278815
  have htrace : WordTrace (prefixWord ++ tailWord_8278815) baseStart_8278815 baseEnd_8278815 := by
    simpa [prefixWord, tailWord_8278815, baseEnd_8278815] using wordTrace_append hprefix tailTrace_8278815
  have hstable : (prefixWord ++ tailWord_8278815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278815).length < 2 ^ (prefixWord ++ tailWord_8278815).sum := by decide
  have hdescent : baseEnd_8278815 < baseStart_8278815 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278828 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 3]
def baseStart_8278828 : Nat := 118140960795 + 8278828 * 2 ^ 59
def prefixEnd_8278828 : Nat := 4983230072969 + 3 ^ 40 * 8278828 * 2
def baseEnd_8278828 : Nat := 4251018019900640281076369

theorem tailTrace_8278828 : CollatzResearch.WordTrace tailWord_8278828 prefixEnd_8278828 4251018019900640281076369 := by
  unfold tailWord_8278828
  simp only [CollatzResearch.WordTrace]
  refine ⟨150976831825613771050142569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201302442434151694733523425 150976831825613771050142569)
  ·
    refine ⟨113232623869210328287606927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150976831825613771050142569 113232623869210328287606927)
    ·
      refine ⟨169848935803815492431410391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113232623869210328287606927 169848935803815492431410391)
      ·
        refine ⟨254773403705723238647115587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169848935803815492431410391 254773403705723238647115587)
        ·
          refine ⟨382160105558584857970673381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254773403705723238647115587 382160105558584857970673381)
          ·
            refine ⟨71655019792234660869501259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 382160105558584857970673381 71655019792234660869501259)
            ·
              refine ⟨107482529688351991304251889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71655019792234660869501259 107482529688351991304251889)
              ·
                refine ⟨80611897266263993478188917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107482529688351991304251889 80611897266263993478188917)
                ·
                  refine ⟨7557365368712249388580211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80611897266263993478188917 7557365368712249388580211)
                  ·
                    refine ⟨11336048053068374082870317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7557365368712249388580211 11336048053068374082870317)
                    ·
                      refine ⟨4251018019900640281076369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11336048053068374082870317 4251018019900640281076369)
                      ·
                        rfl

theorem cell23_8278828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 3].length) (baseStart_8278828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278828 prefixEnd_8278828 := by exact prefixLift 8278828
  have htrace : WordTrace (prefixWord ++ tailWord_8278828) baseStart_8278828 baseEnd_8278828 := by
    simpa [prefixWord, tailWord_8278828, baseEnd_8278828] using wordTrace_append hprefix tailTrace_8278828
  have hstable : (prefixWord ++ tailWord_8278828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278828).length < 2 ^ (prefixWord ++ tailWord_8278828).sum := by decide
  have hdescent : baseEnd_8278828 < baseStart_8278828 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278865 : List Nat := [1, 2, 2, 1, 6, 1, 2, 2, 1, 5]
def baseStart_8278865 : Nat := 118140960795 + 8278865 * 2 ^ 59
def prefixEnd_8278865 : Nat := 4983230072969 + 3 ^ 40 * 8278865 * 2
def baseEnd_8278865 : Nat := 1417012339561618878771233

theorem tailTrace_8278865 : CollatzResearch.WordTrace tailWord_8278865 prefixEnd_8278865 1417012339561618878771233 := by
  unfold tailWord_8278865
  simp only [CollatzResearch.WordTrace]
  refine ⟨301955013152093497419382049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201303342101395664946254699 301955013152093497419382049)
  ·
    refine ⟨226466259864070123064536537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301955013152093497419382049 226466259864070123064536537)
    ·
      refine ⟨169849694898052592298402403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226466259864070123064536537 169849694898052592298402403)
      ·
        refine ⟨254774542347078888447603605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169849694898052592298402403 254774542347078888447603605)
        ·
          refine ⟨11942556672519322895981419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 254774542347078888447603605 11942556672519322895981419)
          ·
            refine ⟨17913835008778984343972129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11942556672519322895981419 17913835008778984343972129)
            ·
              refine ⟨13435376256584238257979097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17913835008778984343972129 13435376256584238257979097)
              ·
                refine ⟨10076532192438178693484323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13435376256584238257979097 10076532192438178693484323)
                ·
                  refine ⟨15114798288657268040226485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10076532192438178693484323 15114798288657268040226485)
                  ·
                    refine ⟨1417012339561618878771233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15114798288657268040226485 1417012339561618878771233)
                    ·
                      rfl

theorem cell23_8278865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 5].length) (baseStart_8278865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278865 prefixEnd_8278865 := by exact prefixLift 8278865
  have htrace : WordTrace (prefixWord ++ tailWord_8278865) baseStart_8278865 baseEnd_8278865 := by
    simpa [prefixWord, tailWord_8278865, baseEnd_8278865] using wordTrace_append hprefix tailTrace_8278865
  have hstable : (prefixWord ++ tailWord_8278865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278865).length < 2 ^ (prefixWord ++ tailWord_8278865).sum := by decide
  have hdescent : baseEnd_8278865 < baseStart_8278865 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278885 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 5, 2, 2]
def baseStart_8278885 : Nat := 118140960795 + 8278885 * 2 ^ 59
def prefixEnd_8278885 : Nat := 4983230072969 + 3 ^ 40 * 8278885 * 2
def baseEnd_8278885 : Nat := 4251047288297946558063607

theorem tailTrace_8278885 : CollatzResearch.WordTrace tailWord_8278885 prefixEnd_8278885 4251047288297946558063607 := by
  unfold tailWord_8278885
  simp only [CollatzResearch.WordTrace]
  refine ⟨301955742612021040835110109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201303828408014027223406739 301955742612021040835110109)
  ·
    refine ⟨113233403479507890313166291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301955742612021040835110109 113233403479507890313166291)
    ·
      refine ⟨169850105219261835469749437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113233403479507890313166291 169850105219261835469749437)
      ·
        refine ⟨63693789457223188301156039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169850105219261835469749437 63693789457223188301156039)
        ·
          refine ⟨95540684185834782451734059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63693789457223188301156039 95540684185834782451734059)
          ·
            refine ⟨143311026278752173677601089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95540684185834782451734059 143311026278752173677601089)
            ·
              refine ⟨107483269709064130258200817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143311026278752173677601089 107483269709064130258200817)
              ·
                refine ⟨80612452281798097693650613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107483269709064130258200817 80612452281798097693650613)
                ·
                  refine ⟨7557417401418571658779745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80612452281798097693650613 7557417401418571658779745)
                  ·
                    refine ⟨5668063051063928744084809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7557417401418571658779745 5668063051063928744084809)
                    ·
                      refine ⟨4251047288297946558063607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5668063051063928744084809 4251047288297946558063607)
                      ·
                        rfl

theorem cell23_8278885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_8278885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278885 prefixEnd_8278885 := by exact prefixLift 8278885
  have htrace : WordTrace (prefixWord ++ tailWord_8278885) baseStart_8278885 baseEnd_8278885 := by
    simpa [prefixWord, tailWord_8278885, baseEnd_8278885] using wordTrace_append hprefix tailTrace_8278885
  have hstable : (prefixWord ++ tailWord_8278885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278885).length < 2 ^ (prefixWord ++ tailWord_8278885).sum := by decide
  have hdescent : baseEnd_8278885 < baseStart_8278885 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278888 : List Nat := [2, 1, 4, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_8278888 : Nat := 118140960795 + 8278888 * 2 ^ 59
def prefixEnd_8278888 : Nat := 4983230072969 + 3 ^ 40 * 8278888 * 2
def baseEnd_8278888 : Nat := 4251048828739910046326093

theorem tailTrace_8278888 : CollatzResearch.WordTrace tailWord_8278888 prefixEnd_8278888 4251048828739910046326093 := by
  unfold tailWord_8278888
  simp only [CollatzResearch.WordTrace]
  refine ⟨150977926015505086173734659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201303901354006781564979545 150977926015505086173734659)
  ·
    refine ⟨226466889023257629260601989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150977926015505086173734659 226466889023257629260601989)
    ·
      refine ⟨42462541691860805486362873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226466889023257629260601989 42462541691860805486362873)
      ·
        refine ⟨31846906268895604114772155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42462541691860805486362873 31846906268895604114772155)
        ·
          refine ⟨47770359403343406172158233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31846906268895604114772155 47770359403343406172158233)
          ·
            refine ⟨35827769552507554629118675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47770359403343406172158233 35827769552507554629118675)
            ·
              refine ⟨53741654328761331943678013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35827769552507554629118675 53741654328761331943678013)
              ·
                refine ⟨20153120373285499478879255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53741654328761331943678013 20153120373285499478879255)
                ·
                  refine ⟨30229680559928249218318883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20153120373285499478879255 30229680559928249218318883)
                  ·
                    refine ⟨45344520839892373827478325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30229680559928249218318883 45344520839892373827478325)
                    ·
                      refine ⟨4251048828739910046326093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45344520839892373827478325 4251048828739910046326093)
                      ·
                        rfl

theorem cell23_8278888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_8278888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278888 prefixEnd_8278888 := by exact prefixLift 8278888
  have htrace : WordTrace (prefixWord ++ tailWord_8278888) baseStart_8278888 baseEnd_8278888 := by
    simpa [prefixWord, tailWord_8278888, baseEnd_8278888] using wordTrace_append hprefix tailTrace_8278888
  have hstable : (prefixWord ++ tailWord_8278888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278888).length < 2 ^ (prefixWord ++ tailWord_8278888).sum := by decide
  have hdescent : baseEnd_8278888 < baseStart_8278888 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278922 : List Nat := [3, 1, 2, 4, 1, 1, 3, 2, 1, 2, 3]
def baseStart_8278922 : Nat := 118140960795 + 8278922 * 2 ^ 59
def prefixEnd_8278922 : Nat := 4983230072969 + 3 ^ 40 * 8278922 * 2
def baseEnd_8278922 : Nat := 4251066287082162913300937

theorem tailTrace_8278922 : CollatzResearch.WordTrace tailWord_8278922 prefixEnd_8278922 4251066287082162913300937 := by
  unfold tailWord_8278922
  simp only [CollatzResearch.WordTrace]
  refine ⟨75489273028221749038551755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201304728075257997436138013 75489273028221749038551755)
  ·
    refine ⟨113233909542332623557827633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75489273028221749038551755 113233909542332623557827633)
    ·
      refine ⟨84925432156749467668370725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113233909542332623557827633 84925432156749467668370725)
      ·
        refine ⟨15923518529390525187819511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84925432156749467668370725 15923518529390525187819511)
        ·
          refine ⟨23885277794085787781729267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15923518529390525187819511 23885277794085787781729267)
          ·
            refine ⟨35827916691128681672593901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23885277794085787781729267 35827916691128681672593901)
            ·
              refine ⟨13435468759173255627222713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35827916691128681672593901 13435468759173255627222713)
              ·
                refine ⟨10076601569379941720417035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13435468759173255627222713 10076601569379941720417035)
                ·
                  refine ⟨15114902354069912580625553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10076601569379941720417035 15114902354069912580625553)
                  ·
                    refine ⟨11336176765552434435469165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15114902354069912580625553 11336176765552434435469165)
                    ·
                      refine ⟨4251066287082162913300937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11336176765552434435469165 4251066287082162913300937)
                      ·
                        rfl

theorem cell23_8278922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_8278922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278922 prefixEnd_8278922 := by exact prefixLift 8278922
  have htrace : WordTrace (prefixWord ++ tailWord_8278922) baseStart_8278922 baseEnd_8278922 := by
    simpa [prefixWord, tailWord_8278922, baseEnd_8278922] using wordTrace_append hprefix tailTrace_8278922
  have hstable : (prefixWord ++ tailWord_8278922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278922).length < 2 ^ (prefixWord ++ tailWord_8278922).sum := by decide
  have hdescent : baseEnd_8278922 < baseStart_8278922 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278931 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 5]
def baseStart_8278931 : Nat := 118140960795 + 8278931 * 2 ^ 59
def prefixEnd_8278931 : Nat := 4983230072969 + 3 ^ 40 * 8278931 * 2
def baseEnd_8278931 : Nat := 4251070908408053378088395

theorem tailTrace_8278931 : CollatzResearch.WordTrace tailWord_8278931 prefixEnd_8278931 4251070908408053378088395 := by
  unfold tailWord_8278931
  simp only [CollatzResearch.WordTrace]
  refine ⟨301957420369854390691284647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201304946913236260460856431 301957420369854390691284647)
  ·
    refine ⟨452936130554781586036926971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301957420369854390691284647 452936130554781586036926971)
    ·
      refine ⟨679404195832172379055390457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452936130554781586036926971 679404195832172379055390457)
      ·
        refine ⟨509553146874129284291542843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 679404195832172379055390457 509553146874129284291542843)
        ·
          refine ⟨764329720311193926437314265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509553146874129284291542843 764329720311193926437314265)
          ·
            refine ⟨573247290233395444827985699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 764329720311193926437314265 573247290233395444827985699)
            ·
              refine ⟨859870935350093167241978549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573247290233395444827985699 859870935350093167241978549)
              ·
                refine ⟨80612900189071234428935489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 859870935350093167241978549 80612900189071234428935489)
                ·
                  refine ⟨60459675141803425821701617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80612900189071234428935489 60459675141803425821701617)
                  ·
                    refine ⟨45344756356352569366276213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60459675141803425821701617 45344756356352569366276213)
                    ·
                      refine ⟨4251070908408053378088395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45344756356352569366276213 4251070908408053378088395)
                      ·
                        rfl

theorem cell23_8278931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 5].length) (baseStart_8278931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278931 prefixEnd_8278931 := by exact prefixLift 8278931
  have htrace : WordTrace (prefixWord ++ tailWord_8278931) baseStart_8278931 baseEnd_8278931 := by
    simpa [prefixWord, tailWord_8278931, baseEnd_8278931] using wordTrace_append hprefix tailTrace_8278931
  have hstable : (prefixWord ++ tailWord_8278931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278931).length < 2 ^ (prefixWord ++ tailWord_8278931).sum := by decide
  have hdescent : baseEnd_8278931 < baseStart_8278931 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278966 : List Nat := [5, 1, 4, 1, 1, 1, 2, 1, 1, 2, 4]
def baseStart_8278966 : Nat := 118140960795 + 8278966 * 2 ^ 59
def prefixEnd_8278966 : Nat := 4983230072969 + 3 ^ 40 * 8278966 * 2
def baseEnd_8278966 : Nat := 4251088880230960741150735

theorem tailTrace_8278966 : CollatzResearch.WordTrace tailWord_8278966 prefixEnd_8278966 4251088880230960741150735 := by
  unfold tailWord_8278966
  simp only [CollatzResearch.WordTrace]
  refine ⟨18872418557795474479300547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201305797949818394445872501 18872418557795474479300547)
  ·
    refine ⟨28308627836693211718950821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18872418557795474479300547 28308627836693211718950821)
    ·
      refine ⟨5307867719379977197303279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28308627836693211718950821 5307867719379977197303279)
      ·
        refine ⟨7961801579069965795954919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5307867719379977197303279 7961801579069965795954919)
        ·
          refine ⟨11942702368604948693932379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7961801579069965795954919 11942702368604948693932379)
          ·
            refine ⟨17914053552907423040898569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11942702368604948693932379 17914053552907423040898569)
            ·
              refine ⟨13435540164680567280673927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17914053552907423040898569 13435540164680567280673927)
              ·
                refine ⟨20153310247020850921010891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13435540164680567280673927 20153310247020850921010891)
                ·
                  refine ⟨30229965370531276381516337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20153310247020850921010891 30229965370531276381516337)
                  ·
                    refine ⟨22672474027898457286137253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30229965370531276381516337 22672474027898457286137253)
                    ·
                      refine ⟨4251088880230960741150735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22672474027898457286137253 4251088880230960741150735)
                      ·
                        rfl

theorem cell23_8278966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_8278966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278966 prefixEnd_8278966 := by exact prefixLift 8278966
  have htrace : WordTrace (prefixWord ++ tailWord_8278966) baseStart_8278966 baseEnd_8278966 := by
    simpa [prefixWord, tailWord_8278966, baseEnd_8278966] using wordTrace_append hprefix tailTrace_8278966
  have hstable : (prefixWord ++ tailWord_8278966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278966).length < 2 ^ (prefixWord ++ tailWord_8278966).sum := by decide
  have hdescent : baseEnd_8278966 < baseStart_8278966 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278968 : List Nat := [2, 1, 2, 1, 2, 5, 1, 1, 2, 6]
def baseStart_8278968 : Nat := 118140960795 + 8278968 * 2 ^ 59
def prefixEnd_8278968 : Nat := 4983230072969 + 3 ^ 40 * 8278968 * 2
def baseEnd_8278968 : Nat := 1417029969064089911108575

theorem tailTrace_8278968 : CollatzResearch.WordTrace tailWord_8278968 prefixEnd_8278968 1417029969064089911108575 := by
  unfold tailWord_8278968
  simp only [CollatzResearch.WordTrace]
  refine ⟨150979384935360173005190779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201305846580480230673587705 150979384935360173005190779)
  ·
    refine ⟨226469077403040259507786169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150979384935360173005190779 226469077403040259507786169)
    ·
      refine ⟨169851808052280194630839627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226469077403040259507786169 169851808052280194630839627)
      ·
        refine ⟨254777712078420291946259441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169851808052280194630839627 254777712078420291946259441)
        ·
          refine ⟨191083284058815218959694581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254777712078420291946259441 191083284058815218959694581)
          ·
            refine ⟨17914057880513926777471367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 191083284058815218959694581 17914057880513926777471367)
            ·
              refine ⟨26871086820770890166207051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17914057880513926777471367 26871086820770890166207051)
              ·
                refine ⟨40306630231156335249310577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26871086820770890166207051 40306630231156335249310577)
                ·
                  refine ⟨30229972673367251436982933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40306630231156335249310577 30229972673367251436982933)
                  ·
                    refine ⟨1417029969064089911108575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30229972673367251436982933 1417029969064089911108575)
                    ·
                      rfl

theorem cell23_8278968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 2, 6].length) (baseStart_8278968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278968 prefixEnd_8278968 := by exact prefixLift 8278968
  have htrace : WordTrace (prefixWord ++ tailWord_8278968) baseStart_8278968 baseEnd_8278968 := by
    simpa [prefixWord, tailWord_8278968, baseEnd_8278968] using wordTrace_append hprefix tailTrace_8278968
  have hstable : (prefixWord ++ tailWord_8278968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278968).length < 2 ^ (prefixWord ++ tailWord_8278968).sum := by decide
  have hdescent : baseEnd_8278968 < baseStart_8278968 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278988 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 1, 4, 4]
def baseStart_8278988 : Nat := 118140960795 + 8278988 * 2 ^ 59
def prefixEnd_8278988 : Nat := 4983230072969 + 3 ^ 40 * 8278988 * 2
def baseEnd_8278988 : Nat := 4251100176805359655075633

theorem tailTrace_8278988 : CollatzResearch.WordTrace tailWord_8278988 prefixEnd_8278988 4251100176805359655075633 := by
  unfold tailWord_8278988
  simp only [CollatzResearch.WordTrace]
  refine ⟨150979749665323944713054809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201306332887098592950739745 150979749665323944713054809)
  ·
    refine ⟨113234812248992958534791107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150979749665323944713054809 113234812248992958534791107)
    ·
      refine ⟨169852218373489437802186661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113234812248992958534791107 169852218373489437802186661)
      ·
        refine ⟨31847290945029269587909999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169852218373489437802186661 31847290945029269587909999)
        ·
          refine ⟨47770936417543904381864999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31847290945029269587909999 47770936417543904381864999)
          ·
            refine ⟨71656404626315856572797499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47770936417543904381864999 71656404626315856572797499)
            ·
              refine ⟨107484606939473784859196249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71656404626315856572797499 107484606939473784859196249)
              ·
                refine ⟨80613455204605338644397187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107484606939473784859196249 80613455204605338644397187)
                ·
                  refine ⟨120920182806908007966595781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80613455204605338644397187 120920182806908007966595781)
                  ·
                    refine ⟨22672534276295251493736709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120920182806908007966595781 22672534276295251493736709)
                    ·
                      refine ⟨4251100176805359655075633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22672534276295251493736709 4251100176805359655075633)
                      ·
                        rfl

theorem cell23_8278988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_8278988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278988 prefixEnd_8278988 := by exact prefixLift 8278988
  have htrace : WordTrace (prefixWord ++ tailWord_8278988) baseStart_8278988 baseEnd_8278988 := by
    simpa [prefixWord, tailWord_8278988, baseEnd_8278988] using wordTrace_append hprefix tailTrace_8278988
  have hstable : (prefixWord ++ tailWord_8278988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278988).length < 2 ^ (prefixWord ++ tailWord_8278988).sum := by decide
  have hdescent : baseEnd_8278988 < baseStart_8278988 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8278996 : List Nat := [2, 4, 1, 2, 1, 4, 2, 1, 1, 3, 2]
def baseStart_8278996 : Nat := 118140960795 + 8278996 * 2 ^ 59
def prefixEnd_8278996 : Nat := 4983230072969 + 3 ^ 40 * 8278996 * 2
def baseEnd_8278996 : Nat := 4251104284650595623775597

theorem tailTrace_8278996 : CollatzResearch.WordTrace tailWord_8278996 prefixEnd_8278996 4251104284650595623775597 := by
  unfold tailWord_8278996
  simp only [CollatzResearch.WordTrace]
  refine ⟨150979895557309453396200421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201306527409745937861600561 150979895557309453396200421)
  ·
    refine ⟨28308730416995522511787579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150979895557309453396200421 28308730416995522511787579)
    ·
      refine ⟨42463095625493283767681369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28308730416995522511787579 42463095625493283767681369)
      ·
        refine ⟨31847321719119962825761027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42463095625493283767681369 31847321719119962825761027)
        ·
          refine ⟨47770982578679944238641541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31847321719119962825761027 47770982578679944238641541)
          ·
            refine ⟨8957059233502489544745289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47770982578679944238641541 8957059233502489544745289)
            ·
              refine ⟨6717794425126867158558967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8957059233502489544745289 6717794425126867158558967)
              ·
                refine ⟨10076691637690300737838451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6717794425126867158558967 10076691637690300737838451)
                ·
                  refine ⟨15115037456535451106757677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10076691637690300737838451 15115037456535451106757677)
                  ·
                    refine ⟨5668139046200794165034129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15115037456535451106757677 5668139046200794165034129)
                    ·
                      refine ⟨4251104284650595623775597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5668139046200794165034129 4251104284650595623775597)
                      ·
                        rfl

theorem cell23_8278996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_8278996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8278996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8278996 prefixEnd_8278996 := by exact prefixLift 8278996
  have htrace : WordTrace (prefixWord ++ tailWord_8278996) baseStart_8278996 baseEnd_8278996 := by
    simpa [prefixWord, tailWord_8278996, baseEnd_8278996] using wordTrace_append hprefix tailTrace_8278996
  have hstable : (prefixWord ++ tailWord_8278996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8278996).length < 2 ^ (prefixWord ++ tailWord_8278996).sum := by decide
  have hdescent : baseEnd_8278996 < baseStart_8278996 := by decide
  rcases family_descends (prefixWord ++ tailWord_8278996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279005 : List Nat := [1, 4, 3, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_8279005 : Nat := 118140960795 + 8279005 * 2 ^ 59
def prefixEnd_8279005 : Nat := 4983230072969 + 3 ^ 40 * 8279005 * 2
def baseEnd_8279005 : Nat := 4251108905976486088563055

theorem tailTrace_8279005 : CollatzResearch.WordTrace tailWord_8279005 prefixEnd_8279005 4251108905976486088563055 := by
  unfold tailWord_8279005
  simp only [CollatzResearch.WordTrace]
  refine ⟨301960119371586301329478469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201306746247724200886318979 301960119371586301329478469)
  ·
    refine ⟨56617522382172431499277213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301960119371586301329478469 56617522382172431499277213)
    ·
      refine ⟨21231570893314661812228955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56617522382172431499277213 21231570893314661812228955)
      ·
        refine ⟨31847356339971992718343433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21231570893314661812228955 31847356339971992718343433)
        ·
          refine ⟨23885517254978994538757575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31847356339971992718343433 23885517254978994538757575)
          ·
            refine ⟨35828275882468491808136363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23885517254978994538757575 35828275882468491808136363)
            ·
              refine ⟨53742413823702737712204545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35828275882468491808136363 53742413823702737712204545)
              ·
                refine ⟨40306810367777053284153409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53742413823702737712204545 40306810367777053284153409)
                ·
                  refine ⟨30230107775832789963115057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40306810367777053284153409 30230107775832789963115057)
                  ·
                    refine ⟨22672580831874592472336293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30230107775832789963115057 22672580831874592472336293)
                    ·
                      refine ⟨4251108905976486088563055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22672580831874592472336293 4251108905976486088563055)
                      ·
                        rfl

theorem cell23_8279005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_8279005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279005 prefixEnd_8279005 := by exact prefixLift 8279005
  have htrace : WordTrace (prefixWord ++ tailWord_8279005) baseStart_8279005 baseEnd_8279005 := by
    simpa [prefixWord, tailWord_8279005, baseEnd_8279005] using wordTrace_append hprefix tailTrace_8279005
  have hstable : (prefixWord ++ tailWord_8279005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279005).length < 2 ^ (prefixWord ++ tailWord_8279005).sum := by decide
  have hdescent : baseEnd_8279005 < baseStart_8279005 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279015 : List Nat := [1, 1, 5, 2, 2, 2, 2, 1, 7]
def baseStart_8279015 : Nat := 118140960795 + 8279015 * 2 ^ 59
def prefixEnd_8279015 : Nat := 4983230072969 + 3 ^ 40 * 8279015 * 2
def baseEnd_8279015 : Nat := 472346004531447894382001

theorem tailTrace_8279015 : CollatzResearch.WordTrace tailWord_8279015 prefixEnd_8279015 472346004531447894382001 := by
  unfold tailWord_8279015
  simp only [CollatzResearch.WordTrace]
  refine ⟨301960484101550073037342499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201306989401033382024894999 301960484101550073037342499)
  ·
    refine ⟨452940726152325109556013749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301960484101550073037342499 452940726152325109556013749)
    ·
      refine ⟨42463193076780479020876289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 452940726152325109556013749 42463193076780479020876289)
      ·
        refine ⟨31847394807585359265657217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42463193076780479020876289 31847394807585359265657217)
        ·
          refine ⟨23885546105689019449242913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31847394807585359265657217 23885546105689019449242913)
          ·
            refine ⟨17914159579266764586932185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23885546105689019449242913 17914159579266764586932185)
            ·
              refine ⟨13435619684450073440199139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17914159579266764586932185 13435619684450073440199139)
              ·
                refine ⟨20153429526675110160298709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13435619684450073440199139 20153429526675110160298709)
                ·
                  refine ⟨472346004531447894382001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20153429526675110160298709 472346004531447894382001)
                  ·
                    rfl

theorem cell23_8279015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 7].length) (baseStart_8279015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279015 prefixEnd_8279015 := by exact prefixLift 8279015
  have htrace : WordTrace (prefixWord ++ tailWord_8279015) baseStart_8279015 baseEnd_8279015 := by
    simpa [prefixWord, tailWord_8279015, baseEnd_8279015] using wordTrace_append hprefix tailTrace_8279015
  have hstable : (prefixWord ++ tailWord_8279015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279015).length < 2 ^ (prefixWord ++ tailWord_8279015).sum := by decide
  have hdescent : baseEnd_8279015 < baseStart_8279015 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279025 : List Nat := [1, 2, 2, 2, 4, 1, 2, 1, 2, 3, 3]
def baseStart_8279025 : Nat := 118140960795 + 8279025 * 2 ^ 59
def prefixEnd_8279025 : Nat := 4983230072969 + 3 ^ 40 * 8279025 * 2
def baseEnd_8279025 : Nat := 4251119175589576010312963

theorem tailTrace_8279025 : CollatzResearch.WordTrace tailWord_8279025 prefixEnd_8279025 4251119175589576010312963 := by
  unfold tailWord_8279025
  simp only [CollatzResearch.WordTrace]
  refine ⟨301960848831513844745206529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201307232554342563163471019 301960848831513844745206529)
  ·
    refine ⟨226470636623635383558904897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301960848831513844745206529 226470636623635383558904897)
    ·
      refine ⟨169852977467726537669178673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226470636623635383558904897 169852977467726537669178673)
      ·
        refine ⟨127389733100794903251884005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169852977467726537669178673 127389733100794903251884005)
        ·
          refine ⟨23885574956399044359728251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127389733100794903251884005 23885574956399044359728251)
          ·
            refine ⟨35828362434598566539592377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23885574956399044359728251 35828362434598566539592377)
            ·
              refine ⟨26871271825948924904694283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35828362434598566539592377 26871271825948924904694283)
              ·
                refine ⟨40306907738923387357041425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26871271825948924904694283 40306907738923387357041425)
                ·
                  refine ⟨30230180804192540517781069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40306907738923387357041425 30230180804192540517781069)
                  ·
                    refine ⟨11336317801572202694167901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30230180804192540517781069 11336317801572202694167901)
                    ·
                      refine ⟨4251119175589576010312963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11336317801572202694167901 4251119175589576010312963)
                      ·
                        rfl

theorem cell23_8279025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_8279025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279025 prefixEnd_8279025 := by exact prefixLift 8279025
  have htrace : WordTrace (prefixWord ++ tailWord_8279025) baseStart_8279025 baseEnd_8279025 := by
    simpa [prefixWord, tailWord_8279025, baseEnd_8279025] using wordTrace_append hprefix tailTrace_8279025
  have hstable : (prefixWord ++ tailWord_8279025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279025).length < 2 ^ (prefixWord ++ tailWord_8279025).sum := by decide
  have hdescent : baseEnd_8279025 < baseStart_8279025 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279026 : List Nat := [3, 2, 1, 5, 1, 2, 1, 1, 1, 4, 2]
def baseStart_8279026 : Nat := 118140960795 + 8279026 * 2 ^ 59
def prefixEnd_8279026 : Nat := 4983230072969 + 3 ^ 40 * 8279026 * 2
def baseEnd_8279026 : Nat := 4251119689070230506400459

theorem tailTrace_8279026 : CollatzResearch.WordTrace tailWord_8279026 prefixEnd_8279026 4251119689070230506400459 := by
  unfold tailWord_8279026
  simp only [CollatzResearch.WordTrace]
  refine ⟨75490221326127555478998233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201307256869673481277328621 75490221326127555478998233)
  ·
    refine ⟨56617665994595666609248675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75490221326127555478998233 56617665994595666609248675)
    ·
      refine ⟨84926498991893499913873013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56617665994595666609248675 84926498991893499913873013)
      ·
        refine ⟨7961859280490015616925595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84926498991893499913873013 7961859280490015616925595)
        ·
          refine ⟨11942788920735023425388393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7961859280490015616925595 11942788920735023425388393)
          ·
            refine ⟨8957091690551267569041295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11942788920735023425388393 8957091690551267569041295)
            ·
              refine ⟨13435637535826901353561943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8957091690551267569041295 13435637535826901353561943)
              ·
                refine ⟨20153456303740352030342915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13435637535826901353561943 20153456303740352030342915)
                ·
                  refine ⟨30230184455610528045514373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20153456303740352030342915 30230184455610528045514373)
                  ·
                    refine ⟨5668159585426974008533945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30230184455610528045514373 5668159585426974008533945)
                    ·
                      refine ⟨4251119689070230506400459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5668159585426974008533945 4251119689070230506400459)
                      ·
                        rfl

theorem cell23_8279026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_8279026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279026 prefixEnd_8279026 := by exact prefixLift 8279026
  have htrace : WordTrace (prefixWord ++ tailWord_8279026) baseStart_8279026 baseEnd_8279026 := by
    simpa [prefixWord, tailWord_8279026, baseEnd_8279026] using wordTrace_append hprefix tailTrace_8279026
  have hstable : (prefixWord ++ tailWord_8279026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279026).length < 2 ^ (prefixWord ++ tailWord_8279026).sum := by decide
  have hdescent : baseEnd_8279026 < baseStart_8279026 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279065 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 4, 4, 2]
def baseStart_8279065 : Nat := 118140960795 + 8279065 * 2 ^ 59
def prefixEnd_8279065 : Nat := 4983230072969 + 3 ^ 40 * 8279065 * 2
def baseEnd_8279065 : Nat := 4251139714815755853812779

theorem tailTrace_8279065 : CollatzResearch.WordTrace tailWord_8279065 prefixEnd_8279065 4251139714815755853812779 := by
  unfold tailWord_8279065
  simp only [CollatzResearch.WordTrace]
  refine ⟨301962307751368931576662649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201308205167579287717775099 301962307751368931576662649)
  ·
    refine ⟨226471730813526698682496987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301962307751368931576662649 226471730813526698682496987)
    ·
      refine ⟨339707596220290048023745481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226471730813526698682496987 339707596220290048023745481)
      ·
        refine ⟨254780697165217536017809111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339707596220290048023745481 254780697165217536017809111)
        ·
          refine ⟨382171045747826304026713667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254780697165217536017809111 382171045747826304026713667)
          ·
            refine ⟨573256568621739456040070501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382171045747826304026713667 573256568621739456040070501)
            ·
              refine ⟨107485606616576148007513219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 573256568621739456040070501 107485606616576148007513219)
              ·
                refine ⟨161228409924864222011269829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107485606616576148007513219 161228409924864222011269829)
                ·
                  refine ⟨30230326860912041627113093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161228409924864222011269829 30230326860912041627113093)
                  ·
                    refine ⟨5668186286421007805083705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30230326860912041627113093 5668186286421007805083705)
                    ·
                      refine ⟨4251139714815755853812779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5668186286421007805083705 4251139714815755853812779)
                      ·
                        rfl

theorem cell23_8279065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 4, 2].length) (baseStart_8279065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279065 prefixEnd_8279065 := by exact prefixLift 8279065
  have htrace : WordTrace (prefixWord ++ tailWord_8279065) baseStart_8279065 baseEnd_8279065 := by
    simpa [prefixWord, tailWord_8279065, baseEnd_8279065] using wordTrace_append hprefix tailTrace_8279065
  have hstable : (prefixWord ++ tailWord_8279065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279065).length < 2 ^ (prefixWord ++ tailWord_8279065).sum := by decide
  have hdescent : baseEnd_8279065 < baseStart_8279065 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279072 : List Nat := [2, 1, 1, 7, 1, 1, 1, 1, 1, 2, 5]
def baseStart_8279072 : Nat := 118140960795 + 8279072 * 2 ^ 59
def prefixEnd_8279072 : Nat := 4983230072969 + 3 ^ 40 * 8279072 * 2
def baseEnd_8279072 : Nat := 4251143309180337326425247

theorem tailTrace_8279072 : CollatzResearch.WordTrace tailWord_8279072 prefixEnd_8279072 4251143309180337326425247 := by
  unfold tailWord_8279072
  simp only [CollatzResearch.WordTrace]
  refine ⟨150981281531171785886083735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201308375374895714514778313 150981281531171785886083735)
  ·
    refine ⟨226471922296757678829125603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150981281531171785886083735 226471922296757678829125603)
    ·
      refine ⟨339707883445136518243688405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226471922296757678829125603 339707883445136518243688405)
      ·
        refine ⟨7961903518245387146336447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 339707883445136518243688405 7961903518245387146336447)
        ·
          refine ⟨11942855277368080719504671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7961903518245387146336447 11942855277368080719504671)
          ·
            refine ⟨17914282916052121079257007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11942855277368080719504671 17914282916052121079257007)
            ·
              refine ⟨26871424374078181618885511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17914282916052121079257007 26871424374078181618885511)
              ·
                refine ⟨40307136561117272428328267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26871424374078181618885511 40307136561117272428328267)
                ·
                  refine ⟨60460704841675908642492401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40307136561117272428328267 60460704841675908642492401)
                  ·
                    refine ⟨45345528631256931481869301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60460704841675908642492401 45345528631256931481869301)
                    ·
                      refine ⟨4251143309180337326425247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45345528631256931481869301 4251143309180337326425247)
                      ·
                        rfl

theorem cell23_8279072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_8279072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279072 prefixEnd_8279072 := by exact prefixLift 8279072
  have htrace : WordTrace (prefixWord ++ tailWord_8279072) baseStart_8279072 baseEnd_8279072 := by
    simpa [prefixWord, tailWord_8279072, baseEnd_8279072] using wordTrace_append hprefix tailTrace_8279072
  have hstable : (prefixWord ++ tailWord_8279072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279072).length < 2 ^ (prefixWord ++ tailWord_8279072).sum := by decide
  have hdescent : baseEnd_8279072 < baseStart_8279072 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279122 : List Nat := [3, 2, 2, 1, 3, 2, 2, 2, 6]
def baseStart_8279122 : Nat := 118140960795 + 8279122 * 2 ^ 59
def prefixEnd_8279122 : Nat := 4983230072969 + 3 ^ 40 * 8279122 * 2
def baseEnd_8279122 : Nat := 472352109245895792311113

theorem tailTrace_8279122 : CollatzResearch.WordTrace tailWord_8279122 prefixEnd_8279122 472352109245895792311113 := by
  unfold tailWord_8279122
  simp only [CollatzResearch.WordTrace]
  refine ⟨75491096678040607577871905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201309591141441620207658413 75491096678040607577871905)
  ·
    refine ⟨56618322508530455683403929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75491096678040607577871905 56618322508530455683403929)
    ·
      refine ⟨42463741881397841762552947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56618322508530455683403929 42463741881397841762552947)
      ·
        refine ⟨63695612822096762643829421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42463741881397841762552947 63695612822096762643829421)
        ·
          refine ⟨23885854808286285991436033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63695612822096762643829421 23885854808286285991436033)
          ·
            refine ⟨17914391106214714493577025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23885854808286285991436033 17914391106214714493577025)
            ·
              refine ⟨13435793329661035870182769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17914391106214714493577025 13435793329661035870182769)
              ·
                refine ⟨10076844997245776902637077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13435793329661035870182769 10076844997245776902637077)
                ·
                  refine ⟨472352109245895792311113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10076844997245776902637077 472352109245895792311113)
                  ·
                    rfl

theorem cell23_8279122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 6].length) (baseStart_8279122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279122 prefixEnd_8279122 := by exact prefixLift 8279122
  have htrace : WordTrace (prefixWord ++ tailWord_8279122) baseStart_8279122 baseEnd_8279122 := by
    simpa [prefixWord, tailWord_8279122, baseEnd_8279122] using wordTrace_append hprefix tailTrace_8279122
  have hstable : (prefixWord ++ tailWord_8279122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279122).length < 2 ^ (prefixWord ++ tailWord_8279122).sum := by decide
  have hdescent : baseEnd_8279122 < baseStart_8279122 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279149 : List Nat := [1, 5, 1, 1, 2, 3, 1, 2, 3, 1, 3]
def baseStart_8279149 : Nat := 118140960795 + 8279149 * 2 ^ 59
def prefixEnd_8279149 : Nat := 4983230072969 + 3 ^ 40 * 8279149 * 2
def baseEnd_8279149 : Nat := 4251182847190733525162393

theorem tailTrace_8279149 : CollatzResearch.WordTrace tailWord_8279149 prefixEnd_8279149 4251182847190733525162393 := by
  unfold tailWord_8279149
  simp only [CollatzResearch.WordTrace]
  refine ⟨301965371483064613922720501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201310247655376409281813667 301965371483064613922720501)
  ·
    refine ⟨28309253576537307555255047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 301965371483064613922720501 28309253576537307555255047)
    ·
      refine ⟨42463880364805961332882571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28309253576537307555255047 42463880364805961332882571)
      ·
        refine ⟨63695820547208941999323857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42463880364805961332882571 63695820547208941999323857)
        ·
          refine ⟨47771865410406706499492893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63695820547208941999323857 47771865410406706499492893)
          ·
            refine ⟨17914449528902514937309835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47771865410406706499492893 17914449528902514937309835)
            ·
              refine ⟨26871674293353772405964753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17914449528902514937309835 26871674293353772405964753)
              ·
                refine ⟨20153755720015329304473565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26871674293353772405964753 20153755720015329304473565)
                ·
                  refine ⟨7557658395005748489177587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20153755720015329304473565 7557658395005748489177587)
                  ·
                    refine ⟨11336487592508622733766381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7557658395005748489177587 11336487592508622733766381)
                    ·
                      refine ⟨4251182847190733525162393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11336487592508622733766381 4251182847190733525162393)
                      ·
                        rfl

theorem cell23_8279149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_8279149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279149 prefixEnd_8279149 := by exact prefixLift 8279149
  have htrace : WordTrace (prefixWord ++ tailWord_8279149) baseStart_8279149 baseEnd_8279149 := by
    simpa [prefixWord, tailWord_8279149, baseEnd_8279149] using wordTrace_append hprefix tailTrace_8279149
  have hstable : (prefixWord ++ tailWord_8279149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279149).length < 2 ^ (prefixWord ++ tailWord_8279149).sum := by decide
  have hdescent : baseEnd_8279149 < baseStart_8279149 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279165 : List Nat := [1, 4, 1, 1, 3, 1, 1, 4, 1, 6]
def baseStart_8279165 : Nat := 118140960795 + 8279165 * 2 ^ 59
def prefixEnd_8279165 : Nat := 4983230072969 + 3 ^ 40 * 8279165 * 2
def baseEnd_8279165 : Nat := 1417063687627068487520773

theorem tailTrace_8279165 : CollatzResearch.WordTrace tailWord_8279165 prefixEnd_8279165 1417063687627068487520773 := by
  unfold tailWord_8279165
  simp only [CollatzResearch.WordTrace]
  refine ⟨301965955051006648655302949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201310636700671099103535299 301965955051006648655302949)
  ·
    refine ⟨56618616572063746622869303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301965955051006648655302949 56618616572063746622869303)
    ·
      refine ⟨84927924858095619934303955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56618616572063746622869303 84927924858095619934303955)
      ·
        refine ⟨127391887287143429901455933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84927924858095619934303955 127391887287143429901455933)
        ·
          refine ⟨47771957732678786213045975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127391887287143429901455933 47771957732678786213045975)
          ·
            refine ⟨71657936599018179319568963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47771957732678786213045975 71657936599018179319568963)
            ·
              refine ⟨107486904898527268979353445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71657936599018179319568963 107486904898527268979353445)
              ·
                refine ⟨20153794668473862933628771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107486904898527268979353445 20153794668473862933628771)
                ·
                  refine ⟨30230692002710794400443157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20153794668473862933628771 30230692002710794400443157)
                  ·
                    refine ⟨1417063687627068487520773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30230692002710794400443157 1417063687627068487520773)
                    ·
                      rfl

theorem cell23_8279165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_8279165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279165 prefixEnd_8279165 := by exact prefixLift 8279165
  have htrace : WordTrace (prefixWord ++ tailWord_8279165) baseStart_8279165 baseEnd_8279165 := by
    simpa [prefixWord, tailWord_8279165, baseEnd_8279165] using wordTrace_append hprefix tailTrace_8279165
  have hstable : (prefixWord ++ tailWord_8279165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279165).length < 2 ^ (prefixWord ++ tailWord_8279165).sum := by decide
  have hdescent : baseEnd_8279165 < baseStart_8279165 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279169 : List Nat := [1, 2, 4, 2, 2, 1, 4, 1, 1, 5]
def baseStart_8279169 : Nat := 118140960795 + 8279169 * 2 ^ 59
def prefixEnd_8279169 : Nat := 4983230072969 + 3 ^ 40 * 8279169 * 2
def baseEnd_8279169 : Nat := 1417064372267941148970767

theorem tailTrace_8279169 : CollatzResearch.WordTrace tailWord_8279169 prefixEnd_8279169 1417064372267941148970767 := by
  unfold tailWord_8279169
  simp only [CollatzResearch.WordTrace]
  refine ⟨301966100942992157338448561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201310733961994771558965707 301966100942992157338448561)
  ·
    refine ⟨226474575707244118003836421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301966100942992157338448561 226474575707244118003836421)
    ·
      refine ⟨42463982945108272125719329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226474575707244118003836421 42463982945108272125719329)
      ·
        refine ⟨31847987208831204094289497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42463982945108272125719329 31847987208831204094289497)
        ·
          refine ⟨23885990406623403070717123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31847987208831204094289497 23885990406623403070717123)
          ·
            refine ⟨35828985609935104606075685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23885990406623403070717123 35828985609935104606075685)
            ·
              refine ⟨6717934801862832113639191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35828985609935104606075685 6717934801862832113639191)
              ·
                refine ⟨10076902202794248170458787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6717934801862832113639191 10076902202794248170458787)
                ·
                  refine ⟨15115353304191372255688181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10076902202794248170458787 15115353304191372255688181)
                  ·
                    refine ⟨1417064372267941148970767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15115353304191372255688181 1417064372267941148970767)
                    ·
                      rfl

theorem cell23_8279169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_8279169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279169 prefixEnd_8279169 := by exact prefixLift 8279169
  have htrace : WordTrace (prefixWord ++ tailWord_8279169) baseStart_8279169 baseEnd_8279169 := by
    simpa [prefixWord, tailWord_8279169, baseEnd_8279169] using wordTrace_append hprefix tailTrace_8279169
  have hstable : (prefixWord ++ tailWord_8279169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279169).length < 2 ^ (prefixWord ++ tailWord_8279169).sum := by decide
  have hdescent : baseEnd_8279169 < baseStart_8279169 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279175 : List Nat := [1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 5]
def baseStart_8279175 : Nat := 118140960795 + 8279175 * 2 ^ 59
def prefixEnd_8279175 : Nat := 4983230072969 + 3 ^ 40 * 8279175 * 2
def baseEnd_8279175 : Nat := 4251196197687750423437273

theorem tailTrace_8279175 : CollatzResearch.WordTrace tailWord_8279175 prefixEnd_8279175 4251196197687750423437273 := by
  unfold tailWord_8279175
  simp only [CollatzResearch.WordTrace]
  refine ⟨301966319780970420363166979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201310879853980280242111319 301966319780970420363166979)
  ·
    refine ⟨452949479671455630544750469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301966319780970420363166979 452949479671455630544750469)
    ·
      refine ⟨84928027438397930727140713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 452949479671455630544750469 84928027438397930727140713)
      ·
        refine ⟨63696020578798448045355535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84928027438397930727140713 63696020578798448045355535)
        ·
          refine ⟨95544030868197672068033303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63696020578798448045355535 95544030868197672068033303)
          ·
            refine ⟨143316046302296508102049955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95544030868197672068033303 143316046302296508102049955)
            ·
              refine ⟨214974069453444762153074933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143316046302296508102049955 214974069453444762153074933)
              ·
                refine ⟨20153819011260446451850775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 214974069453444762153074933 20153819011260446451850775)
                ·
                  refine ⟨30230728516890669677776163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20153819011260446451850775 30230728516890669677776163)
                  ·
                    refine ⟨45346092775336004516664245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30230728516890669677776163 45346092775336004516664245)
                    ·
                      refine ⟨4251196197687750423437273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45346092775336004516664245 4251196197687750423437273)
                      ·
                        rfl

theorem cell23_8279175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_8279175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279175 prefixEnd_8279175 := by exact prefixLift 8279175
  have htrace : WordTrace (prefixWord ++ tailWord_8279175) baseStart_8279175 baseEnd_8279175 := by
    simpa [prefixWord, tailWord_8279175, baseEnd_8279175] using wordTrace_append hprefix tailTrace_8279175
  have hstable : (prefixWord ++ tailWord_8279175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279175).length < 2 ^ (prefixWord ++ tailWord_8279175).sum := by decide
  have hdescent : baseEnd_8279175 < baseStart_8279175 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279192 : List Nat := [2, 1, 2, 4, 2, 2, 1, 2, 1, 1, 5]
def baseStart_8279192 : Nat := 118140960795 + 8279192 * 2 ^ 59
def prefixEnd_8279192 : Nat := 4983230072969 + 3 ^ 40 * 8279192 * 2
def baseEnd_8279192 : Nat := 4251204926858876856924695

theorem tailTrace_8279192 : CollatzResearch.WordTrace tailWord_8279192 prefixEnd_8279192 4251204926858876856924695 := by
  unfold tailWord_8279192
  simp only [CollatzResearch.WordTrace]
  refine ⟨150983469910954416133267915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201311293214605888177690553 150983469910954416133267915)
  ·
    refine ⟨226475204866431624199901873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150983469910954416133267915 226475204866431624199901873)
    ·
      refine ⟨169856403649823718149926405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226475204866431624199901873 169856403649823718149926405)
      ·
        refine ⟨31848075684341947153111201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169856403649823718149926405 31848075684341947153111201)
        ·
          refine ⟨23886056763256460364833401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31848075684341947153111201 23886056763256460364833401)
          ·
            refine ⟨17914542572442345273625051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23886056763256460364833401 17914542572442345273625051)
            ·
              refine ⟨26871813858663517910437577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17914542572442345273625051 26871813858663517910437577)
              ·
                refine ⟨20153860393997638432828183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26871813858663517910437577 20153860393997638432828183)
                ·
                  refine ⟨30230790590996457649242275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20153860393997638432828183 30230790590996457649242275)
                  ·
                    refine ⟨45346185886494686473863413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30230790590996457649242275 45346185886494686473863413)
                    ·
                      refine ⟨4251204926858876856924695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45346185886494686473863413 4251204926858876856924695)
                      ·
                        rfl

theorem cell23_8279192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_8279192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279192 prefixEnd_8279192 := by exact prefixLift 8279192
  have htrace : WordTrace (prefixWord ++ tailWord_8279192) baseStart_8279192 baseEnd_8279192 := by
    simpa [prefixWord, tailWord_8279192, baseEnd_8279192] using wordTrace_append hprefix tailTrace_8279192
  have hstable : (prefixWord ++ tailWord_8279192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279192).length < 2 ^ (prefixWord ++ tailWord_8279192).sum := by decide
  have hdescent : baseEnd_8279192 < baseStart_8279192 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279199 : List Nat := [1, 1, 2, 6, 2, 2, 1, 1, 1, 6]
def baseStart_8279199 : Nat := 118140960795 + 8279199 * 2 ^ 59
def prefixEnd_8279199 : Nat := 4983230072969 + 3 ^ 40 * 8279199 * 2
def baseEnd_8279199 : Nat := 1417069507074486109845721

theorem tailTrace_8279199 : CollatzResearch.WordTrace tailWord_8279199 prefixEnd_8279199 1417069507074486109845721 := by
  unfold tailWord_8279199
  simp only [CollatzResearch.WordTrace]
  refine ⟨301967195132883472462040651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201311463421922314974693767 301967195132883472462040651)
  ·
    refine ⟨452950792699325208693060977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301967195132883472462040651 452950792699325208693060977)
    ·
      refine ⟨339713094524493906519795733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452950792699325208693060977 339713094524493906519795733)
      ·
        refine ⟨15924051305835651868115425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 339713094524493906519795733 15924051305835651868115425)
        ·
          refine ⟨11943038479376738901086569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15924051305835651868115425 11943038479376738901086569)
          ·
            refine ⟨8957278859532554175814927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11943038479376738901086569 8957278859532554175814927)
            ·
              refine ⟨13435918289298831263722391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8957278859532554175814927 13435918289298831263722391)
              ·
                refine ⟨20153877433948246895583587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13435918289298831263722391 20153877433948246895583587)
                ·
                  refine ⟨30230816150922370343375381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20153877433948246895583587 30230816150922370343375381)
                  ·
                    refine ⟨1417069507074486109845721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30230816150922370343375381 1417069507074486109845721)
                    ·
                      rfl

theorem cell23_8279199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 6].length) (baseStart_8279199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279199 prefixEnd_8279199 := by exact prefixLift 8279199
  have htrace : WordTrace (prefixWord ++ tailWord_8279199) baseStart_8279199 baseEnd_8279199 := by
    simpa [prefixWord, tailWord_8279199, baseEnd_8279199] using wordTrace_append hprefix tailTrace_8279199
  have hstable : (prefixWord ++ tailWord_8279199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279199).length < 2 ^ (prefixWord ++ tailWord_8279199).sum := by decide
  have hdescent : baseEnd_8279199 < baseStart_8279199 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279255 : List Nat := [1, 1, 3, 2, 1, 2, 2, 3, 2, 6]
def baseStart_8279255 : Nat := 118140960795 + 8279255 * 2 ^ 59
def prefixEnd_8279255 : Nat := 4983230072969 + 3 ^ 40 * 8279255 * 2
def baseEnd_8279255 : Nat := 1417079092046703370145635

theorem tailTrace_8279255 : CollatzResearch.WordTrace tailWord_8279255 prefixEnd_8279255 1417079092046703370145635 := by
  unfold tailWord_8279255
  simp only [CollatzResearch.WordTrace]
  refine ⟨301969237620680594026079219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201312825080453729350719479 301969237620680594026079219)
  ·
    refine ⟨452953856431020891039118829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301969237620680594026079219 452953856431020891039118829)
    ·
      refine ⟨169857696161632834139669561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452953856431020891039118829 169857696161632834139669561)
      ·
        refine ⟨127393272121224625604752171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169857696161632834139669561 127393272121224625604752171)
        ·
          refine ⟨191089908181836938407128257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127393272121224625604752171 191089908181836938407128257)
          ·
            refine ⟨143317431136377703805346193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191089908181836938407128257 143317431136377703805346193)
            ·
              refine ⟨107488073352283277854009645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143317431136377703805346193 107488073352283277854009645)
              ·
                refine ⟨40308027507106229195253617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107488073352283277854009645 40308027507106229195253617)
                ·
                  refine ⟨30231020630329671896440213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40308027507106229195253617 30231020630329671896440213)
                  ·
                    refine ⟨1417079092046703370145635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30231020630329671896440213 1417079092046703370145635)
                    ·
                      rfl

theorem cell23_8279255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 6].length) (baseStart_8279255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279255 prefixEnd_8279255 := by exact prefixLift 8279255
  have htrace : WordTrace (prefixWord ++ tailWord_8279255) baseStart_8279255 baseEnd_8279255 := by
    simpa [prefixWord, tailWord_8279255, baseEnd_8279255] using wordTrace_append hprefix tailTrace_8279255
  have hstable : (prefixWord ++ tailWord_8279255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279255).length < 2 ^ (prefixWord ++ tailWord_8279255).sum := by decide
  have hdescent : baseEnd_8279255 < baseStart_8279255 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279256 : List Nat := [2, 1, 2, 2, 5, 1, 1, 3, 2, 1, 3]
def baseStart_8279256 : Nat := 118140960795 + 8279256 * 2 ^ 59
def prefixEnd_8279256 : Nat := 4983230072969 + 3 ^ 40 * 8279256 * 2
def baseEnd_8279256 : Nat := 4251237789620764606524401

theorem tailTrace_8279256 : CollatzResearch.WordTrace tailWord_8279256 prefixEnd_8279256 4251237789620764606524401 := by
  unfold tailWord_8279256
  simp only [CollatzResearch.WordTrace]
  refine ⟨150984637046838485598432811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201312849395784647464577081 150984637046838485598432811)
  ·
    refine ⟨226476955570257728397649217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150984637046838485598432811 226476955570257728397649217)
    ·
      refine ⟨169857716677693296298236913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226476955570257728397649217 169857716677693296298236913)
      ·
        refine ⟨127393287508269972223677685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169857716677693296298236913 127393287508269972223677685)
        ·
          refine ⟨11943120703900309895969783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127393287508269972223677685 11943120703900309895969783)
          ·
            refine ⟨17914681055850464843954675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11943120703900309895969783 17914681055850464843954675)
            ·
              refine ⟨26872021583775697265932013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17914681055850464843954675 26872021583775697265932013)
              ·
                refine ⟨10077008093915886474724505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26872021583775697265932013 10077008093915886474724505)
                ·
                  refine ⟨7557756070436914856043379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10077008093915886474724505 7557756070436914856043379)
                  ·
                    refine ⟨11336634105655372284065069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7557756070436914856043379 11336634105655372284065069)
                    ·
                      refine ⟨4251237789620764606524401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11336634105655372284065069 4251237789620764606524401)
                      ·
                        rfl

theorem cell23_8279256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_8279256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279256 prefixEnd_8279256 := by exact prefixLift 8279256
  have htrace : WordTrace (prefixWord ++ tailWord_8279256) baseStart_8279256 baseEnd_8279256 := by
    simpa [prefixWord, tailWord_8279256, baseEnd_8279256] using wordTrace_append hprefix tailTrace_8279256
  have hstable : (prefixWord ++ tailWord_8279256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279256).length < 2 ^ (prefixWord ++ tailWord_8279256).sum := by decide
  have hdescent : baseEnd_8279256 < baseStart_8279256 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279332 : List Nat := [2, 3, 1, 3, 1, 1, 3, 1, 1, 7]
def baseStart_8279332 : Nat := 118140960795 + 8279332 * 2 ^ 59
def prefixEnd_8279332 : Nat := 4983230072969 + 3 ^ 40 * 8279332 * 2
def baseEnd_8279332 : Nat := 1417092271383502103058017

theorem tailTrace_8279332 : CollatzResearch.WordTrace tailWord_8279332 prefixEnd_8279332 1417092271383502103058017 := by
  unfold tailWord_8279332
  simp only [CollatzResearch.WordTrace]
  refine ⟨150986023020700818088316125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201314697360934424117754833 150986023020700818088316125)
  ·
    refine ⟨56619758632762806783118547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150986023020700818088316125 56619758632762806783118547)
    ·
      refine ⟨84929637949144210174677821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56619758632762806783118547 84929637949144210174677821)
      ·
        refine ⟨31848614230929078815504183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84929637949144210174677821 31848614230929078815504183)
        ·
          refine ⟨47772921346393618223256275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31848614230929078815504183 47772921346393618223256275)
          ·
            refine ⟨71659382019590427334884413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47772921346393618223256275 71659382019590427334884413)
            ·
              refine ⟨26872268257346410250581655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71659382019590427334884413 26872268257346410250581655)
              ·
                refine ⟨40308402386019615375872483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26872268257346410250581655 40308402386019615375872483)
                ·
                  refine ⟨60462603579029423063808725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40308402386019615375872483 60462603579029423063808725)
                  ·
                    refine ⟨1417092271383502103058017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60462603579029423063808725 1417092271383502103058017)
                    ·
                      rfl

theorem cell23_8279332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_8279332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279332 prefixEnd_8279332 := by exact prefixLift 8279332
  have htrace : WordTrace (prefixWord ++ tailWord_8279332) baseStart_8279332 baseEnd_8279332 := by
    simpa [prefixWord, tailWord_8279332, baseEnd_8279332] using wordTrace_append hprefix tailTrace_8279332
  have hstable : (prefixWord ++ tailWord_8279332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279332).length < 2 ^ (prefixWord ++ tailWord_8279332).sum := by decide
  have hdescent : baseEnd_8279332 < baseStart_8279332 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279336 : List Nat := [2, 1, 5, 1, 2, 2, 2, 3, 5]
def baseStart_8279336 : Nat := 118140960795 + 8279336 * 2 ^ 59
def prefixEnd_8279336 : Nat := 4983230072969 + 3 ^ 40 * 8279336 * 2
def baseEnd_8279336 : Nat := 472364318674791588169337

theorem tailTrace_8279336 : CollatzResearch.WordTrace tailWord_8279336 prefixEnd_8279336 472364318674791588169337 := by
  unfold tailWord_8279336
  simp only [CollatzResearch.WordTrace]
  refine ⟨150986095966693572429888931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201314794622258096573185241 150986095966693572429888931)
  ·
    refine ⟨226479143950040358644833397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150986095966693572429888931 226479143950040358644833397)
    ·
      refine ⟨21232419745316283622953131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 226479143950040358644833397 21232419745316283622953131)
      ·
        refine ⟨31848629617974425434429697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21232419745316283622953131 31848629617974425434429697)
        ·
          refine ⟨23886472213480819075822273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31848629617974425434429697 23886472213480819075822273)
          ·
            refine ⟨17914854160110614306866705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23886472213480819075822273 17914854160110614306866705)
            ·
              refine ⟨13436140620082960730150029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17914854160110614306866705 13436140620082960730150029)
              ·
                refine ⟨5038552732531110273806261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13436140620082960730150029 5038552732531110273806261)
                ·
                  refine ⟨472364318674791588169337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5038552732531110273806261 472364318674791588169337)
                  ·
                    rfl

theorem cell23_8279336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3, 5].length) (baseStart_8279336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279336 prefixEnd_8279336 := by exact prefixLift 8279336
  have htrace : WordTrace (prefixWord ++ tailWord_8279336) baseStart_8279336 baseEnd_8279336 := by
    simpa [prefixWord, tailWord_8279336, baseEnd_8279336] using wordTrace_append hprefix tailTrace_8279336
  have hstable : (prefixWord ++ tailWord_8279336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279336).length < 2 ^ (prefixWord ++ tailWord_8279336).sum := by decide
  have hdescent : baseEnd_8279336 < baseStart_8279336 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279352 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 4, 1, 4]
def baseStart_8279352 : Nat := 118140960795 + 8279352 * 2 ^ 59
def prefixEnd_8279352 : Nat := 4983230072969 + 3 ^ 40 * 8279352 * 2
def baseEnd_8279352 : Nat := 4251287083763596230923959

theorem tailTrace_8279352 : CollatzResearch.WordTrace tailWord_8279352 prefixEnd_8279352 4251287083763596230923959 := by
  unfold tailWord_8279352
  simp only [CollatzResearch.WordTrace]
  refine ⟨150986387750664589796180155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201315183667552786394906873 150986387750664589796180155)
  ·
    refine ⟨226479581625996884694270233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150986387750664589796180155 226479581625996884694270233)
    ·
      refine ⟨169859686219497663520702675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226479581625996884694270233 169859686219497663520702675)
      ·
        refine ⟨254789529329246495281054013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169859686219497663520702675 254789529329246495281054013)
        ·
          refine ⟨95546073498467435730395255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254789529329246495281054013 95546073498467435730395255)
          ·
            refine ⟨143319110247701153595592883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95546073498467435730395255 143319110247701153595592883)
            ·
              refine ⟨214978665371551730393389325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143319110247701153595592883 214978665371551730393389325)
              ·
                refine ⟨80616999514331898897520997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214978665371551730393389325 80616999514331898897520997)
                ·
                  refine ⟨15115687408937231043285187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80616999514331898897520997 15115687408937231043285187)
                  ·
                    refine ⟨22673531113405846564927781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15115687408937231043285187 22673531113405846564927781)
                    ·
                      refine ⟨4251287083763596230923959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22673531113405846564927781 4251287083763596230923959)
                      ·
                        rfl

theorem cell23_8279352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_8279352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279352 prefixEnd_8279352 := by exact prefixLift 8279352
  have htrace : WordTrace (prefixWord ++ tailWord_8279352) baseStart_8279352 baseEnd_8279352 := by
    simpa [prefixWord, tailWord_8279352, baseEnd_8279352] using wordTrace_append hprefix tailTrace_8279352
  have hstable : (prefixWord ++ tailWord_8279352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279352).length < 2 ^ (prefixWord ++ tailWord_8279352).sum := by decide
  have hdescent : baseEnd_8279352 < baseStart_8279352 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279369 : List Nat := [1, 2, 1, 1, 2, 3, 4, 1, 2, 4, 2]
def baseStart_8279369 : Nat := 118140960795 + 8279369 * 2 ^ 59
def prefixEnd_8279369 : Nat := 4983230072969 + 3 ^ 40 * 8279369 * 2
def baseEnd_8279369 : Nat := 4251295812934722664411381

theorem tailTrace_8279369 : CollatzResearch.WordTrace tailWord_8279369 prefixEnd_8279369 4251295812934722664411381 := by
  unfold tailWord_8279369
  simp only [CollatzResearch.WordTrace]
  refine ⟨301973395542267591495729161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201315597028178394330486107 301973395542267591495729161)
  ·
    refine ⟨226480046656700693621796871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301973395542267591495729161 226480046656700693621796871)
    ·
      refine ⟨339720069985051040432695307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226480046656700693621796871 339720069985051040432695307)
      ·
        refine ⟨509580104977576560649042961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339720069985051040432695307 509580104977576560649042961)
        ·
          refine ⟨382185078733182420486782221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 509580104977576560649042961 382185078733182420486782221)
          ·
            refine ⟨143319404524943407682543333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382185078733182420486782221 143319404524943407682543333)
            ·
              refine ⟨26872388348426888940476875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143319404524943407682543333 26872388348426888940476875)
              ·
                refine ⟨40308582522640333410715313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26872388348426888940476875 40308582522640333410715313)
                ·
                  refine ⟨30231436891980250058036485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40308582522640333410715313 30231436891980250058036485)
                  ·
                    refine ⟨5668394417246296885881841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30231436891980250058036485 5668394417246296885881841)
                    ·
                      refine ⟨4251295812934722664411381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5668394417246296885881841 4251295812934722664411381)
                      ·
                        rfl

theorem cell23_8279369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 4, 2].length) (baseStart_8279369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279369 prefixEnd_8279369 := by exact prefixLift 8279369
  have htrace : WordTrace (prefixWord ++ tailWord_8279369) baseStart_8279369 baseEnd_8279369 := by
    simpa [prefixWord, tailWord_8279369, baseEnd_8279369] using wordTrace_append hprefix tailTrace_8279369
  have hstable : (prefixWord ++ tailWord_8279369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279369).length < 2 ^ (prefixWord ++ tailWord_8279369).sum := by decide
  have hdescent : baseEnd_8279369 < baseStart_8279369 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279392 : List Nat := [2, 1, 1, 3, 4, 1, 1, 2, 8]
def baseStart_8279392 : Nat := 118140960795 + 8279392 * 2 ^ 59
def prefixEnd_8279392 : Nat := 4983230072969 + 3 ^ 40 * 8279392 * 2
def baseEnd_8279392 : Nat := 472367513665530674935975

theorem tailTrace_8279392 : CollatzResearch.WordTrace tailWord_8279392 prefixEnd_8279392 472367513665530674935975 := by
  unfold tailWord_8279392
  simp only [CollatzResearch.WordTrace]
  refine ⟨150987117210592133211908215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201316156280789510949210953 150987117210592133211908215)
  ·
    refine ⟨226480675815888199817862323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150987117210592133211908215 226480675815888199817862323)
    ·
      refine ⟨339721013723832299726793485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226480675815888199817862323 339721013723832299726793485)
      ·
        refine ⟨127395380146437112397547557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339721013723832299726793485 127395380146437112397547557)
        ·
          refine ⟨23886633777456958574540167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127395380146437112397547557 23886633777456958574540167)
          ·
            refine ⟨35829950666185437861810251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23886633777456958574540167 35829950666185437861810251)
            ·
              refine ⟨53744925999278156792715377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35829950666185437861810251 53744925999278156792715377)
              ·
                refine ⟨40308694499458617594536533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53744925999278156792715377 40308694499458617594536533)
                ·
                  refine ⟨472367513665530674935975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40308694499458617594536533 472367513665530674935975)
                  ·
                    rfl

theorem cell23_8279392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 8].length) (baseStart_8279392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279392 prefixEnd_8279392 := by exact prefixLift 8279392
  have htrace : WordTrace (prefixWord ++ tailWord_8279392) baseStart_8279392 baseEnd_8279392 := by
    simpa [prefixWord, tailWord_8279392, baseEnd_8279392] using wordTrace_append hprefix tailTrace_8279392
  have hstable : (prefixWord ++ tailWord_8279392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279392).length < 2 ^ (prefixWord ++ tailWord_8279392).sum := by decide
  have hdescent : baseEnd_8279392 < baseStart_8279392 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279413 : List Nat := [1, 3, 4, 1, 3, 2, 1, 1, 3, 4]
def baseStart_8279413 : Nat := 118140960795 + 8279413 * 2 ^ 59
def prefixEnd_8279413 : Nat := 4983230072969 + 3 ^ 40 * 8279413 * 2
def baseEnd_8279413 : Nat := 1417106135361173497420393

theorem tailTrace_8279413 : CollatzResearch.WordTrace tailWord_8279413 prefixEnd_8279413 1417106135361173497420393 := by
  unfold tailWord_8279413
  simp only [CollatzResearch.WordTrace]
  refine ⟨301975000354108187010330893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201316666902738791340220595 301975000354108187010330893)
  ·
    refine ⟨113240625132790570128874085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301975000354108187010330893 113240625132790570128874085)
    ·
      refine ⟨21232617212398231899163891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113240625132790570128874085 21232617212398231899163891)
      ·
        refine ⟨31848925818597347848745837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21232617212398231899163891 31848925818597347848745837)
        ·
          refine ⟨11943347181974005443279689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31848925818597347848745837 11943347181974005443279689)
          ·
            refine ⟨8957510386480504082459767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11943347181974005443279689 8957510386480504082459767)
            ·
              refine ⟨13436265579720756123689651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8957510386480504082459767 13436265579720756123689651)
              ·
                refine ⟨20154398369581134185534477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13436265579720756123689651 20154398369581134185534477)
                ·
                  refine ⟨7557899388592925319575429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20154398369581134185534477 7557899388592925319575429)
                  ·
                    refine ⟨1417106135361173497420393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7557899388592925319575429 1417106135361173497420393)
                    ·
                      rfl

theorem cell23_8279413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_8279413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279413 prefixEnd_8279413 := by exact prefixLift 8279413
  have htrace : WordTrace (prefixWord ++ tailWord_8279413) baseStart_8279413 baseEnd_8279413 := by
    simpa [prefixWord, tailWord_8279413, baseEnd_8279413] using wordTrace_append hprefix tailTrace_8279413
  have hstable : (prefixWord ++ tailWord_8279413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279413).length < 2 ^ (prefixWord ++ tailWord_8279413).sum := by decide
  have hdescent : baseEnd_8279413 < baseStart_8279413 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279429 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 3, 5, 2]
def baseStart_8279429 : Nat := 118140960795 + 8279429 * 2 ^ 59
def prefixEnd_8279429 : Nat := 4983230072969 + 3 ^ 40 * 8279429 * 2
def baseEnd_8279429 : Nat := 4251326621773992429661105

theorem tailTrace_8279429 : CollatzResearch.WordTrace tailWord_8279429 prefixEnd_8279429 4251326621773992429661105 := by
  unfold tailWord_8279429
  simp only [CollatzResearch.WordTrace]
  refine ⟨301975583922050221742913341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201317055948033481161942227 301975583922050221742913341)
  ·
    refine ⟨113240843970768833153592503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301975583922050221742913341 113240843970768833153592503)
    ·
      refine ⟨169861265956153249730388755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113240843970768833153592503 169861265956153249730388755)
      ·
        refine ⟨254791898934229874595583133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169861265956153249730388755 254791898934229874595583133)
        ·
          refine ⟨95546962100336202973343675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254791898934229874595583133 95546962100336202973343675)
          ·
            refine ⟨143320443150504304460015513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95546962100336202973343675 143320443150504304460015513)
            ·
              refine ⟨107490332362878228345011635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143320443150504304460015513 107490332362878228345011635)
              ·
                refine ⟨161235498544317342517517453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107490332362878228345011635 161235498544317342517517453)
                ·
                  refine ⟨60463311954119003444069045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161235498544317342517517453 60463311954119003444069045)
                  ·
                    refine ⟨5668435495698656572881473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60463311954119003444069045 5668435495698656572881473)
                    ·
                      refine ⟨4251326621773992429661105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5668435495698656572881473 4251326621773992429661105)
                      ·
                        rfl

theorem cell23_8279429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 5, 2].length) (baseStart_8279429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279429 prefixEnd_8279429 := by exact prefixLift 8279429
  have htrace : WordTrace (prefixWord ++ tailWord_8279429) baseStart_8279429 baseEnd_8279429 := by
    simpa [prefixWord, tailWord_8279429, baseEnd_8279429] using wordTrace_append hprefix tailTrace_8279429
  have hstable : (prefixWord ++ tailWord_8279429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279429).length < 2 ^ (prefixWord ++ tailWord_8279429).sum := by decide
  have hdescent : baseEnd_8279429 < baseStart_8279429 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279456 : List Nat := [2, 1, 1, 4, 1, 2, 5, 1, 1, 5]
def baseStart_8279456 : Nat := 118140960795 + 8279456 * 2 ^ 59
def prefixEnd_8279456 : Nat := 4983230072969 + 3 ^ 40 * 8279456 * 2
def baseEnd_8279456 : Nat := 1417113495250554608007827

theorem tailTrace_8279456 : CollatzResearch.WordTrace tailWord_8279456 prefixEnd_8279456 1417113495250554608007827 := by
  unfold tailWord_8279456
  simp only [CollatzResearch.WordTrace]
  refine ⟨150988284346476202677073111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201317712461968270236097481 150988284346476202677073111)
  ·
    refine ⟨226482426519714304015609667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150988284346476202677073111 226482426519714304015609667)
    ·
      refine ⟨339723639779571456023414501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226482426519714304015609667 339723639779571456023414501)
      ·
        refine ⟨63698182458669648004390219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339723639779571456023414501 63698182458669648004390219)
        ·
          refine ⟨95547273688004472006585329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63698182458669648004390219 95547273688004472006585329)
          ·
            refine ⟨71660455266003354004938997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95547273688004472006585329 71660455266003354004938997)
            ·
              refine ⟨6718167681187814437963031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71660455266003354004938997 6718167681187814437963031)
              ·
                refine ⟨10077251521781721656944547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6718167681187814437963031 10077251521781721656944547)
                ·
                  refine ⟨15115877282672582485416821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10077251521781721656944547 15115877282672582485416821)
                  ·
                    refine ⟨1417113495250554608007827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15115877282672582485416821 1417113495250554608007827)
                    ·
                      rfl

theorem cell23_8279456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 1, 5].length) (baseStart_8279456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279456 prefixEnd_8279456 := by exact prefixLift 8279456
  have htrace : WordTrace (prefixWord ++ tailWord_8279456) baseStart_8279456 baseEnd_8279456 := by
    simpa [prefixWord, tailWord_8279456, baseEnd_8279456] using wordTrace_append hprefix tailTrace_8279456
  have hstable : (prefixWord ++ tailWord_8279456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279456).length < 2 ^ (prefixWord ++ tailWord_8279456).sum := by decide
  have hdescent : baseEnd_8279456 < baseStart_8279456 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279464 : List Nat := [2, 1, 6, 1, 3, 1, 2, 2, 1, 4]
def baseStart_8279464 : Nat := 118140960795 + 8279464 * 2 ^ 59
def prefixEnd_8279464 : Nat := 4983230072969 + 3 ^ 40 * 8279464 * 2
def baseEnd_8279464 : Nat := 1417114864532299930907815

theorem tailTrace_8279464 : CollatzResearch.WordTrace tailWord_8279464 prefixEnd_8279464 1417114864532299930907815 := by
  unfold tailWord_8279464
  simp only [CollatzResearch.WordTrace]
  refine ⟨150988430238461711360218723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201317906984615615146958297 150988430238461711360218723)
  ·
    refine ⟨226482645357692567040328085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150988430238461711360218723 226482645357692567040328085)
    ·
      refine ⟨10616374001141839080015379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 226482645357692567040328085 10616374001141839080015379)
      ·
        refine ⟨15924561001712758620023069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10616374001141839080015379 15924561001712758620023069)
        ·
          refine ⟨5971710375642284482508651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15924561001712758620023069 5971710375642284482508651)
          ·
            refine ⟨8957565563463426723762977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5971710375642284482508651 8957565563463426723762977)
            ·
              refine ⟨6718174172597570042822233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8957565563463426723762977 6718174172597570042822233)
              ·
                refine ⟨5038630629448177532116675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6718174172597570042822233 5038630629448177532116675)
                ·
                  refine ⟨7557945944172266298175013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5038630629448177532116675 7557945944172266298175013)
                  ·
                    refine ⟨1417114864532299930907815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7557945944172266298175013 1417114864532299930907815)
                    ·
                      rfl

theorem cell23_8279464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_8279464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279464 prefixEnd_8279464 := by exact prefixLift 8279464
  have htrace : WordTrace (prefixWord ++ tailWord_8279464) baseStart_8279464 baseEnd_8279464 := by
    simpa [prefixWord, tailWord_8279464, baseEnd_8279464] using wordTrace_append hprefix tailTrace_8279464
  have hstable : (prefixWord ++ tailWord_8279464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279464).length < 2 ^ (prefixWord ++ tailWord_8279464).sum := by decide
  have hdescent : baseEnd_8279464 < baseStart_8279464 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279472 : List Nat := [2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 6]
def baseStart_8279472 : Nat := 118140960795 + 8279472 * 2 ^ 59
def prefixEnd_8279472 : Nat := 4983230072969 + 3 ^ 40 * 8279472 * 2
def baseEnd_8279472 : Nat := 4251348701442135761423407

theorem tailTrace_8279472 : CollatzResearch.WordTrace tailWord_8279472 prefixEnd_8279472 4251348701442135761423407 := by
  unfold tailWord_8279472
  simp only [CollatzResearch.WordTrace]
  refine ⟨150988576130447220043364335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201318101507262960057819113 150988576130447220043364335)
  ·
    refine ⟨226482864195670830065046503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150988576130447220043364335 226482864195670830065046503)
    ·
      refine ⟨339724296293506245097569755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226482864195670830065046503 339724296293506245097569755)
      ·
        refine ⟨509586444440259367646354633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339724296293506245097569755 509586444440259367646354633)
        ·
          refine ⟨382189833330194525734765975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 509586444440259367646354633 382189833330194525734765975)
          ·
            refine ⟨573284749995291788602148963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382189833330194525734765975 573284749995291788602148963)
            ·
              refine ⟨859927124992937682903223445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573284749995291788602148963 859927124992937682903223445)
              ·
                refine ⟨40309083984043953886088599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 859927124992937682903223445 40309083984043953886088599)
                ·
                  refine ⟨60463625976065930829132899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40309083984043953886088599 60463625976065930829132899)
                  ·
                    refine ⟨90695438964098896243699349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60463625976065930829132899 90695438964098896243699349)
                    ·
                      refine ⟨4251348701442135761423407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90695438964098896243699349 4251348701442135761423407)
                      ·
                        rfl

theorem cell23_8279472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 6].length) (baseStart_8279472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279472 prefixEnd_8279472 := by exact prefixLift 8279472
  have htrace : WordTrace (prefixWord ++ tailWord_8279472) baseStart_8279472 baseEnd_8279472 := by
    simpa [prefixWord, tailWord_8279472, baseEnd_8279472] using wordTrace_append hprefix tailTrace_8279472
  have hstable : (prefixWord ++ tailWord_8279472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279472).length < 2 ^ (prefixWord ++ tailWord_8279472).sum := by decide
  have hdescent : baseEnd_8279472 < baseStart_8279472 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279479 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 5, 2, 3]
def baseStart_8279479 : Nat := 118140960795 + 8279479 * 2 ^ 59
def prefixEnd_8279479 : Nat := 4983230072969 + 3 ^ 40 * 8279479 * 2
def baseEnd_8279479 : Nat := 4251352295806717234035875

theorem tailTrace_8279479 : CollatzResearch.WordTrace tailWord_8279479 prefixEnd_8279479 4251352295806717234035875 := by
  unfold tailWord_8279479
  simp only [CollatzResearch.WordTrace]
  refine ⟨301977407571869080282233491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201318271714579386854822327 301977407571869080282233491)
  ·
    refine ⟨452966111357803620423350237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301977407571869080282233491 452966111357803620423350237)
    ·
      refine ⟨169862291759176357658756339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452966111357803620423350237 169862291759176357658756339)
      ·
        refine ⟨254793437638764536488134509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169862291759176357658756339 254793437638764536488134509)
        ·
          refine ⟨95547539114536701183050441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254793437638764536488134509 95547539114536701183050441)
          ·
            refine ⟨71660654335902525887287831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95547539114536701183050441 71660654335902525887287831)
            ·
              refine ⟨107490981503853788830931747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71660654335902525887287831 107490981503853788830931747)
              ·
                refine ⟨161236472255780683246397621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107490981503853788830931747 161236472255780683246397621)
                ·
                  refine ⟨15115919273979439054349777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161236472255780683246397621 15115919273979439054349777)
                  ·
                    refine ⟨11336939455484579290762333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15115919273979439054349777 11336939455484579290762333)
                    ·
                      refine ⟨4251352295806717234035875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11336939455484579290762333 4251352295806717234035875)
                      ·
                        rfl

theorem cell23_8279479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2, 3].length) (baseStart_8279479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279479 prefixEnd_8279479 := by exact prefixLift 8279479
  have htrace : WordTrace (prefixWord ++ tailWord_8279479) baseStart_8279479 baseEnd_8279479 := by
    simpa [prefixWord, tailWord_8279479, baseEnd_8279479] using wordTrace_append hprefix tailTrace_8279479
  have hstable : (prefixWord ++ tailWord_8279479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279479).length < 2 ^ (prefixWord ++ tailWord_8279479).sum := by decide
  have hdescent : baseEnd_8279479 < baseStart_8279479 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279496 : List Nat := [2, 1, 3, 1, 3, 1, 2, 4, 1, 2, 3]
def baseStart_8279496 : Nat := 118140960795 + 8279496 * 2 ^ 59
def prefixEnd_8279496 : Nat := 4983230072969 + 3 ^ 40 * 8279496 * 2
def baseEnd_8279496 : Nat := 4251361024977843667523297

theorem tailTrace_8279496 : CollatzResearch.WordTrace tailWord_8279496 prefixEnd_8279496 4251361024977843667523297 := by
  unfold tailWord_8279496
  simp only [CollatzResearch.WordTrace]
  refine ⟨150989013806403746092801171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201318685075204994790401561 150989013806403746092801171)
  ·
    refine ⟨226483520709605619139201757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150989013806403746092801171 226483520709605619139201757)
    ·
      refine ⟨84931320266102107177200659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226483520709605619139201757 84931320266102107177200659)
      ·
        refine ⟨127396980399153160765800989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84931320266102107177200659 127396980399153160765800989)
        ·
          refine ⟨47773867649682435287175371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127396980399153160765800989 47773867649682435287175371)
          ·
            refine ⟨71660801474523652930763057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47773867649682435287175371 71660801474523652930763057)
            ·
              refine ⟨53745601105892739698072293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71660801474523652930763057 53745601105892739698072293)
              ·
                refine ⟨10077300207354888693388555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53745601105892739698072293 10077300207354888693388555)
                ·
                  refine ⟨15115950311032333040082833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10077300207354888693388555 15115950311032333040082833)
                  ·
                    refine ⟨11336962733274249780062125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15115950311032333040082833 11336962733274249780062125)
                    ·
                      refine ⟨4251361024977843667523297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11336962733274249780062125 4251361024977843667523297)
                      ·
                        rfl

theorem cell23_8279496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_8279496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279496 prefixEnd_8279496 := by exact prefixLift 8279496
  have htrace : WordTrace (prefixWord ++ tailWord_8279496) baseStart_8279496 baseEnd_8279496 := by
    simpa [prefixWord, tailWord_8279496, baseEnd_8279496] using wordTrace_append hprefix tailTrace_8279496
  have hstable : (prefixWord ++ tailWord_8279496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279496).length < 2 ^ (prefixWord ++ tailWord_8279496).sum := by decide
  have hdescent : baseEnd_8279496 < baseStart_8279496 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279510 : List Nat := [5, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4]
def baseStart_8279510 : Nat := 118140960795 + 8279510 * 2 ^ 59
def prefixEnd_8279510 : Nat := 4983230072969 + 3 ^ 40 * 8279510 * 2
def baseEnd_8279510 : Nat := 4251368213707006612748233

theorem tailTrace_8279510 : CollatzResearch.WordTrace tailWord_8279510 prefixEnd_8279510 4251368213707006612748233 := by
  unfold tailWord_8279510
  simp only [CollatzResearch.WordTrace]
  refine ⟨18873658639672298286038249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201319025489837848384407989 18873658639672298286038249)
  ·
    refine ⟨14155243979754223714528687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18873658639672298286038249 14155243979754223714528687)
    ·
      refine ⟨21232865969631335571793031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14155243979754223714528687 21232865969631335571793031)
      ·
        refine ⟨31849298954447003357689547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21232865969631335571793031 31849298954447003357689547)
        ·
          refine ⟨47773948431670505036534321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31849298954447003357689547 47773948431670505036534321)
          ·
            refine ⟨35830461323752878777400741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47773948431670505036534321 35830461323752878777400741)
            ·
              refine ⟨6718211498203664770762639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35830461323752878777400741 6718211498203664770762639)
              ·
                refine ⟨10077317247305497156143959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6718211498203664770762639 10077317247305497156143959)
                ·
                  refine ⟨15115975870958245734215939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10077317247305497156143959 15115975870958245734215939)
                  ·
                    refine ⟨22673963806437368601323909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15115975870958245734215939 22673963806437368601323909)
                    ·
                      refine ⟨4251368213707006612748233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22673963806437368601323909 4251368213707006612748233)
                      ·
                        rfl

theorem cell23_8279510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_8279510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279510 prefixEnd_8279510 := by exact prefixLift 8279510
  have htrace : WordTrace (prefixWord ++ tailWord_8279510) baseStart_8279510 baseEnd_8279510 := by
    simpa [prefixWord, tailWord_8279510, baseEnd_8279510] using wordTrace_append hprefix tailTrace_8279510
  have hstable : (prefixWord ++ tailWord_8279510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279510).length < 2 ^ (prefixWord ++ tailWord_8279510).sum := by decide
  have hdescent : baseEnd_8279510 < baseStart_8279510 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279513 : List Nat := [1, 2, 1, 2, 4, 2, 4, 1, 1, 2, 3]
def baseStart_8279513 : Nat := 118140960795 + 8279513 * 2 ^ 59
def prefixEnd_8279513 : Nat := 4983230072969 + 3 ^ 40 * 8279513 * 2
def baseEnd_8279513 : Nat := 4251369754148970101010719

theorem tailTrace_8279513 : CollatzResearch.WordTrace tailWord_8279513 prefixEnd_8279513 4251369754148970101010719 := by
  unfold tailWord_8279513
  simp only [CollatzResearch.WordTrace]
  refine ⟨301978647653745904088971193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201319098435830602725980795 301978647653745904088971193)
  ·
    refine ⟨226483985740309428066728395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301978647653745904088971193 226483985740309428066728395)
    ·
      refine ⟨339725978610464142100092593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226483985740309428066728395 339725978610464142100092593)
      ·
        refine ⟨254794483957848106575069445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339725978610464142100092593 254794483957848106575069445)
        ·
          refine ⟨47773965742096519982825521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254794483957848106575069445 47773965742096519982825521)
          ·
            refine ⟨35830474306572389987119141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47773965742096519982825521 35830474306572389987119141)
            ·
              refine ⟨6718213932482323122584839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35830474306572389987119141 6718213932482323122584839)
              ·
                refine ⟨10077320898723484683877259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6718213932482323122584839 10077320898723484683877259)
                ·
                  refine ⟨15115981348085227025815889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10077320898723484683877259 15115981348085227025815889)
                  ·
                    refine ⟨11336986011063920269361917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15115981348085227025815889 11336986011063920269361917)
                    ·
                      refine ⟨4251369754148970101010719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11336986011063920269361917 4251369754148970101010719)
                      ·
                        rfl

theorem cell23_8279513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 1, 2, 3].length) (baseStart_8279513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279513 prefixEnd_8279513 := by exact prefixLift 8279513
  have htrace : WordTrace (prefixWord ++ tailWord_8279513) baseStart_8279513 baseEnd_8279513 := by
    simpa [prefixWord, tailWord_8279513, baseEnd_8279513] using wordTrace_append hprefix tailTrace_8279513
  have hstable : (prefixWord ++ tailWord_8279513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279513).length < 2 ^ (prefixWord ++ tailWord_8279513).sum := by decide
  have hdescent : baseEnd_8279513 < baseStart_8279513 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279550 : List Nat := [4, 2, 2, 3, 1, 2, 2, 7]
def baseStart_8279550 : Nat := 118140960795 + 8279550 * 2 ^ 59
def prefixEnd_8279550 : Nat := 4983230072969 + 3 ^ 40 * 8279550 * 2
def baseEnd_8279550 : Nat := 157458842701229128009187

theorem tailTrace_8279550 : CollatzResearch.WordTrace tailWord_8279550 prefixEnd_8279550 157458842701229128009187 := by
  unfold tailWord_8279550
  simp only [CollatzResearch.WordTrace]
  refine ⟨37747499644326482426008513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201319998103074572938712069 37747499644326482426008513)
  ·
    refine ⟨28310624733244861819506385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37747499644326482426008513 28310624733244861819506385)
    ·
      refine ⟨21232968549933646364629789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28310624733244861819506385 21232968549933646364629789)
      ·
        refine ⟨7962363206225117386736171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21232968549933646364629789 7962363206225117386736171)
        ·
          refine ⟨11943544809337676080104257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7962363206225117386736171 11943544809337676080104257)
          ·
            refine ⟨8957658607003257060078193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11943544809337676080104257 8957658607003257060078193)
            ·
              refine ⟨6718243955252442795058645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8957658607003257060078193 6718243955252442795058645)
              ·
                refine ⟨157458842701229128009187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6718243955252442795058645 157458842701229128009187)
                ·
                  rfl

theorem cell23_8279550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 7].length) (baseStart_8279550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279550 prefixEnd_8279550 := by exact prefixLift 8279550
  have htrace : WordTrace (prefixWord ++ tailWord_8279550) baseStart_8279550 baseEnd_8279550 := by
    simpa [prefixWord, tailWord_8279550, baseEnd_8279550] using wordTrace_append hprefix tailTrace_8279550
  have hstable : (prefixWord ++ tailWord_8279550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279550).length < 2 ^ (prefixWord ++ tailWord_8279550).sum := by decide
  have hdescent : baseEnd_8279550 < baseStart_8279550 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279569 : List Nat := [1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 5]
def baseStart_8279569 : Nat := 118140960795 + 8279569 * 2 ^ 59
def prefixEnd_8279569 : Nat := 4983230072969 + 3 ^ 40 * 8279569 * 2
def baseEnd_8279569 : Nat := 4251398509065621881910461

theorem tailTrace_8279569 : CollatzResearch.WordTrace tailWord_8279569 prefixEnd_8279569 4251398509065621881910461 := by
  unfold tailWord_8279569
  simp only [CollatzResearch.WordTrace]
  refine ⟨301980690141543025653009761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201320460094362017102006507 301980690141543025653009761)
  ·
    refine ⟨226485517606157269239757321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301980690141543025653009761 226485517606157269239757321)
    ·
      refine ⟨169864138204617951929817991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226485517606157269239757321 169864138204617951929817991)
      ·
        refine ⟨254796207306926927894726987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169864138204617951929817991 254796207306926927894726987)
        ·
          refine ⟨382194310960390391842090481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254796207306926927894726987 382194310960390391842090481)
          ·
            refine ⟨286645733220292793881567861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382194310960390391842090481 286645733220292793881567861)
            ·
              refine ⟨26873037489402449426396987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 286645733220292793881567861 26873037489402449426396987)
              ·
                refine ⟨40309556234103674139595481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26873037489402449426396987 40309556234103674139595481)
                ·
                  refine ⟨30232167175577755604696611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40309556234103674139595481 30232167175577755604696611)
                  ·
                    refine ⟨45348250763366633407044917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30232167175577755604696611 45348250763366633407044917)
                    ·
                      refine ⟨4251398509065621881910461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45348250763366633407044917 4251398509065621881910461)
                      ·
                        rfl

theorem cell23_8279569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_8279569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279569 prefixEnd_8279569 := by exact prefixLift 8279569
  have htrace : WordTrace (prefixWord ++ tailWord_8279569) baseStart_8279569 baseEnd_8279569 := by
    simpa [prefixWord, tailWord_8279569, baseEnd_8279569] using wordTrace_append hprefix tailTrace_8279569
  have hstable : (prefixWord ++ tailWord_8279569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279569).length < 2 ^ (prefixWord ++ tailWord_8279569).sum := by decide
  have hdescent : baseEnd_8279569 < baseStart_8279569 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279583 : List Nat := [1, 1, 2, 4, 1, 1, 4, 1, 4, 2, 2]
def baseStart_8279583 : Nat := 118140960795 + 8279583 * 2 ^ 59
def prefixEnd_8279583 : Nat := 4983230072969 + 3 ^ 40 * 8279583 * 2
def baseEnd_8279583 : Nat := 4251405697794784827135397

theorem tailTrace_8279583 : CollatzResearch.WordTrace tailWord_8279583 prefixEnd_8279583 4251405697794784827135397 := by
  unfold tailWord_8279583
  simp only [CollatzResearch.WordTrace]
  refine ⟨301981200763492306044019403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201320800508994870696012935 301981200763492306044019403)
  ·
    refine ⟨452971801145238459066029105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301981200763492306044019403 452971801145238459066029105)
    ·
      refine ⟨339728850858928844299521829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452971801145238459066029105 339728850858928844299521829)
      ·
        refine ⟨63699159536049158306160343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339728850858928844299521829 63699159536049158306160343)
        ·
          refine ⟨95548739304073737459240515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63699159536049158306160343 95548739304073737459240515)
          ·
            refine ⟨143323108956110606188860773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95548739304073737459240515 143323108956110606188860773)
            ·
              refine ⟨26873082929270738660411395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143323108956110606188860773 26873082929270738660411395)
              ·
                refine ⟨40309624393906107990617093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26873082929270738660411395 40309624393906107990617093)
                ·
                  refine ⟨7558054573857395248240705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40309624393906107990617093 7558054573857395248240705)
                  ·
                    refine ⟨5668540930393046436180529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7558054573857395248240705 5668540930393046436180529)
                    ·
                      refine ⟨4251405697794784827135397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5668540930393046436180529 4251405697794784827135397)
                      ·
                        rfl

theorem cell23_8279583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_8279583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279583 prefixEnd_8279583 := by exact prefixLift 8279583
  have htrace : WordTrace (prefixWord ++ tailWord_8279583) baseStart_8279583 baseEnd_8279583 := by
    simpa [prefixWord, tailWord_8279583, baseEnd_8279583] using wordTrace_append hprefix tailTrace_8279583
  have hstable : (prefixWord ++ tailWord_8279583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279583).length < 2 ^ (prefixWord ++ tailWord_8279583).sum := by decide
  have hdescent : baseEnd_8279583 < baseStart_8279583 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279636 : List Nat := [2, 4, 1, 1, 1, 2, 1, 4, 2, 5]
def baseStart_8279636 : Nat := 118140960795 + 8279636 * 2 ^ 59
def prefixEnd_8279636 : Nat := 4983230072969 + 3 ^ 40 * 8279636 * 2
def baseEnd_8279636 : Nat := 1417144304089824373257551

theorem tailTrace_8279636 : CollatzResearch.WordTrace tailWord_8279636 prefixEnd_8279636 1417144304089824373257551 := by
  unfold tailWord_8279636
  simp only [CollatzResearch.WordTrace]
  refine ⟨150991566916150148047849381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201322089221533530730465841 150991566916150148047849381)
  ·
    refine ⟨28310918796778152758971759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150991566916150148047849381 28310918796778152758971759)
    ·
      refine ⟨42466378195167229138457639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28310918796778152758971759 42466378195167229138457639)
      ·
        refine ⟨63699567292750843707686459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42466378195167229138457639 63699567292750843707686459)
        ·
          refine ⟨95549350939126265561529689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63699567292750843707686459 95549350939126265561529689)
          ·
            refine ⟨71662013204344699171147267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95549350939126265561529689 71662013204344699171147267)
            ·
              refine ⟨107493019806517048756720901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71662013204344699171147267 107493019806517048756720901)
              ·
                refine ⟨20154941213721946641885169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107493019806517048756720901 20154941213721946641885169)
                ·
                  refine ⟨15116205910291459981413877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20154941213721946641885169 15116205910291459981413877)
                  ·
                    refine ⟨1417144304089824373257551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15116205910291459981413877 1417144304089824373257551)
                    ·
                      rfl

theorem cell23_8279636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_8279636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279636 prefixEnd_8279636 := by exact prefixLift 8279636
  have htrace : WordTrace (prefixWord ++ tailWord_8279636) baseStart_8279636 baseEnd_8279636 := by
    simpa [prefixWord, tailWord_8279636, baseEnd_8279636] using wordTrace_append hprefix tailTrace_8279636
  have hstable : (prefixWord ++ tailWord_8279636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279636).length < 2 ^ (prefixWord ++ tailWord_8279636).sum := by decide
  have hdescent : baseEnd_8279636 < baseStart_8279636 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279670 : List Nat := [5, 1, 1, 2, 2, 3, 1, 1, 2, 5]
def baseStart_8279670 : Nat := 118140960795 + 8279670 * 2 ^ 59
def prefixEnd_8279670 : Nat := 4983230072969 + 3 ^ 40 * 8279670 * 2
def baseEnd_8279670 : Nat := 1417150123537241995582499

theorem tailTrace_8279670 : CollatzResearch.WordTrace tailWord_8279670 prefixEnd_8279670 1417150123537241995582499 := by
  unfold tailWord_8279670
  simp only [CollatzResearch.WordTrace]
  refine ⟨18874023369636069993902279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201322915942784746601624309 18874023369636069993902279)
  ·
    refine ⟨28311035054454104990853419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18874023369636069993902279 28311035054454104990853419)
    ·
      refine ⟨42466552581681157486280129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28311035054454104990853419 42466552581681157486280129)
      ·
        refine ⟨31849914436260868114710097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42466552581681157486280129 31849914436260868114710097)
        ·
          refine ⟨23887435827195651086032573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31849914436260868114710097 23887435827195651086032573)
          ·
            refine ⟨8957788435198369157262215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23887435827195651086032573 8957788435198369157262215)
            ·
              refine ⟨13436682652797553735893323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8957788435198369157262215 13436682652797553735893323)
              ·
                refine ⟨20155023979196330603839985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13436682652797553735893323 20155023979196330603839985)
                ·
                  refine ⟨15116267984397247952879989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20155023979196330603839985 15116267984397247952879989)
                  ·
                    refine ⟨1417150123537241995582499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15116267984397247952879989 1417150123537241995582499)
                    ·
                      rfl

theorem cell23_8279670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_8279670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279670 prefixEnd_8279670 := by exact prefixLift 8279670
  have htrace : WordTrace (prefixWord ++ tailWord_8279670) baseStart_8279670 baseEnd_8279670 := by
    simpa [prefixWord, tailWord_8279670, baseEnd_8279670] using wordTrace_append hprefix tailTrace_8279670
  have hstable : (prefixWord ++ tailWord_8279670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279670).length < 2 ^ (prefixWord ++ tailWord_8279670).sum := by decide
  have hdescent : baseEnd_8279670 < baseStart_8279670 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279734 : List Nat := [5, 1, 3, 1, 1, 1, 3, 3, 1, 4]
def baseStart_8279734 : Nat := 118140960795 + 8279734 * 2 ^ 59
def prefixEnd_8279734 : Nat := 4983230072969 + 3 ^ 40 * 8279734 * 2
def baseEnd_8279734 : Nat := 1417161077791204578782401

theorem tailTrace_8279734 : CollatzResearch.WordTrace tailWord_8279734 prefixEnd_8279734 1417161077791204578782401 := by
  unfold tailWord_8279734
  simp only [CollatzResearch.WordTrace]
  refine ⟨18874169261621578677047891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201324472123963505888510837 18874169261621578677047891)
  ·
    refine ⟨28311253892432368015571837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18874169261621578677047891 28311253892432368015571837)
    ·
      refine ⟨10616720209662138005839439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28311253892432368015571837 10616720209662138005839439)
      ·
        refine ⟨15925080314493207008759159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10616720209662138005839439 15925080314493207008759159)
        ·
          refine ⟨23887620471739810513138739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15925080314493207008759159 23887620471739810513138739)
          ·
            refine ⟨35831430707609715769708109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23887620471739810513138739 35831430707609715769708109)
            ·
              refine ⟨13436786515353643413640541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35831430707609715769708109 13436786515353643413640541)
              ·
                refine ⟨5038794943257616280115203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13436786515353643413640541 5038794943257616280115203)
                ·
                  refine ⟨7558192414886424420172805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5038794943257616280115203 7558192414886424420172805)
                  ·
                    refine ⟨1417161077791204578782401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7558192414886424420172805 1417161077791204578782401)
                    ·
                      rfl

theorem cell23_8279734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_8279734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279734 prefixEnd_8279734 := by exact prefixLift 8279734
  have htrace : WordTrace (prefixWord ++ tailWord_8279734) baseStart_8279734 baseEnd_8279734 := by
    simpa [prefixWord, tailWord_8279734, baseEnd_8279734] using wordTrace_append hprefix tailTrace_8279734
  have hstable : (prefixWord ++ tailWord_8279734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279734).length < 2 ^ (prefixWord ++ tailWord_8279734).sum := by decide
  have hdescent : baseEnd_8279734 < baseStart_8279734 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279776 : List Nat := [2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 6]
def baseStart_8279776 : Nat := 118140960795 + 8279776 * 2 ^ 59
def prefixEnd_8279776 : Nat := 4983230072969 + 3 ^ 40 * 8279776 * 2
def baseEnd_8279776 : Nat := 4251504799561102572022009

theorem tailTrace_8279776 : CollatzResearch.WordTrace tailWord_8279776 prefixEnd_8279776 4251504799561102572022009 := by
  unfold tailWord_8279776
  simp only [CollatzResearch.WordTrace]
  refine ⟨150994120025896550002897591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201325493367862066670530121 150994120025896550002897591)
  ·
    refine ⟨226491180038844825004346387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150994120025896550002897591 226491180038844825004346387)
    ·
      refine ⟨339736770058267237506519581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226491180038844825004346387 339736770058267237506519581)
      ·
        refine ⟨127401288771850214064944843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339736770058267237506519581 127401288771850214064944843)
        ·
          refine ⟨191101933157775321097417265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127401288771850214064944843 191101933157775321097417265)
          ·
            refine ⟨143326449868331490823062949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191101933157775321097417265 143326449868331490823062949)
            ·
              refine ⟨26873709350312154529324303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143326449868331490823062949 26873709350312154529324303)
              ·
                refine ⟨40310564025468231793986455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26873709350312154529324303 40310564025468231793986455)
                ·
                  refine ⟨60465846038202347690979683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40310564025468231793986455 60465846038202347690979683)
                  ·
                    refine ⟨90698769057303521536469525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60465846038202347690979683 90698769057303521536469525)
                    ·
                      refine ⟨4251504799561102572022009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90698769057303521536469525 4251504799561102572022009)
                      ·
                        rfl

theorem cell23_8279776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_8279776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279776 prefixEnd_8279776 := by exact prefixLift 8279776
  have htrace : WordTrace (prefixWord ++ tailWord_8279776) baseStart_8279776 baseEnd_8279776 := by
    simpa [prefixWord, tailWord_8279776, baseEnd_8279776] using wordTrace_append hprefix tailTrace_8279776
  have hstable : (prefixWord ++ tailWord_8279776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279776).length < 2 ^ (prefixWord ++ tailWord_8279776).sum := by decide
  have hdescent : baseEnd_8279776 < baseStart_8279776 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279777 : List Nat := [1, 2, 3, 1, 6, 1, 1, 2, 1, 5]
def baseStart_8279777 : Nat := 118140960795 + 8279777 * 2 ^ 59
def prefixEnd_8279777 : Nat := 4983230072969 + 3 ^ 40 * 8279777 * 2
def baseEnd_8279777 : Nat := 1417168437680585689369835

theorem tailTrace_8279777 : CollatzResearch.WordTrace tailWord_8279777 prefixEnd_8279777 1417168437680585689369835 := by
  unfold tailWord_8279777
  simp only [CollatzResearch.WordTrace]
  refine ⟨301988276524789477176581585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201325517683192984784387723 301988276524789477176581585)
  ·
    refine ⟨226491207393592107882436189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301988276524789477176581585 226491207393592107882436189)
    ·
      refine ⟨84934202772597040455913571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226491207393592107882436189 84934202772597040455913571)
      ·
        refine ⟨127401304158895560683870357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84934202772597040455913571 127401304158895560683870357)
        ·
          refine ⟨5971936132448229407056423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 127401304158895560683870357 5971936132448229407056423)
          ·
            refine ⟨8957904198672344110584635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5971936132448229407056423 8957904198672344110584635)
            ·
              refine ⟨13436856298008516165876953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8957904198672344110584635 13436856298008516165876953)
              ·
                refine ⟨10077642223506387124407715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13436856298008516165876953 10077642223506387124407715)
                ·
                  refine ⟨15116463335259580686611573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10077642223506387124407715 15116463335259580686611573)
                  ·
                    refine ⟨1417168437680585689369835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15116463335259580686611573 1417168437680585689369835)
                    ·
                      rfl

theorem cell23_8279777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_8279777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279777 prefixEnd_8279777 := by exact prefixLift 8279777
  have htrace : WordTrace (prefixWord ++ tailWord_8279777) baseStart_8279777 baseEnd_8279777 := by
    simpa [prefixWord, tailWord_8279777, baseEnd_8279777] using wordTrace_append hprefix tailTrace_8279777
  have hstable : (prefixWord ++ tailWord_8279777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279777).length < 2 ^ (prefixWord ++ tailWord_8279777).sum := by decide
  have hdescent : baseEnd_8279777 < baseStart_8279777 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279780 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 5, 2, 2]
def baseStart_8279780 : Nat := 118140960795 + 8279780 * 2 ^ 59
def prefixEnd_8279780 : Nat := 4983230072969 + 3 ^ 40 * 8279780 * 2
def baseEnd_8279780 : Nat := 4251506853483720556371991

theorem tailTrace_8279780 : CollatzResearch.WordTrace tailWord_8279780 prefixEnd_8279780 4251506853483720556371991 := by
  unfold tailWord_8279780
  simp only [CollatzResearch.WordTrace]
  refine ⟨150994192971889304344470397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201325590629185739125960529 150994192971889304344470397)
  ·
    refine ⟨56622822364458489129176399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150994192971889304344470397 56622822364458489129176399)
    ·
      refine ⟨84934233546687733693764599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56622822364458489129176399 84934233546687733693764599)
      ·
        refine ⟨127401350320031600540646899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84934233546687733693764599 127401350320031600540646899)
        ·
          refine ⟨191102025480047400810970349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127401350320031600540646899 191102025480047400810970349)
          ·
            refine ⟨71663259555017775304113881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191102025480047400810970349 71663259555017775304113881)
            ·
              refine ⟨53747444666263331478085411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71663259555017775304113881 53747444666263331478085411)
              ·
                refine ⟨80621166999394997217128117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53747444666263331478085411 80621166999394997217128117)
                ·
                  refine ⟨7558234406193280989105761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80621166999394997217128117 7558234406193280989105761)
                  ·
                    refine ⟨5668675804644960741829321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7558234406193280989105761 5668675804644960741829321)
                    ·
                      refine ⟨4251506853483720556371991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5668675804644960741829321 4251506853483720556371991)
                      ·
                        rfl

theorem cell23_8279780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 5, 2, 2].length) (baseStart_8279780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279780 prefixEnd_8279780 := by exact prefixLift 8279780
  have htrace : WordTrace (prefixWord ++ tailWord_8279780) baseStart_8279780 baseEnd_8279780 := by
    simpa [prefixWord, tailWord_8279780, baseEnd_8279780] using wordTrace_append hprefix tailTrace_8279780
  have hstable : (prefixWord ++ tailWord_8279780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279780).length < 2 ^ (prefixWord ++ tailWord_8279780).sum := by decide
  have hdescent : baseEnd_8279780 < baseStart_8279780 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279786 : List Nat := [3, 1, 3, 1, 1, 1, 4, 9]
def baseStart_8279786 : Nat := 118140960795 + 8279786 * 2 ^ 59
def prefixEnd_8279786 : Nat := 4983230072969 + 3 ^ 40 * 8279786 * 2
def baseEnd_8279786 : Nat := 157463330902505464181369

theorem tailTrace_8279786 : CollatzResearch.WordTrace tailWord_8279786 prefixEnd_8279786 157463330902505464181369 := by
  unfold tailWord_8279786
  simp only [CollatzResearch.WordTrace]
  refine ⟨75497151195439217928414803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201325736521171247809106141 75497151195439217928414803)
  ·
    refine ⟨113245726793158826892622205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75497151195439217928414803 113245726793158826892622205)
    ·
      refine ⟨42467147547434560084733327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113245726793158826892622205 42467147547434560084733327)
      ·
        refine ⟨63700721321151840127099991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42467147547434560084733327 63700721321151840127099991)
        ·
          refine ⟨95551081981727760190649987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63700721321151840127099991 95551081981727760190649987)
          ·
            refine ⟨143326622972591640285974981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95551081981727760190649987 143326622972591640285974981)
            ·
              refine ⟨26873741807360932553620309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143326622972591640285974981 26873741807360932553620309)
              ·
                refine ⟨157463330902505464181369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26873741807360932553620309 157463330902505464181369)
                ·
                  rfl

theorem cell23_8279786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 9].length) (baseStart_8279786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279786 prefixEnd_8279786 := by exact prefixLift 8279786
  have htrace : WordTrace (prefixWord ++ tailWord_8279786) baseStart_8279786 baseEnd_8279786 := by
    simpa [prefixWord, tailWord_8279786, baseEnd_8279786] using wordTrace_append hprefix tailTrace_8279786
  have hstable : (prefixWord ++ tailWord_8279786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279786).length < 2 ^ (prefixWord ++ tailWord_8279786).sum := by decide
  have hdescent : baseEnd_8279786 < baseStart_8279786 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279793 : List Nat := [1, 2, 2, 2, 2, 4, 1, 2, 1, 2, 4]
def baseStart_8279793 : Nat := 118140960795 + 8279793 * 2 ^ 59
def prefixEnd_8279793 : Nat := 4983230072969 + 3 ^ 40 * 8279793 * 2
def baseEnd_8279793 : Nat := 4251513528732229005509431

theorem tailTrace_8279793 : CollatzResearch.WordTrace tailWord_8279793 prefixEnd_8279793 4251513528732229005509431 := by
  unfold tailWord_8279793
  simp only [CollatzResearch.WordTrace]
  refine ⟨301988860092731511909164033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201325906728487674606109355 301988860092731511909164033)
  ·
    refine ⟨226491645069548633931873025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301988860092731511909164033 226491645069548633931873025)
    ·
      refine ⟨169868733802161475448904769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226491645069548633931873025 169868733802161475448904769)
      ·
        refine ⟨127401550351621106586678577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169868733802161475448904769 127401550351621106586678577)
        ·
          refine ⟨95551162763715829940008933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127401550351621106586678577 95551162763715829940008933)
          ·
            refine ⟨17915843018196718113751675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95551162763715829940008933 17915843018196718113751675)
            ·
              refine ⟨26873764527295077170627513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17915843018196718113751675 26873764527295077170627513)
              ·
                refine ⟨20155323395471307877970635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26873764527295077170627513 20155323395471307877970635)
                ·
                  refine ⟨30232985093206961816955953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20155323395471307877970635 30232985093206961816955953)
                  ·
                    refine ⟨22674738819905221362716965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30232985093206961816955953 22674738819905221362716965)
                    ·
                      refine ⟨4251513528732229005509431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22674738819905221362716965 4251513528732229005509431)
                      ·
                        rfl

theorem cell23_8279793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_8279793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279793 prefixEnd_8279793 := by exact prefixLift 8279793
  have htrace : WordTrace (prefixWord ++ tailWord_8279793) baseStart_8279793 baseEnd_8279793 := by
    simpa [prefixWord, tailWord_8279793, baseEnd_8279793] using wordTrace_append hprefix tailTrace_8279793
  have hstable : (prefixWord ++ tailWord_8279793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279793).length < 2 ^ (prefixWord ++ tailWord_8279793).sum := by decide
  have hdescent : baseEnd_8279793 < baseStart_8279793 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279816 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 1, 9]
def baseStart_8279816 : Nat := 118140960795 + 8279816 * 2 ^ 59
def prefixEnd_8279816 : Nat := 4983230072969 + 3 ^ 40 * 8279816 * 2
def baseEnd_8279816 : Nat := 1417175112929094138507275

theorem tailTrace_8279816 : CollatzResearch.WordTrace tailWord_8279816 prefixEnd_8279816 1417175112929094138507275 := by
  unfold tailWord_8279816
  simp only [CollatzResearch.WordTrace]
  refine ⟨150994849485824093418625651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201326465981098791224834201 150994849485824093418625651)
  ·
    refine ⟨226492274228736140127938477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150994849485824093418625651 226492274228736140127938477)
    ·
      refine ⟨84934602835776052547976929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226492274228736140127938477 84934602835776052547976929)
      ·
        refine ⟨63700952126832039410982697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84934602835776052547976929 63700952126832039410982697)
        ·
          refine ⟨47775714095124029558237023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63700952126832039410982697 47775714095124029558237023)
          ·
            refine ⟨71663571142686044337355535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47775714095124029558237023 71663571142686044337355535)
            ·
              refine ⟨107495356714029066506033303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71663571142686044337355535 107495356714029066506033303)
              ·
                refine ⟨161243035071043599759049955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107495356714029066506033303 161243035071043599759049955)
                ·
                  refine ⟨241864552606565399638574933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161243035071043599759049955 241864552606565399638574933)
                  ·
                    refine ⟨1417175112929094138507275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 241864552606565399638574933 1417175112929094138507275)
                    ·
                      rfl

theorem cell23_8279816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_8279816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279816 prefixEnd_8279816 := by exact prefixLift 8279816
  have htrace : WordTrace (prefixWord ++ tailWord_8279816) baseStart_8279816 baseEnd_8279816 := by
    simpa [prefixWord, tailWord_8279816, baseEnd_8279816] using wordTrace_append hprefix tailTrace_8279816
  have hstable : (prefixWord ++ tailWord_8279816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279816).length < 2 ^ (prefixWord ++ tailWord_8279816).sum := by decide
  have hdescent : baseEnd_8279816 < baseStart_8279816 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279840 : List Nat := [2, 1, 1, 5, 1, 1, 1, 3, 3, 3, 2]
def baseStart_8279840 : Nat := 118140960795 + 8279840 * 2 ^ 59
def prefixEnd_8279840 : Nat := 4983230072969 + 3 ^ 40 * 8279840 * 2
def baseEnd_8279840 : Nat := 4251537662322990321621715

theorem tailTrace_8279840 : CollatzResearch.WordTrace tailWord_8279840 prefixEnd_8279840 4251537662322990321621715 := by
  unfold tailWord_8279840
  simp only [CollatzResearch.WordTrace]
  refine ⟨150995287161780619468062487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201327049549040825957416649 150995287161780619468062487)
  ·
    refine ⟨226492930742670929202093731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150995287161780619468062487 226492930742670929202093731)
    ·
      refine ⟨339739396114006393803140597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226492930742670929202093731 339739396114006393803140597)
      ·
        refine ⟨31850568385688099419044431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 339739396114006393803140597 31850568385688099419044431)
        ·
          refine ⟨47775852578532149128566647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31850568385688099419044431 47775852578532149128566647)
          ·
            refine ⟨71663778867798223692849971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47775852578532149128566647 71663778867798223692849971)
            ·
              refine ⟨107495668301697335539274957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71663778867798223692849971 107495668301697335539274957)
              ·
                refine ⟨40310875613136500827228109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107495668301697335539274957 40310875613136500827228109)
                ·
                  refine ⟨15116578354926187810210541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40310875613136500827228109 15116578354926187810210541)
                  ·
                    refine ⟨5668716883097320428828953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15116578354926187810210541 5668716883097320428828953)
                    ·
                      refine ⟨4251537662322990321621715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5668716883097320428828953 4251537662322990321621715)
                      ·
                        rfl

theorem cell23_8279840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_8279840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279840 prefixEnd_8279840 := by exact prefixLift 8279840
  have htrace : WordTrace (prefixWord ++ tailWord_8279840) baseStart_8279840 baseEnd_8279840 := by
    simpa [prefixWord, tailWord_8279840, baseEnd_8279840] using wordTrace_append hprefix tailTrace_8279840
  have hstable : (prefixWord ++ tailWord_8279840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279840).length < 2 ^ (prefixWord ++ tailWord_8279840).sum := by decide
  have hdescent : baseEnd_8279840 < baseStart_8279840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279857 : List Nat := [1, 2, 2, 3, 2, 3, 1, 3, 1, 3, 2]
def baseStart_8279857 : Nat := 118140960795 + 8279857 * 2 ^ 59
def prefixEnd_8279857 : Nat := 4983230072969 + 3 ^ 40 * 8279857 * 2
def baseEnd_8279857 : Nat := 4251546391494116755109137

theorem tailTrace_8279857 : CollatzResearch.WordTrace tailWord_8279857 prefixEnd_8279857 4251546391494116755109137 := by
  unfold tailWord_8279857
  simp only [CollatzResearch.WordTrace]
  refine ⟨301991194364499650839493825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201327462909666433892995883 301991194364499650839493825)
  ·
    refine ⟨226493395773374738129620369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301991194364499650839493825 226493395773374738129620369)
    ·
      refine ⟨169870046830031053597215277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226493395773374738129620369 169870046830031053597215277)
      ·
        refine ⟨63701267561261645098955729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169870046830031053597215277 63701267561261645098955729)
        ·
          refine ⟨47775950670946233824216797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63701267561261645098955729 47775950670946233824216797)
          ·
            refine ⟨17915981501604837684081299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47775950670946233824216797 17915981501604837684081299)
            ·
              refine ⟨26873972252407256526121949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17915981501604837684081299 26873972252407256526121949)
              ·
                refine ⟨10077739594652721197295731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26873972252407256526121949 10077739594652721197295731)
                ·
                  refine ⟨15116609391979081795943597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10077739594652721197295731 15116609391979081795943597)
                  ·
                    refine ⟨5668728521992155673478849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15116609391979081795943597 5668728521992155673478849)
                    ·
                      refine ⟨4251546391494116755109137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5668728521992155673478849 4251546391494116755109137)
                      ·
                        rfl

theorem cell23_8279857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_8279857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279857 prefixEnd_8279857 := by exact prefixLift 8279857
  have htrace : WordTrace (prefixWord ++ tailWord_8279857) baseStart_8279857 baseEnd_8279857 := by
    simpa [prefixWord, tailWord_8279857, baseEnd_8279857] using wordTrace_append hprefix tailTrace_8279857
  have hstable : (prefixWord ++ tailWord_8279857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279857).length < 2 ^ (prefixWord ++ tailWord_8279857).sum := by decide
  have hdescent : baseEnd_8279857 < baseStart_8279857 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279893 : List Nat := [1, 3, 2, 2, 2, 2, 2, 2, 7]
def baseStart_8279893 : Nat := 118140960795 + 8279893 * 2 ^ 59
def prefixEnd_8279893 : Nat := 4983230072969 + 3 ^ 40 * 8279893 * 2
def baseEnd_8279893 : Nat := 472396097421964290473219

theorem tailTrace_8279893 : CollatzResearch.WordTrace tailWord_8279893 prefixEnd_8279893 472396097421964290473219 := by
  unfold tailWord_8279893
  simp only [CollatzResearch.WordTrace]
  refine ⟨301992507392369228987804333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201328338261579485991869555 301992507392369228987804333)
  ·
    refine ⟨113247190272138460870426625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301992507392369228987804333 113247190272138460870426625)
    ·
      refine ⟨84935392704103845652819969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113247190272138460870426625 84935392704103845652819969)
      ·
        refine ⟨63701544528077884239614977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84935392704103845652819969 63701544528077884239614977)
        ·
          refine ⟨47776158396058413179711233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63701544528077884239614977 47776158396058413179711233)
          ·
            refine ⟨35832118797043809884783425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47776158396058413179711233 35832118797043809884783425)
            ·
              refine ⟨26874089097782857413587569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35832118797043809884783425 26874089097782857413587569)
              ·
                refine ⟨20155566823337143060190677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26874089097782857413587569 20155566823337143060190677)
                ·
                  refine ⟨472396097421964290473219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20155566823337143060190677 472396097421964290473219)
                  ·
                    rfl

theorem cell23_8279893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 7].length) (baseStart_8279893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279893 prefixEnd_8279893 := by exact prefixLift 8279893
  have htrace : WordTrace (prefixWord ++ tailWord_8279893) baseStart_8279893 baseEnd_8279893 := by
    simpa [prefixWord, tailWord_8279893, baseEnd_8279893] using wordTrace_append hprefix tailTrace_8279893
  have hstable : (prefixWord ++ tailWord_8279893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279893).length < 2 ^ (prefixWord ++ tailWord_8279893).sum := by decide
  have hdescent : baseEnd_8279893 < baseStart_8279893 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8279987 : List Nat := [1, 1, 1, 2, 3, 1, 5, 4, 1, 4]
def baseStart_8279987 : Nat := 118140960795 + 8279987 * 2 ^ 59
def prefixEnd_8279987 : Nat := 4983230072969 + 3 ^ 40 * 8279987 * 2
def baseEnd_8279987 : Nat := 1417204381326400415494513

theorem tailTrace_8279987 : CollatzResearch.WordTrace tailWord_8279987 prefixEnd_8279987 1417204381326400415494513 := by
  unfold tailWord_8279987
  simp only [CollatzResearch.WordTrace]
  refine ⟨301995935854028683041726215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201330623902685788694484143 301995935854028683041726215)
  ·
    refine ⟨452993903781043024562589323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301995935854028683041726215 452993903781043024562589323)
    ·
      refine ⟨679490855671564536843883985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452993903781043024562589323 679490855671564536843883985)
      ·
        refine ⟨509618141753673402632912989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 679490855671564536843883985 509618141753673402632912989)
        ·
          refine ⟨191106803157627525987342371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 509618141753673402632912989 191106803157627525987342371)
          ·
            refine ⟨286660204736441288981013557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191106803157627525987342371 286660204736441288981013557)
            ·
              refine ⟨26874394194041370841970021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 286660204736441288981013557 26874394194041370841970021)
              ·
                refine ⟨5038948911382757032869379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26874394194041370841970021 5038948911382757032869379)
                ·
                  refine ⟨7558423367074135549304069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5038948911382757032869379 7558423367074135549304069)
                  ·
                    refine ⟨1417204381326400415494513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7558423367074135549304069 1417204381326400415494513)
                    ·
                      rfl

theorem cell23_8279987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4, 1, 4].length) (baseStart_8279987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8279987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8279987 prefixEnd_8279987 := by exact prefixLift 8279987
  have htrace : WordTrace (prefixWord ++ tailWord_8279987) baseStart_8279987 baseEnd_8279987 := by
    simpa [prefixWord, tailWord_8279987, baseEnd_8279987] using wordTrace_append hprefix tailTrace_8279987
  have hstable : (prefixWord ++ tailWord_8279987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8279987).length < 2 ^ (prefixWord ++ tailWord_8279987).sum := by decide
  have hdescent : baseEnd_8279987 < baseStart_8279987 := by decide
  rcases family_descends (prefixWord ++ tailWord_8279987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280043 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 3, 6]
def baseStart_8280043 : Nat := 118140960795 + 8280043 * 2 ^ 59
def prefixEnd_8280043 : Nat := 4983230072969 + 3 ^ 40 * 8280043 * 2
def baseEnd_8280043 : Nat := 1417213966298617675794427

theorem tailTrace_8280043 : CollatzResearch.WordTrace tailWord_8280043 prefixEnd_8280043 1417213966298617675794427 := by
  unfold tailWord_8280043
  simp only [CollatzResearch.WordTrace]
  refine ⟨301997978341825804605764783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201331985561217203070509855 301997978341825804605764783)
  ·
    refine ⟨452996967512738706908647175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301997978341825804605764783 452996967512738706908647175)
    ·
      refine ⟨679495451269108060362970763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452996967512738706908647175 679495451269108060362970763)
      ·
        refine ⟨1019243176903662090544456145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679495451269108060362970763 1019243176903662090544456145)
        ·
          refine ⟨764432382677746567908342109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1019243176903662090544456145 764432382677746567908342109)
          ·
            refine ⟨286662143504154962965628291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 764432382677746567908342109 286662143504154962965628291)
            ·
              refine ⟨429993215256232444448442437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286662143504154962965628291 429993215256232444448442437)
              ·
                refine ⟨80623727860543583334082957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 429993215256232444448442437 80623727860543583334082957)
                ·
                  refine ⟨30233897947703843750281109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80623727860543583334082957 30233897947703843750281109)
                  ·
                    refine ⟨1417213966298617675794427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30233897947703843750281109 1417213966298617675794427)
                    ·
                      rfl

theorem cell23_8280043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 6].length) (baseStart_8280043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280043 prefixEnd_8280043 := by exact prefixLift 8280043
  have htrace : WordTrace (prefixWord ++ tailWord_8280043) baseStart_8280043 baseEnd_8280043 := by
    simpa [prefixWord, tailWord_8280043, baseEnd_8280043] using wordTrace_append hprefix tailTrace_8280043
  have hstable : (prefixWord ++ tailWord_8280043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280043).length < 2 ^ (prefixWord ++ tailWord_8280043).sum := by decide
  have hdescent : baseEnd_8280043 < baseStart_8280043 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280090 : List Nat := [3, 1, 1, 3, 1, 5, 9]
def baseStart_8280090 : Nat := 118140960795 + 8280090 * 2 ^ 59
def prefixEnd_8280090 : Nat := 4983230072969 + 3 ^ 40 * 8280090 * 2
def baseEnd_8280090 : Nat := 52489704104773016586365

theorem tailTrace_8280090 : CollatzResearch.WordTrace tailWord_8280090 prefixEnd_8280090 52489704104773016586365 := by
  unfold tailWord_8280090
  simp only [CollatzResearch.WordTrace]
  refine ⟨75499923143163882908181431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201333128381770354421817149 75499923143163882908181431)
  ·
    refine ⟨113249884714745824362272147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75499923143163882908181431 113249884714745824362272147)
    ·
      refine ⟨169874827072118736543408221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113249884714745824362272147 169874827072118736543408221)
      ·
        refine ⟨63703060152044526203778083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169874827072118736543408221 63703060152044526203778083)
        ·
          refine ⟨95554590228066789305667125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63703060152044526203778083 95554590228066789305667125)
          ·
            refine ⟨8958242833881261497406293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95554590228066789305667125 8958242833881261497406293)
            ·
              refine ⟨52489704104773016586365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8958242833881261497406293 52489704104773016586365)
              ·
                rfl

theorem cell23_8280090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 9].length) (baseStart_8280090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280090 prefixEnd_8280090 := by exact prefixLift 8280090
  have htrace : WordTrace (prefixWord ++ tailWord_8280090) baseStart_8280090 baseEnd_8280090 := by
    simpa [prefixWord, tailWord_8280090, baseEnd_8280090] using wordTrace_append hprefix tailTrace_8280090
  have hstable : (prefixWord ++ tailWord_8280090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280090).length < 2 ^ (prefixWord ++ tailWord_8280090).sum := by decide
  have hdescent : baseEnd_8280090 < baseStart_8280090 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280101 : List Nat := [1, 3, 1, 2, 2, 5, 1, 1, 3, 2, 2]
def baseStart_8280101 : Nat := 118140960795 + 8280101 * 2 ^ 59
def prefixEnd_8280101 : Nat := 4983230072969 + 3 ^ 40 * 8280101 * 2
def baseEnd_8280101 : Nat := 4251671680773813800458015

theorem tailTrace_8280101 : CollatzResearch.WordTrace tailWord_8280101 prefixEnd_8280101 4251671680773813800458015 := by
  unfold tailWord_8280101
  simp only [CollatzResearch.WordTrace]
  refine ⟨302000093775615680511376157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201333395850410453674250771 302000093775615680511376157)
  ·
    refine ⟨113250035165855880191766059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302000093775615680511376157 113250035165855880191766059)
    ·
      refine ⟨169875052748783820287649089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113250035165855880191766059 169875052748783820287649089)
      ·
        refine ⟨127406289561587865215736817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169875052748783820287649089 127406289561587865215736817)
        ·
          refine ⟨95554717171190898911802613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127406289561587865215736817 95554717171190898911802613)
          ·
            refine ⟨8958254734799146772981495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95554717171190898911802613 8958254734799146772981495)
            ·
              refine ⟨13437382102198720159472243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8958254734799146772981495 13437382102198720159472243)
              ·
                refine ⟨20156073153298080239208365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13437382102198720159472243 20156073153298080239208365)
                ·
                  refine ⟨7558527432486780089703137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20156073153298080239208365 7558527432486780089703137)
                  ·
                    refine ⟨5668895574365085067277353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7558527432486780089703137 5668895574365085067277353)
                    ·
                      refine ⟨4251671680773813800458015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5668895574365085067277353 4251671680773813800458015)
                      ·
                        rfl

theorem cell23_8280101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3, 2, 2].length) (baseStart_8280101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280101 prefixEnd_8280101 := by exact prefixLift 8280101
  have htrace : WordTrace (prefixWord ++ tailWord_8280101) baseStart_8280101 baseEnd_8280101 := by
    simpa [prefixWord, tailWord_8280101, baseEnd_8280101] using wordTrace_append hprefix tailTrace_8280101
  have hstable : (prefixWord ++ tailWord_8280101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280101).length < 2 ^ (prefixWord ++ tailWord_8280101).sum := by decide
  have hdescent : baseEnd_8280101 < baseStart_8280101 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280121 : List Nat := [1, 2, 1, 5, 3, 2, 1, 2, 1, 2, 3]
def baseStart_8280121 : Nat := 118140960795 + 8280121 * 2 ^ 59
def prefixEnd_8280121 : Nat := 4983230072969 + 3 ^ 40 * 8280121 * 2
def baseEnd_8280121 : Nat := 4251681950386903722207923

theorem tailTrace_8280121 : CollatzResearch.WordTrace tailWord_8280121 prefixEnd_8280121 4251681950386903722207923 := by
  unfold tailWord_8280121
  simp only [CollatzResearch.WordTrace]
  refine ⟨302000823235543223927104217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201333882157028815951402811 302000823235543223927104217)
  ·
    refine ⟨226500617426657417945328163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302000823235543223927104217 226500617426657417945328163)
    ·
      refine ⟨339750926139986126917992245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226500617426657417945328163 339750926139986126917992245)
      ·
        refine ⟨31851649325623699398561773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 339750926139986126917992245 31851649325623699398561773)
        ·
          refine ⟨11944368497108887274460665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31851649325623699398561773 11944368497108887274460665)
          ·
            refine ⟨8958276372831665455845499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11944368497108887274460665 8958276372831665455845499)
            ·
              refine ⟨13437414559247498183768249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8958276372831665455845499 13437414559247498183768249)
              ·
                refine ⟨10078060919435623637826187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13437414559247498183768249 10078060919435623637826187)
                ·
                  refine ⟨15117091379153435456739281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10078060919435623637826187 15117091379153435456739281)
                  ·
                    refine ⟨11337818534365076592554461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15117091379153435456739281 11337818534365076592554461)
                    ·
                      refine ⟨4251681950386903722207923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11337818534365076592554461 4251681950386903722207923)
                      ·
                        rfl

theorem cell23_8280121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_8280121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280121 prefixEnd_8280121 := by exact prefixLift 8280121
  have htrace : WordTrace (prefixWord ++ tailWord_8280121) baseStart_8280121 baseEnd_8280121 := by
    simpa [prefixWord, tailWord_8280121, baseEnd_8280121] using wordTrace_append hprefix tailTrace_8280121
  have hstable : (prefixWord ++ tailWord_8280121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280121).length < 2 ^ (prefixWord ++ tailWord_8280121).sum := by decide
  have hdescent : baseEnd_8280121 < baseStart_8280121 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280158 : List Nat := [4, 4, 1, 1, 3, 1, 1, 8]
def baseStart_8280158 : Nat := 118140960795 + 8280158 * 2 ^ 59
def prefixEnd_8280158 : Nat := 4983230072969 + 3 ^ 40 * 8280158 * 2
def baseEnd_8280158 : Nat := 157470405524856299164639

theorem tailTrace_8280158 : CollatzResearch.WordTrace tailWord_8280158 prefixEnd_8280158 157470405524856299164639 := by
  unfold tailWord_8280158
  simp only [CollatzResearch.WordTrace]
  refine ⟨37750271592051147405775141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201334781824272786164134085 37750271592051147405775141)
  ·
    refine ⟨7078175923509590138582839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37750271592051147405775141 7078175923509590138582839)
    ·
      refine ⟨10617263885264385207874259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7078175923509590138582839 10617263885264385207874259)
      ·
        refine ⟨15925895827896577811811389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10617263885264385207874259 15925895827896577811811389)
        ·
          refine ⟨5972210935461216679429271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15925895827896577811811389 5972210935461216679429271)
          ·
            refine ⟨8958316403191825019143907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5972210935461216679429271 8958316403191825019143907)
            ·
              refine ⟨13437474604787737528715861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8958316403191825019143907 13437474604787737528715861)
              ·
                refine ⟨157470405524856299164639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13437474604787737528715861 157470405524856299164639)
                ·
                  rfl

theorem cell23_8280158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 8].length) (baseStart_8280158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280158 prefixEnd_8280158 := by exact prefixLift 8280158
  have htrace : WordTrace (prefixWord ++ tailWord_8280158) baseStart_8280158 baseEnd_8280158 := by
    simpa [prefixWord, tailWord_8280158, baseEnd_8280158] using wordTrace_append hprefix tailTrace_8280158
  have hstable : (prefixWord ++ tailWord_8280158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280158).length < 2 ^ (prefixWord ++ tailWord_8280158).sum := by decide
  have hdescent : baseEnd_8280158 < baseStart_8280158 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280217 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 1, 7, 2]
def baseStart_8280217 : Nat := 118140960795 + 8280217 * 2 ^ 59
def prefixEnd_8280217 : Nat := 4983230072969 + 3 ^ 40 * 8280217 * 2
def baseEnd_8280217 : Nat := 4251731244529735346607481

theorem tailTrace_8280217 : CollatzResearch.WordTrace tailWord_8280217 prefixEnd_8280217 4251731244529735346607481 := by
  unfold tailWord_8280217
  simp only [CollatzResearch.WordTrace]
  refine ⟨302004324643195432322598905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201336216428796954881732603 302004324643195432322598905)
  ·
    refine ⟨226503243482396574241949179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302004324643195432322598905 226503243482396574241949179)
    ·
      refine ⟨339754865223594861362923769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226503243482396574241949179 339754865223594861362923769)
      ·
        refine ⟨254816148917696146022192827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339754865223594861362923769 254816148917696146022192827)
        ·
          refine ⟨382224223376544219033289241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254816148917696146022192827 382224223376544219033289241)
          ·
            refine ⟨286668167532408164274966931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382224223376544219033289241 286668167532408164274966931)
            ·
              refine ⟨430002251298612246412450397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286668167532408164274966931 430002251298612246412450397)
              ·
                refine ⟨161250844236979592404668899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 430002251298612246412450397 161250844236979592404668899)
                ·
                  refine ⟨241876266355469388607003349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161250844236979592404668899 241876266355469388607003349)
                  ·
                    refine ⟨5668974992706313795476641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 241876266355469388607003349 5668974992706313795476641)
                    ·
                      refine ⟨4251731244529735346607481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5668974992706313795476641 4251731244529735346607481)
                      ·
                        rfl

theorem cell23_8280217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 7, 2].length) (baseStart_8280217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280217 prefixEnd_8280217 := by exact prefixLift 8280217
  have htrace : WordTrace (prefixWord ++ tailWord_8280217) baseStart_8280217 baseEnd_8280217 := by
    simpa [prefixWord, tailWord_8280217, baseEnd_8280217] using wordTrace_append hprefix tailTrace_8280217
  have hstable : (prefixWord ++ tailWord_8280217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280217).length < 2 ^ (prefixWord ++ tailWord_8280217).sum := by decide
  have hdescent : baseEnd_8280217 < baseStart_8280217 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280247 : List Nat := [1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 4]
def baseStart_8280247 : Nat := 118140960795 + 8280247 * 2 ^ 59
def prefixEnd_8280247 : Nat := 4983230072969 + 3 ^ 40 * 8280247 * 2
def baseEnd_8280247 : Nat := 4251746648949370229232343

theorem tailTrace_8280247 : CollatzResearch.WordTrace tailWord_8280247 prefixEnd_8280247 4251746648949370229232343 := by
  unfold tailWord_8280247
  simp only [CollatzResearch.WordTrace]
  refine ⟨302005418833086747446190995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201336945888724498297460663 302005418833086747446190995)
  ·
    refine ⟨453008128249630121169286493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302005418833086747446190995 453008128249630121169286493)
    ·
      refine ⟨169878048093611295438482435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 453008128249630121169286493 169878048093611295438482435)
      ·
        refine ⟨254817072140416943157723653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169878048093611295438482435 254817072140416943157723653)
        ·
          refine ⟨47778201026328176842073185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254817072140416943157723653 47778201026328176842073185)
          ·
            refine ⟨35833650769746132631554889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47778201026328176842073185 35833650769746132631554889)
            ·
              refine ⟨26875238077309599473666167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35833650769746132631554889 26875238077309599473666167)
              ·
                refine ⟨40312857115964399210499251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26875238077309599473666167 40312857115964399210499251)
                ·
                  refine ⟨60469285673946598815748877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40312857115964399210499251 60469285673946598815748877)
                  ·
                    refine ⟨22675982127729974555905829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60469285673946598815748877 22675982127729974555905829)
                    ·
                      refine ⟨4251746648949370229232343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22675982127729974555905829 4251746648949370229232343)
                      ·
                        rfl

theorem cell23_8280247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_8280247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280247 prefixEnd_8280247 := by exact prefixLift 8280247
  have htrace : WordTrace (prefixWord ++ tailWord_8280247) baseStart_8280247 baseEnd_8280247 := by
    simpa [prefixWord, tailWord_8280247, baseEnd_8280247] using wordTrace_append hprefix tailTrace_8280247
  have hstable : (prefixWord ++ tailWord_8280247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280247).length < 2 ^ (prefixWord ++ tailWord_8280247).sum := by decide
  have hdescent : baseEnd_8280247 < baseStart_8280247 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280347 : List Nat := [1, 1, 1, 1, 1, 1, 7, 3, 1, 6]
def baseStart_8280347 : Nat := 118140960795 + 8280347 * 2 ^ 59
def prefixEnd_8280347 : Nat := 4983230072969 + 3 ^ 40 * 8280347 * 2
def baseEnd_8280347 : Nat := 1417265999004939945993961

theorem tailTrace_8280347 : CollatzResearch.WordTrace tailWord_8280347 prefixEnd_8280347 1417265999004939945993961 := by
  unfold tailWord_8280347
  simp only [CollatzResearch.WordTrace]
  refine ⟨302009066132724464524831295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201339377421816309683220863 302009066132724464524831295)
  ·
    refine ⟨453013599199086696787246943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302009066132724464524831295 453013599199086696787246943)
    ·
      refine ⟨679520398798630045180870415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453013599199086696787246943 679520398798630045180870415)
      ·
        refine ⟨1019280598197945067771305623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679520398798630045180870415 1019280598197945067771305623)
        ·
          refine ⟨1528920897296917601656958435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1019280598197945067771305623 1528920897296917601656958435)
          ·
            refine ⟨2293381345945376402485437653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1528920897296917601656958435 2293381345945376402485437653)
            ·
              refine ⟨53751125295594759433252445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2293381345945376402485437653 53751125295594759433252445)
              ·
                refine ⟨20156671985848034787469667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53751125295594759433252445 20156671985848034787469667)
                ·
                  refine ⟨30235007978772052181204501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20156671985848034787469667 30235007978772052181204501)
                  ·
                    refine ⟨1417265999004939945993961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30235007978772052181204501 1417265999004939945993961)
                    ·
                      rfl

theorem cell23_8280347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 6].length) (baseStart_8280347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280347 prefixEnd_8280347 := by exact prefixLift 8280347
  have htrace : WordTrace (prefixWord ++ tailWord_8280347) baseStart_8280347 baseEnd_8280347 := by
    simpa [prefixWord, tailWord_8280347, baseEnd_8280347] using wordTrace_append hprefix tailTrace_8280347
  have hstable : (prefixWord ++ tailWord_8280347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280347).length < 2 ^ (prefixWord ++ tailWord_8280347).sum := by decide
  have hdescent : baseEnd_8280347 < baseStart_8280347 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280371 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 5, 2, 2]
def baseStart_8280371 : Nat := 118140960795 + 8280371 * 2 ^ 59
def prefixEnd_8280371 : Nat := 4983230072969 + 3 ^ 40 * 8280371 * 2
def baseEnd_8280371 : Nat := 4251810320550527744081773

theorem tailTrace_8280371 : CollatzResearch.WordTrace tailWord_8280371 prefixEnd_8280371 4251810320550527744081773 := by
  unfold tailWord_8280371
  simp only [CollatzResearch.WordTrace]
  refine ⟨302009941484637516623704967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201339960989758344415803311 302009941484637516623704967)
  ·
    refine ⟨453014912226956274935557451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302009941484637516623704967 453014912226956274935557451)
    ·
      refine ⟨679522368340434412403336177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453014912226956274935557451 679522368340434412403336177)
      ·
        refine ⟨509641776255325809302502133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 679522368340434412403336177 509641776255325809302502133)
        ·
          refine ⟨47778916523936794622109575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 509641776255325809302502133 47778916523936794622109575)
          ·
            refine ⟨71668374785905191933164363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47778916523936794622109575 71668374785905191933164363)
            ·
              refine ⟨107502562178857787899746545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71668374785905191933164363 107502562178857787899746545)
              ·
                refine ⟨80626921634143340924809909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107502562178857787899746545 80626921634143340924809909)
                ·
                  refine ⟨7558773903200938211700929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80626921634143340924809909 7558773903200938211700929)
                  ·
                    refine ⟨5669080427400703658775697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7558773903200938211700929 5669080427400703658775697)
                    ·
                      refine ⟨4251810320550527744081773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5669080427400703658775697 4251810320550527744081773)
                      ·
                        rfl

theorem cell23_8280371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5, 2, 2].length) (baseStart_8280371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280371 prefixEnd_8280371 := by exact prefixLift 8280371
  have htrace : WordTrace (prefixWord ++ tailWord_8280371) baseStart_8280371 baseEnd_8280371 := by
    simpa [prefixWord, tailWord_8280371, baseEnd_8280371] using wordTrace_append hprefix tailTrace_8280371
  have hstable : (prefixWord ++ tailWord_8280371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280371).length < 2 ^ (prefixWord ++ tailWord_8280371).sum := by decide
  have hdescent : baseEnd_8280371 < baseStart_8280371 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280401 : List Nat := [1, 2, 2, 1, 4, 4, 1, 1, 1, 2, 4]
def baseStart_8280401 : Nat := 118140960795 + 8280401 * 2 ^ 59
def prefixEnd_8280401 : Nat := 4983230072969 + 3 ^ 40 * 8280401 * 2
def baseEnd_8280401 : Nat := 4251825724970162626706635

theorem tailTrace_8280401 : CollatzResearch.WordTrace tailWord_8280401 prefixEnd_8280401 4251825724970162626706635 := by
  unfold tailWord_8280401
  simp only [CollatzResearch.WordTrace]
  refine ⟨302011035674528831747297057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201340690449685887831531371 302011035674528831747297057)
  ·
    refine ⟨226508276755896623810472793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302011035674528831747297057 226508276755896623810472793)
    ·
      refine ⟨169881207566922467857854595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226508276755896623810472793 169881207566922467857854595)
      ·
        refine ⟨254821811350383701786781893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169881207566922467857854595 254821811350383701786781893)
        ·
          refine ⟨47779089628196944085021605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254821811350383701786781893 47779089628196944085021605)
          ·
            refine ⟨8958579305286927015941551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47779089628196944085021605 8958579305286927015941551)
            ·
              refine ⟨13437868957930390523912327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8958579305286927015941551 13437868957930390523912327)
              ·
                refine ⟨20156803436895585785868491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13437868957930390523912327 20156803436895585785868491)
                ·
                  refine ⟨30235205155343378678802737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20156803436895585785868491 30235205155343378678802737)
                  ·
                    refine ⟨22676403866507534009102053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30235205155343378678802737 22676403866507534009102053)
                    ·
                      refine ⟨4251825724970162626706635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22676403866507534009102053 4251825724970162626706635)
                      ·
                        rfl

theorem cell23_8280401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 2, 4].length) (baseStart_8280401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280401 prefixEnd_8280401 := by exact prefixLift 8280401
  have htrace : WordTrace (prefixWord ++ tailWord_8280401) baseStart_8280401 baseEnd_8280401 := by
    simpa [prefixWord, tailWord_8280401, baseEnd_8280401] using wordTrace_append hprefix tailTrace_8280401
  have hstable : (prefixWord ++ tailWord_8280401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280401).length < 2 ^ (prefixWord ++ tailWord_8280401).sum := by decide
  have hdescent : baseEnd_8280401 < baseStart_8280401 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280421 : List Nat := [1, 3, 1, 3, 1, 3, 1, 2, 4, 1, 3]
def baseStart_8280421 : Nat := 118140960795 + 8280421 * 2 ^ 59
def prefixEnd_8280421 : Nat := 4983230072969 + 3 ^ 40 * 8280421 * 2
def baseEnd_8280421 : Nat := 4251835994583252548456543

theorem tailTrace_8280421 : CollatzResearch.WordTrace tailWord_8280421 prefixEnd_8280421 4251835994583252548456543 := by
  unfold tailWord_8280421
  simp only [CollatzResearch.WordTrace]
  refine ⟨302011765134456375163025117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201341176756304250108683411 302011765134456375163025117)
  ·
    refine ⟨113254411925421140686134419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302011765134456375163025117 113254411925421140686134419)
    ·
      refine ⟨169881617888131711029201629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113254411925421140686134419 169881617888131711029201629)
      ·
        refine ⟨63705606708049391635950611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169881617888131711029201629 63705606708049391635950611)
        ·
          refine ⟨95558410062074087453925917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63705606708049391635950611 95558410062074087453925917)
          ·
            refine ⟨35834403773277782795222219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95558410062074087453925917 35834403773277782795222219)
            ·
              refine ⟨53751605659916674192833329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35834403773277782795222219 53751605659916674192833329)
              ·
                refine ⟨40313704244937505644624997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53751605659916674192833329 40313704244937505644624997)
                ·
                  refine ⟨7558819545925782308367187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40313704244937505644624997 7558819545925782308367187)
                  ·
                    refine ⟨11338229318888673462550781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7558819545925782308367187 11338229318888673462550781)
                    ·
                      refine ⟨4251835994583252548456543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11338229318888673462550781 4251835994583252548456543)
                      ·
                        rfl

theorem cell23_8280421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_8280421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280421 prefixEnd_8280421 := by exact prefixLift 8280421
  have htrace : WordTrace (prefixWord ++ tailWord_8280421) baseStart_8280421 baseEnd_8280421 := by
    simpa [prefixWord, tailWord_8280421, baseEnd_8280421] using wordTrace_append hprefix tailTrace_8280421
  have hstable : (prefixWord ++ tailWord_8280421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280421).length < 2 ^ (prefixWord ++ tailWord_8280421).sum := by decide
  have hdescent : baseEnd_8280421 < baseStart_8280421 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280490 : List Nat := [3, 1, 6, 1, 2, 1, 2, 2, 1, 2, 2]
def baseStart_8280490 : Nat := 118140960795 + 8280490 * 2 ^ 59
def prefixEnd_8280490 : Nat := 4983230072969 + 3 ^ 40 * 8280490 * 2
def baseEnd_8280490 : Nat := 4251871424748412778493727

theorem tailTrace_8280490 : CollatzResearch.WordTrace tailWord_8280490 prefixEnd_8280490 4251871424748412778493727 := by
  unfold tailWord_8280490
  simp only [CollatzResearch.WordTrace]
  refine ⟨75503570442801599986821731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201342854514137599964857949 75503570442801599986821731)
  ·
    refine ⟨113255355664202399980232597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75503570442801599986821731 113255355664202399980232597)
    ·
      refine ⟨5308844796759487499073403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113255355664202399980232597 5308844796759487499073403)
      ·
        refine ⟨7963267195139231248610105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5308844796759487499073403 7963267195139231248610105)
        ·
          refine ⟨5972450396354423436457579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7963267195139231248610105 5972450396354423436457579)
          ·
            refine ⟨8958675594531635154686369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5972450396354423436457579 8958675594531635154686369)
            ·
              refine ⟨6719006695898726366014777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8958675594531635154686369 6719006695898726366014777)
              ·
                refine ⟨5039255021924044774511083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6719006695898726366014777 5039255021924044774511083)
                ·
                  refine ⟨7558882532886067161766625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5039255021924044774511083 7558882532886067161766625)
                  ·
                    refine ⟨5669161899664550371324969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7558882532886067161766625 5669161899664550371324969)
                    ·
                      refine ⟨4251871424748412778493727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5669161899664550371324969 4251871424748412778493727)
                      ·
                        rfl

theorem cell23_8280490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_8280490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280490 prefixEnd_8280490 := by exact prefixLift 8280490
  have htrace : WordTrace (prefixWord ++ tailWord_8280490) baseStart_8280490 baseEnd_8280490 := by
    simpa [prefixWord, tailWord_8280490, baseEnd_8280490] using wordTrace_append hprefix tailTrace_8280490
  have hstable : (prefixWord ++ tailWord_8280490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280490).length < 2 ^ (prefixWord ++ tailWord_8280490).sum := by decide
  have hdescent : baseEnd_8280490 < baseStart_8280490 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280546 : List Nat := [3, 3, 3, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_8280546 : Nat := 118140960795 + 8280546 * 2 ^ 59
def prefixEnd_8280546 : Nat := 4983230072969 + 3 ^ 40 * 8280546 * 2
def baseEnd_8280546 : Nat := 4251900179665064559393469

theorem tailTrace_8280546 : CollatzResearch.WordTrace tailWord_8280546 prefixEnd_8280546 4251900179665064559393469 := by
  unfold tailWord_8280546
  simp only [CollatzResearch.WordTrace]
  refine ⟨75504081064750880377831373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201344216172669014340883661 75504081064750880377831373)
  ·
    refine ⟨28314030399281580141686765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75504081064750880377831373 28314030399281580141686765)
    ·
      refine ⟨10617761399730592553132537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28314030399281580141686765 10617761399730592553132537)
      ·
        refine ⟨7963321049797944414849403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10617761399730592553132537 7963321049797944414849403)
        ·
          refine ⟨11944981574696916622274105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7963321049797944414849403 11944981574696916622274105)
          ·
            refine ⟨8958736181022687466705579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11944981574696916622274105 8958736181022687466705579)
            ·
              refine ⟨13438104271534031200058369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8958736181022687466705579 13438104271534031200058369)
              ·
                refine ⟨10078578203650523400043777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13438104271534031200058369 10078578203650523400043777)
                ·
                  refine ⟨7558933652737892550032833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10078578203650523400043777 7558933652737892550032833)
                  ·
                    refine ⟨5669200239553419412524625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7558933652737892550032833 5669200239553419412524625)
                    ·
                      refine ⟨4251900179665064559393469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5669200239553419412524625 4251900179665064559393469)
                      ·
                        rfl

theorem cell23_8280546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_8280546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280546 prefixEnd_8280546 := by exact prefixLift 8280546
  have htrace : WordTrace (prefixWord ++ tailWord_8280546) baseStart_8280546 baseEnd_8280546 := by
    simpa [prefixWord, tailWord_8280546, baseEnd_8280546] using wordTrace_append hprefix tailTrace_8280546
  have hstable : (prefixWord ++ tailWord_8280546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280546).length < 2 ^ (prefixWord ++ tailWord_8280546).sum := by decide
  have hdescent : baseEnd_8280546 < baseStart_8280546 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280551 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_8280551 : Nat := 118140960795 + 8280551 * 2 ^ 59
def prefixEnd_8280551 : Nat := 4983230072969 + 3 ^ 40 * 8280551 * 2
def baseEnd_8280551 : Nat := 4251902747068337039830945

theorem tailTrace_8280551 : CollatzResearch.WordTrace tailWord_8280551 prefixEnd_8280551 4251902747068337039830945 := by
  unfold tailWord_8280551
  simp only [CollatzResearch.WordTrace]
  refine ⟨302016506623985407365257507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201344337749323604910171671 302016506623985407365257507)
  ·
    refine ⟨453024759935978111047886261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302016506623985407365257507 453024759935978111047886261)
    ·
      refine ⟨42471071243997947910739337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 453024759935978111047886261 42471071243997947910739337)
      ·
        refine ⟨31853303432998460933054503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42471071243997947910739337 31853303432998460933054503)
        ·
          refine ⟨47779955149497691399581755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31853303432998460933054503 47779955149497691399581755)
          ·
            refine ⟨71669932724246537099372633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47779955149497691399581755 71669932724246537099372633)
            ·
              refine ⟨53752449543184902824529475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71669932724246537099372633 53752449543184902824529475)
              ·
                refine ⟨80628674314777354236794213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53752449543184902824529475 80628674314777354236794213)
                ·
                  refine ⟨15117876434020753919398915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80628674314777354236794213 15117876434020753919398915)
                  ·
                    refine ⟨22676814651031130879098373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15117876434020753919398915 22676814651031130879098373)
                    ·
                      refine ⟨4251902747068337039830945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22676814651031130879098373 4251902747068337039830945)
                      ·
                        rfl

theorem cell23_8280551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_8280551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280551 prefixEnd_8280551 := by exact prefixLift 8280551
  have htrace : WordTrace (prefixWord ++ tailWord_8280551) baseStart_8280551 baseEnd_8280551 := by
    simpa [prefixWord, tailWord_8280551, baseEnd_8280551] using wordTrace_append hprefix tailTrace_8280551
  have hstable : (prefixWord ++ tailWord_8280551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280551).length < 2 ^ (prefixWord ++ tailWord_8280551).sum := by decide
  have hdescent : baseEnd_8280551 < baseStart_8280551 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280612 : List Nat := [2, 3, 1, 5, 1, 2, 1, 1, 3, 4]
def baseStart_8280612 : Nat := 118140960795 + 8280612 * 2 ^ 59
def prefixEnd_8280612 : Nat := 4983230072969 + 3 ^ 40 * 8280612 * 2
def baseEnd_8280612 : Nat := 1417311356462753767056055

theorem tailTrace_8280612 : CollatzResearch.WordTrace tailWord_8280612 prefixEnd_8280612 1417311356462753767056055 := by
  unfold tailWord_8280612
  simp only [CollatzResearch.WordTrace]
  refine ⟨151009365738382207391614045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201345820984509609855485393 151009365738382207391614045)
  ·
    refine ⟨56628512151893327771855267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151009365738382207391614045 56628512151893327771855267)
    ·
      refine ⟨84942768227839991657782901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56628512151893327771855267 84942768227839991657782901)
      ·
        refine ⟨7963384521359999217917147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84942768227839991657782901 7963384521359999217917147)
        ·
          refine ⟨11945076782039998826875721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7963384521359999217917147 11945076782039998826875721)
          ·
            refine ⟨8958807586529999120156791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11945076782039998826875721 8958807586529999120156791)
            ·
              refine ⟨13438211379794998680235187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8958807586529999120156791 13438211379794998680235187)
              ·
                refine ⟨20157317069692498020352781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13438211379794998680235187 20157317069692498020352781)
                ·
                  refine ⟨7558993901134686757632293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20157317069692498020352781 7558993901134686757632293)
                  ·
                    refine ⟨1417311356462753767056055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7558993901134686757632293 1417311356462753767056055)
                    ·
                      rfl

theorem cell23_8280612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_8280612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280612 prefixEnd_8280612 := by exact prefixLift 8280612
  have htrace : WordTrace (prefixWord ++ tailWord_8280612) baseStart_8280612 baseEnd_8280612 := by
    simpa [prefixWord, tailWord_8280612, baseEnd_8280612] using wordTrace_append hprefix tailTrace_8280612
  have hstable : (prefixWord ++ tailWord_8280612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280612).length < 2 ^ (prefixWord ++ tailWord_8280612).sum := by decide
  have hdescent : baseEnd_8280612 < baseStart_8280612 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280645 : List Nat := [1, 3, 1, 1, 1, 6, 2, 1, 2, 3, 2]
def baseStart_8280645 : Nat := 118140960795 + 8280645 * 2 ^ 59
def prefixEnd_8280645 : Nat := 4983230072969 + 3 ^ 40 * 8280645 * 2
def baseEnd_8280645 : Nat := 4251951014249859672055513

theorem tailTrace_8280645 : CollatzResearch.WordTrace tailWord_8280645 prefixEnd_8280645 4251951014249859672055513 := by
  unfold tailWord_8280645
  simp only [CollatzResearch.WordTrace]
  refine ⟨302019935085644861419179389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201346623390429907612786259 302019935085644861419179389)
  ·
    refine ⟨113257475657116823032192271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302019935085644861419179389 113257475657116823032192271)
    ·
      refine ⟨169886213485675234548288407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113257475657116823032192271 169886213485675234548288407)
      ·
        refine ⟨254829320228512851822432611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169886213485675234548288407 254829320228512851822432611)
        ·
          refine ⟨382243980342769277733648917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254829320228512851822432611 382243980342769277733648917)
          ·
            refine ⟨17917686578567309893764793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 382243980342769277733648917 17917686578567309893764793)
            ·
              refine ⟨13438264933925482420323595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17917686578567309893764793 13438264933925482420323595)
              ·
                refine ⟨20157397400888223630485393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13438264933925482420323595 20157397400888223630485393)
                ·
                  refine ⟨15118048050666167722864045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20157397400888223630485393 15118048050666167722864045)
                  ·
                    refine ⟨5669268018999812896074017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15118048050666167722864045 5669268018999812896074017)
                    ·
                      refine ⟨4251951014249859672055513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5669268018999812896074017 4251951014249859672055513)
                      ·
                        rfl

theorem cell23_8280645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 3, 2].length) (baseStart_8280645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280645 prefixEnd_8280645 := by exact prefixLift 8280645
  have htrace : WordTrace (prefixWord ++ tailWord_8280645) baseStart_8280645 baseEnd_8280645 := by
    simpa [prefixWord, tailWord_8280645, baseEnd_8280645] using wordTrace_append hprefix tailTrace_8280645
  have hstable : (prefixWord ++ tailWord_8280645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280645).length < 2 ^ (prefixWord ++ tailWord_8280645).sum := by decide
  have hdescent : baseEnd_8280645 < baseStart_8280645 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280651 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 6, 4]
def baseStart_8280651 : Nat := 118140960795 + 8280651 * 2 ^ 59
def prefixEnd_8280651 : Nat := 4983230072969 + 3 ^ 40 * 8280651 * 2
def baseEnd_8280651 : Nat := 1417318031711262216193495

theorem tailTrace_8280651 : CollatzResearch.WordTrace tailWord_8280651 prefixEnd_8280651 1417318031711262216193495 := by
  unfold tailWord_8280651
  simp only [CollatzResearch.WordTrace]
  refine ⟨302020153923623124443897807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201346769282415416295931871 302020153923623124443897807)
  ·
    refine ⟨453030230885434686665846711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302020153923623124443897807 453030230885434686665846711)
    ·
      refine ⟨679545346328152029998770067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453030230885434686665846711 679545346328152029998770067)
      ·
        refine ⟨1019318019492228044998155101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679545346328152029998770067 1019318019492228044998155101)
        ·
          refine ⟨382244257309585516874308163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1019318019492228044998155101 382244257309585516874308163)
          ·
            refine ⟨573366385964378275311462245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382244257309585516874308163 573366385964378275311462245)
            ·
              refine ⟨107506197368320926620899171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 573366385964378275311462245 107506197368320926620899171)
              ·
                refine ⟨161259296052481389931348757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107506197368320926620899171 161259296052481389931348757)
                ·
                  refine ⟨7559029502460065153031973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 161259296052481389931348757 7559029502460065153031973)
                  ·
                    refine ⟨1417318031711262216193495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7559029502460065153031973 1417318031711262216193495)
                    ·
                      rfl

theorem cell23_8280651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6, 4].length) (baseStart_8280651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280651 prefixEnd_8280651 := by exact prefixLift 8280651
  have htrace : WordTrace (prefixWord ++ tailWord_8280651) baseStart_8280651 baseEnd_8280651 := by
    simpa [prefixWord, tailWord_8280651, baseEnd_8280651] using wordTrace_append hprefix tailTrace_8280651
  have hstable : (prefixWord ++ tailWord_8280651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280651).length < 2 ^ (prefixWord ++ tailWord_8280651).sum := by decide
  have hdescent : baseEnd_8280651 < baseStart_8280651 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280675 : List Nat := [1, 1, 1, 5, 1, 2, 2, 3, 3, 2, 2]
def baseStart_8280675 : Nat := 118140960795 + 8280675 * 2 ^ 59
def prefixEnd_8280675 : Nat := 4983230072969 + 3 ^ 40 * 8280675 * 2
def baseEnd_8280675 : Nat := 4251966418669494554680375

theorem tailTrace_8280675 : CollatzResearch.WordTrace tailWord_8280675 prefixEnd_8280675 4251966418669494554680375 := by
  unfold tailWord_8280675
  simp only [CollatzResearch.WordTrace]
  refine ⟨302021029275536176542771479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201347352850357451028514319 302021029275536176542771479)
  ·
    refine ⟨453031543913304264814157219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302021029275536176542771479 453031543913304264814157219)
    ·
      refine ⟨679547315869956397221235829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453031543913304264814157219 679547315869956397221235829)
      ·
        refine ⟨63707560862808412239490859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 679547315869956397221235829 63707560862808412239490859)
        ·
          refine ⟨95561341294212618359236289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63707560862808412239490859 95561341294212618359236289)
          ·
            refine ⟨71671005970659463769427217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95561341294212618359236289 71671005970659463769427217)
            ·
              refine ⟨53753254477994597827070413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71671005970659463769427217 53753254477994597827070413)
              ·
                refine ⟨20157470429247974185151405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53753254477994597827070413 20157470429247974185151405)
                ·
                  refine ⟨7559051410967990319431777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20157470429247974185151405 7559051410967990319431777)
                  ·
                    refine ⟨5669288558225992739573833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7559051410967990319431777 5669288558225992739573833)
                    ·
                      refine ⟨4251966418669494554680375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5669288558225992739573833 4251966418669494554680375)
                      ·
                        rfl

theorem cell23_8280675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_8280675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280675 prefixEnd_8280675 := by exact prefixLift 8280675
  have htrace : WordTrace (prefixWord ++ tailWord_8280675) baseStart_8280675 baseEnd_8280675 := by
    simpa [prefixWord, tailWord_8280675, baseEnd_8280675] using wordTrace_append hprefix tailTrace_8280675
  have hstable : (prefixWord ++ tailWord_8280675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280675).length < 2 ^ (prefixWord ++ tailWord_8280675).sum := by decide
  have hdescent : baseEnd_8280675 < baseStart_8280675 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280685 : List Nat := [1, 5, 1, 1, 3, 1, 2, 3, 2, 4]
def baseStart_8280685 : Nat := 118140960795 + 8280685 * 2 ^ 59
def prefixEnd_8280685 : Nat := 4983230072969 + 3 ^ 40 * 8280685 * 2
def baseEnd_8280685 : Nat := 1417323851158679838518443

theorem tailTrace_8280685 : CollatzResearch.WordTrace tailWord_8280685 prefixEnd_8280685 1417323851158679838518443 := by
  unfold tailWord_8280685
  simp only [CollatzResearch.WordTrace]
  refine ⟨302021394005499948250635509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201347596003666632167090339 302021394005499948250635509)
  ·
    refine ⟨28314505688015620148497079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 302021394005499948250635509 28314505688015620148497079)
    ·
      refine ⟨42471758532023430222745619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28314505688015620148497079 42471758532023430222745619)
      ·
        refine ⟨63707637798035145334118429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42471758532023430222745619 63707637798035145334118429)
        ·
          refine ⟨23890364174263179500294411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63707637798035145334118429 23890364174263179500294411)
          ·
            refine ⟨35835546261394769250441617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23890364174263179500294411 35835546261394769250441617)
            ·
              refine ⟨26876659696046076937831213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35835546261394769250441617 26876659696046076937831213)
              ·
                refine ⟨10078747386017278851686705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26876659696046076937831213 10078747386017278851686705)
                ·
                  refine ⟨7559060539512959138765029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10078747386017278851686705 7559060539512959138765029)
                  ·
                    refine ⟨1417323851158679838518443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7559060539512959138765029 1417323851158679838518443)
                    ·
                      rfl

theorem cell23_8280685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_8280685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280685 prefixEnd_8280685 := by exact prefixLift 8280685
  have htrace : WordTrace (prefixWord ++ tailWord_8280685) baseStart_8280685 baseEnd_8280685 := by
    simpa [prefixWord, tailWord_8280685, baseEnd_8280685] using wordTrace_append hprefix tailTrace_8280685
  have hstable : (prefixWord ++ tailWord_8280685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280685).length < 2 ^ (prefixWord ++ tailWord_8280685).sum := by decide
  have hdescent : baseEnd_8280685 < baseStart_8280685 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280709 : List Nat := [1, 3, 1, 1, 4, 3, 2, 3, 1, 2, 2]
def baseStart_8280709 : Nat := 118140960795 + 8280709 * 2 ^ 59
def prefixEnd_8280709 : Nat := 4983230072969 + 3 ^ 40 * 8280709 * 2
def baseEnd_8280709 : Nat := 4251983877011747421655219

theorem tailTrace_8280709 : CollatzResearch.WordTrace tailWord_8280709 prefixEnd_8280709 4251983877011747421655219 := by
  unfold tailWord_8280709
  simp only [CollatzResearch.WordTrace]
  refine ⟨302022269357413000349509181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201348179571608666899672787 302022269357413000349509181)
  ·
    refine ⟨113258351009029875131065943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302022269357413000349509181 113258351009029875131065943)
    ·
      refine ⟨169887526513544812696598915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113258351009029875131065943 169887526513544812696598915)
      ·
        refine ⟨254831289770317219044898373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169887526513544812696598915 254831289770317219044898373)
        ·
          refine ⟨47780866831934478570918445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254831289770317219044898373 47780866831934478570918445)
          ·
            refine ⟨17917825061975429464094417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47780866831934478570918445 17917825061975429464094417)
            ·
              refine ⟨13438368796481572098070813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17917825061975429464094417 13438368796481572098070813)
              ·
                refine ⟨5039388298680589536776555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13438368796481572098070813 5039388298680589536776555)
                ·
                  refine ⟨7559082448020884305164833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5039388298680589536776555 7559082448020884305164833)
                  ·
                    refine ⟨5669311836015663228873625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7559082448020884305164833 5669311836015663228873625)
                    ·
                      refine ⟨4251983877011747421655219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5669311836015663228873625 4251983877011747421655219)
                      ·
                        rfl

theorem cell23_8280709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3, 1, 2, 2].length) (baseStart_8280709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280709 prefixEnd_8280709 := by exact prefixLift 8280709
  have htrace : WordTrace (prefixWord ++ tailWord_8280709) baseStart_8280709 baseEnd_8280709 := by
    simpa [prefixWord, tailWord_8280709, baseEnd_8280709] using wordTrace_append hprefix tailTrace_8280709
  have hstable : (prefixWord ++ tailWord_8280709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280709).length < 2 ^ (prefixWord ++ tailWord_8280709).sum := by decide
  have hdescent : baseEnd_8280709 < baseStart_8280709 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280768 : List Nat := [2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 5]
def baseStart_8280768 : Nat := 118140960795 + 8280768 * 2 ^ 59
def prefixEnd_8280768 : Nat := 4983230072969 + 3 ^ 40 * 8280768 * 2
def baseEnd_8280768 : Nat := 4252014172370362690817447

theorem tailTrace_8280768 : CollatzResearch.WordTrace tailWord_8280768 prefixEnd_8280768 4252014172370362690817447 := by
  unfold tailWord_8280768
  simp only [CollatzResearch.WordTrace]
  refine ⟨151012210632099626712953479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201349614176132835617271305 151012210632099626712953479)
  ·
    refine ⟨226518315948149440069430219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151012210632099626712953479 226518315948149440069430219)
    ·
      refine ⟨339777473922224160104145329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226518315948149440069430219 339777473922224160104145329)
      ·
        refine ⟨254833105441668120078108997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339777473922224160104145329 254833105441668120078108997)
        ·
          refine ⟨47781207270312772514645437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254833105441668120078108997 47781207270312772514645437)
          ·
            refine ⟨17917952726367289692992039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47781207270312772514645437 17917952726367289692992039)
            ·
              refine ⟨26876929089550934539488059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17917952726367289692992039 26876929089550934539488059)
              ·
                refine ⟨40315393634326401809232089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26876929089550934539488059 40315393634326401809232089)
                ·
                  refine ⟨30236545225744801356924067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40315393634326401809232089 30236545225744801356924067)
                  ·
                    refine ⟨45354817838617202035386101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30236545225744801356924067 45354817838617202035386101)
                    ·
                      refine ⟨4252014172370362690817447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45354817838617202035386101 4252014172370362690817447)
                      ·
                        rfl

theorem cell23_8280768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_8280768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280768 prefixEnd_8280768 := by exact prefixLift 8280768
  have htrace : WordTrace (prefixWord ++ tailWord_8280768) baseStart_8280768 baseEnd_8280768 := by
    simpa [prefixWord, tailWord_8280768, baseEnd_8280768] using wordTrace_append hprefix tailTrace_8280768
  have hstable : (prefixWord ++ tailWord_8280768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280768).length < 2 ^ (prefixWord ++ tailWord_8280768).sum := by decide
  have hdescent : baseEnd_8280768 < baseStart_8280768 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280782 : List Nat := [4, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2]
def baseStart_8280782 : Nat := 118140960795 + 8280782 * 2 ^ 59
def prefixEnd_8280782 : Nat := 4983230072969 + 3 ^ 40 * 8280782 * 2
def baseEnd_8280782 : Nat := 4252021361099525636042383

theorem tailTrace_8280782 : CollatzResearch.WordTrace tailWord_8280782 prefixEnd_8280782 4252021361099525636042383 := by
  unfold tailWord_8280782
  simp only [CollatzResearch.WordTrace]
  refine ⟨37753116485768566727114575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201349954590765689211277733 37753116485768566727114575)
  ·
    refine ⟨56629674728652850090671863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37753116485768566727114575 56629674728652850090671863)
    ·
      refine ⟨84944512092979275136007795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56629674728652850090671863 84944512092979275136007795)
      ·
        refine ⟨127416768139468912704011693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84944512092979275136007795 127416768139468912704011693)
        ·
          refine ⟨47781288052300842264004385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127416768139468912704011693 47781288052300842264004385)
          ·
            refine ⟨35835966039225631698003289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47781288052300842264004385 35835966039225631698003289)
            ·
              refine ⟨26876974529419223773502467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35835966039225631698003289 26876974529419223773502467)
              ·
                refine ⟨40315461794128835660253701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26876974529419223773502467 40315461794128835660253701)
                ·
                  refine ⟨7559149086399156686297569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40315461794128835660253701 7559149086399156686297569)
                  ·
                    refine ⟨5669361814799367514723177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7559149086399156686297569 5669361814799367514723177)
                    ·
                      refine ⟨4252021361099525636042383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5669361814799367514723177 4252021361099525636042383)
                      ·
                        rfl

theorem cell23_8280782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2].length) (baseStart_8280782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280782 prefixEnd_8280782 := by exact prefixLift 8280782
  have htrace : WordTrace (prefixWord ++ tailWord_8280782) baseStart_8280782 baseEnd_8280782 := by
    simpa [prefixWord, tailWord_8280782, baseEnd_8280782] using wordTrace_append hprefix tailTrace_8280782
  have hstable : (prefixWord ++ tailWord_8280782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280782).length < 2 ^ (prefixWord ++ tailWord_8280782).sum := by decide
  have hdescent : baseEnd_8280782 < baseStart_8280782 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280799 : List Nat := [1, 1, 2, 3, 2, 3, 4, 1, 2, 2, 2]
def baseStart_8280799 : Nat := 118140960795 + 8280799 * 2 ^ 59
def prefixEnd_8280799 : Nat := 4983230072969 + 3 ^ 40 * 8280799 * 2
def baseEnd_8280799 : Nat := 4252030090270652069529805

theorem tailTrace_8280799 : CollatzResearch.WordTrace tailWord_8280799 prefixEnd_8280799 4252030090270652069529805 := by
  unfold tailWord_8280799
  simp only [CollatzResearch.WordTrace]
  refine ⟨302025551927086945720285451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201350367951391297146856967 302025551927086945720285451)
  ·
    refine ⟨453038327890630418580428177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302025551927086945720285451 453038327890630418580428177)
    ·
      refine ⟨339778745917972813935321133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453038327890630418580428177 339778745917972813935321133)
      ·
        refine ⟨127417029719239805225745425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339778745917972813935321133 127417029719239805225745425)
        ·
          refine ⟨95562772289429853919309069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127417029719239805225745425 95562772289429853919309069)
          ·
            refine ⟨35836039608536195219740901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95562772289429853919309069 35836039608536195219740901)
            ·
              refine ⟨6719257426600536603701419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35836039608536195219740901 6719257426600536603701419)
              ·
                refine ⟨10078886139900804905552129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6719257426600536603701419 10078886139900804905552129)
                ·
                  refine ⟨7559164604925603679164097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10078886139900804905552129 7559164604925603679164097)
                  ·
                    refine ⟨5669373453694202759373073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7559164604925603679164097 5669373453694202759373073)
                    ·
                      refine ⟨4252030090270652069529805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5669373453694202759373073 4252030090270652069529805)
                      ·
                        rfl

theorem cell23_8280799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 2, 2, 2].length) (baseStart_8280799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280799 prefixEnd_8280799 := by exact prefixLift 8280799
  have htrace : WordTrace (prefixWord ++ tailWord_8280799) baseStart_8280799 baseEnd_8280799 := by
    simpa [prefixWord, tailWord_8280799, baseEnd_8280799] using wordTrace_append hprefix tailTrace_8280799
  have hstable : (prefixWord ++ tailWord_8280799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280799).length < 2 ^ (prefixWord ++ tailWord_8280799).sum := by decide
  have hdescent : baseEnd_8280799 < baseStart_8280799 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280811 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 7]
def baseStart_8280811 : Nat := 118140960795 + 8280811 * 2 ^ 59
def prefixEnd_8280811 : Nat := 4983230072969 + 3 ^ 40 * 8280811 * 2
def baseEnd_8280811 : Nat := 4252036252038506022579749

theorem tailTrace_8280811 : CollatzResearch.WordTrace tailWord_8280811 prefixEnd_8280811 4252036252038506022579749 := by
  unfold tailWord_8280811
  simp only [CollatzResearch.WordTrace]
  refine ⟨302025989603043471769722287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201350659735362314513148191 302025989603043471769722287)
  ·
    refine ⟨453038984404565207654583431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302025989603043471769722287 453038984404565207654583431)
    ·
      refine ⟨679558476606847811481875147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453038984404565207654583431 679558476606847811481875147)
      ·
        refine ⟨1019337714910271717222812721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679558476606847811481875147 1019337714910271717222812721)
        ·
          refine ⟨764503286182703787917109541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1019337714910271717222812721 764503286182703787917109541)
          ·
            refine ⟨143344366159256960234458039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 764503286182703787917109541 143344366159256960234458039)
            ·
              refine ⟨215016549238885440351687059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143344366159256960234458039 215016549238885440351687059)
              ·
                refine ⟨322524823858328160527530589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215016549238885440351687059 322524823858328160527530589)
                ·
                  refine ⟨120946808946873060197823971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322524823858328160527530589 120946808946873060197823971)
                  ·
                    refine ⟨181420213420309590296735957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120946808946873060197823971 181420213420309590296735957)
                    ·
                      refine ⟨4252036252038506022579749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 181420213420309590296735957 4252036252038506022579749)
                      ·
                        rfl

theorem cell23_8280811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 7].length) (baseStart_8280811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280811 prefixEnd_8280811 := by exact prefixLift 8280811
  have htrace : WordTrace (prefixWord ++ tailWord_8280811) baseStart_8280811 baseEnd_8280811 := by
    simpa [prefixWord, tailWord_8280811, baseEnd_8280811] using wordTrace_append hprefix tailTrace_8280811
  have hstable : (prefixWord ++ tailWord_8280811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280811).length < 2 ^ (prefixWord ++ tailWord_8280811).sum := by decide
  have hdescent : baseEnd_8280811 < baseStart_8280811 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
