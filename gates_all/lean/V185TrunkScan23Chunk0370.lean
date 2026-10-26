import V185TrunkScan23Chunk0369

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2187539 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 3, 4, 3]
def baseStart_2187539 : Nat := 118140960795 + 2187539 * 2 ^ 59
def prefixEnd_2187539 : Nat := 4983230072969 + 3 ^ 40 * 2187539 * 2
def baseEnd_2187539 : Nat := 1123258957455821977302197

theorem tailTrace_2187539 : CollatzResearch.WordTrace tailWord_2187539 prefixEnd_2187539 1123258957455821977302197 := by
  unfold tailWord_2187539
  simp only [CollatzResearch.WordTrace]
  refine ⟨79786102021927279762341671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53190734681284853174894447 79786102021927279762341671)
  ·
    refine ⟨119679153032890919643512507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79786102021927279762341671 119679153032890919643512507)
    ·
      refine ⟨179518729549336379465268761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119679153032890919643512507 179518729549336379465268761)
      ·
        refine ⟨134639047162002284598951571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179518729549336379465268761 134639047162002284598951571)
        ·
          refine ⟨201958570743003426898427357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134639047162002284598951571 201958570743003426898427357)
          ·
            refine ⟨75734464028626285086910259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201958570743003426898427357 75734464028626285086910259)
            ·
              refine ⟨113601696042939427630365389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75734464028626285086910259 113601696042939427630365389)
              ·
                refine ⟨42600636016102285361387021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113601696042939427630365389 42600636016102285361387021)
                ·
                  refine ⟨15975238506038357010520133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42600636016102285361387021 15975238506038357010520133)
                  ·
                    refine ⟨2995357219882191939472525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15975238506038357010520133 2995357219882191939472525)
                    ·
                      refine ⟨1123258957455821977302197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2995357219882191939472525 1123258957455821977302197)
                      ·
                        rfl

theorem cell23_2187539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4, 3].length) (baseStart_2187539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187539 prefixEnd_2187539 := by exact prefixLift 2187539
  have htrace : WordTrace (prefixWord ++ tailWord_2187539) baseStart_2187539 baseEnd_2187539 := by
    simpa [prefixWord, tailWord_2187539, baseEnd_2187539] using wordTrace_append hprefix tailTrace_2187539
  have hstable : (prefixWord ++ tailWord_2187539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187539).length < 2 ^ (prefixWord ++ tailWord_2187539).sum := by decide
  have hdescent : baseEnd_2187539 < baseStart_2187539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187550 : List Nat := [4, 3, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_2187550 : Nat := 118140960795 + 2187550 * 2 ^ 59
def prefixEnd_2187550 : Nat := 4983230072969 + 3 ^ 40 * 2187550 * 2
def baseEnd_2187550 : Nat := 374421535247673811421549

theorem tailTrace_2187550 : CollatzResearch.WordTrace tailWord_2187550 prefixEnd_2187550 374421535247673811421549 := by
  unfold tailWord_2187550
  simp only [CollatzResearch.WordTrace]
  refine ⟨9973312903110928580124013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53191002149924952427328069 9973312903110928580124013)
  ·
    refine ⟨3739992338666598217546505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9973312903110928580124013 3739992338666598217546505)
    ·
      refine ⟨2804994253999948663159879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3739992338666598217546505 2804994253999948663159879)
      ·
        refine ⟨4207491380999922994739819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2804994253999948663159879 4207491380999922994739819)
        ·
          refine ⟨6311237071499884492109729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4207491380999922994739819 6311237071499884492109729)
          ·
            refine ⟨4733427803624913369082297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6311237071499884492109729 4733427803624913369082297)
            ·
              refine ⟨3550070852718685026811723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4733427803624913369082297 3550070852718685026811723)
              ·
                refine ⟨5325106279078027540217585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3550070852718685026811723 5325106279078027540217585)
                ·
                  refine ⟨3993829709308520655163189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5325106279078027540217585 3993829709308520655163189)
                  ·
                    refine ⟨374421535247673811421549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3993829709308520655163189 374421535247673811421549)
                    ·
                      rfl

theorem cell23_2187550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_2187550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187550 prefixEnd_2187550 := by exact prefixLift 2187550
  have htrace : WordTrace (prefixWord ++ tailWord_2187550) baseStart_2187550 baseEnd_2187550 := by
    simpa [prefixWord, tailWord_2187550, baseEnd_2187550] using wordTrace_append hprefix tailTrace_2187550
  have hstable : (prefixWord ++ tailWord_2187550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187550).length < 2 ^ (prefixWord ++ tailWord_2187550).sum := by decide
  have hdescent : baseEnd_2187550 < baseStart_2187550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187623 : List Nat := [1, 1, 5, 1, 3, 2, 1, 3, 1, 5]
def baseStart_2187623 : Nat := 118140960795 + 2187623 * 2 ^ 59
def prefixEnd_2187623 : Nat := 4983230072969 + 3 ^ 40 * 2187623 * 2
def baseEnd_2187623 : Nat := 374434029943599882883937

theorem tailTrace_2187623 : CollatzResearch.WordTrace tailWord_2187623 prefixEnd_2187623 374434029943599882883937 := by
  unfold tailWord_2187623
  simp only [CollatzResearch.WordTrace]
  refine ⟨79789165753622962108399523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53192777169081974738933015 79789165753622962108399523)
  ·
    refine ⟨119683748630434443162599285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79789165753622962108399523 119683748630434443162599285)
    ·
      refine ⟨11220351434103229046493683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119683748630434443162599285 11220351434103229046493683)
      ·
        refine ⟨16830527151154843569740525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11220351434103229046493683 16830527151154843569740525)
        ·
          refine ⟨6311447681683066338652697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16830527151154843569740525 6311447681683066338652697)
          ·
            refine ⟨4733585761262299753989523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6311447681683066338652697 4733585761262299753989523)
            ·
              refine ⟨7100378641893449630984285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4733585761262299753989523 7100378641893449630984285)
              ·
                refine ⟨2662641990710043611619107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7100378641893449630984285 2662641990710043611619107)
                ·
                  refine ⟨3993962986065065417428661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2662641990710043611619107 3993962986065065417428661)
                  ·
                    refine ⟨374434029943599882883937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3993962986065065417428661 374434029943599882883937)
                    ·
                      rfl

theorem cell23_2187623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_2187623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187623 prefixEnd_2187623 := by exact prefixLift 2187623
  have htrace : WordTrace (prefixWord ++ tailWord_2187623) baseStart_2187623 baseEnd_2187623 := by
    simpa [prefixWord, tailWord_2187623, baseEnd_2187623] using wordTrace_append hprefix tailTrace_2187623
  have hstable : (prefixWord ++ tailWord_2187623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187623).length < 2 ^ (prefixWord ++ tailWord_2187623).sum := by decide
  have hdescent : baseEnd_2187623 < baseStart_2187623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187637 : List Nat := [1, 3, 4, 1, 2, 1, 2, 4, 1, 1, 3]
def baseStart_2187637 : Nat := 118140960795 + 2187637 * 2 ^ 59
def prefixEnd_2187637 : Nat := 4983230072969 + 3 ^ 40 * 2187637 * 2
def baseEnd_2187637 : Nat := 1123309278559962593876747

theorem tailTrace_2187637 : CollatzResearch.WordTrace tailWord_2187637 prefixEnd_2187637 1123309278559962593876747 := by
  unfold tailWord_2187637
  simp only [CollatzResearch.WordTrace]
  refine ⟨79789676375572242499409165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53193117583714828332939443 79789676375572242499409165)
  ·
    refine ⟨29921128640839590937278437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79789676375572242499409165 29921128640839590937278437)
    ·
      refine ⟨5610211620157423300739707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29921128640839590937278437 5610211620157423300739707)
      ·
        refine ⟨8415317430236134951109561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5610211620157423300739707 8415317430236134951109561)
        ·
          refine ⟨6311488072677101213332171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8415317430236134951109561 6311488072677101213332171)
          ·
            refine ⟨9467232109015651819998257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6311488072677101213332171 9467232109015651819998257)
            ·
              refine ⟨7100424081761738864998693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9467232109015651819998257 7100424081761738864998693)
              ·
                refine ⟨1331329515330326037187255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7100424081761738864998693 1331329515330326037187255)
                ·
                  refine ⟨1996994272995489055780883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1331329515330326037187255 1996994272995489055780883)
                  ·
                    refine ⟨2995491409493233583671325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1996994272995489055780883 2995491409493233583671325)
                    ·
                      refine ⟨1123309278559962593876747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2995491409493233583671325 1123309278559962593876747)
                      ·
                        rfl

theorem cell23_2187637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_2187637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187637 prefixEnd_2187637 := by exact prefixLift 2187637
  have htrace : WordTrace (prefixWord ++ tailWord_2187637) baseStart_2187637 baseEnd_2187637 := by
    simpa [prefixWord, tailWord_2187637, baseEnd_2187637] using wordTrace_append hprefix tailTrace_2187637
  have hstable : (prefixWord ++ tailWord_2187637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187637).length < 2 ^ (prefixWord ++ tailWord_2187637).sum := by decide
  have hdescent : baseEnd_2187637 < baseStart_2187637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187656 : List Nat := [2, 1, 3, 3, 1, 1, 3, 1, 1, 1, 6]
def baseStart_2187656 : Nat := 118140960795 + 2187656 * 2 ^ 59
def prefixEnd_2187656 : Nat := 4983230072969 + 3 ^ 40 * 2187656 * 2
def baseEnd_2187656 : Nat := 1123319034692398019539159

theorem tailTrace_2187656 : CollatzResearch.WordTrace tailWord_2187656 prefixEnd_2187656 1123319034692398019539159 := by
  unfold tailWord_2187656
  simp only [CollatzResearch.WordTrace]
  refine ⟨39895184681251704372175411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53193579575002272496233881 39895184681251704372175411)
  ·
    refine ⟨59842777021877556558263117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39895184681251704372175411 59842777021877556558263117)
    ·
      refine ⟨22441041383204083709348669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59842777021877556558263117 22441041383204083709348669)
      ·
        refine ⟨8415390518701531391005751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22441041383204083709348669 8415390518701531391005751)
        ·
          refine ⟨12623085778052297086508627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8415390518701531391005751 12623085778052297086508627)
          ·
            refine ⟨18934628667078445629762941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12623085778052297086508627 18934628667078445629762941)
            ·
              refine ⟨7100485750154417111161103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18934628667078445629762941 7100485750154417111161103)
              ·
                refine ⟨10650728625231625666741655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7100485750154417111161103 10650728625231625666741655)
                ·
                  refine ⟨15976092937847438500112483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10650728625231625666741655 15976092937847438500112483)
                  ·
                    refine ⟨23964139406771157750168725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15976092937847438500112483 23964139406771157750168725)
                    ·
                      refine ⟨1123319034692398019539159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23964139406771157750168725 1123319034692398019539159)
                      ·
                        rfl

theorem cell23_2187656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_2187656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187656 prefixEnd_2187656 := by exact prefixLift 2187656
  have htrace : WordTrace (prefixWord ++ tailWord_2187656) baseStart_2187656 baseEnd_2187656 := by
    simpa [prefixWord, tailWord_2187656, baseEnd_2187656] using wordTrace_append hprefix tailTrace_2187656
  have hstable : (prefixWord ++ tailWord_2187656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187656).length < 2 ^ (prefixWord ++ tailWord_2187656).sum := by decide
  have hdescent : baseEnd_2187656 < baseStart_2187656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187660 : List Nat := [2, 2, 1, 2, 1, 4, 2, 2, 3, 2, 2]
def baseStart_2187660 : Nat := 118140960795 + 2187660 * 2 ^ 59
def prefixEnd_2187660 : Nat := 4983230072969 + 3 ^ 40 * 2187660 * 2
def baseEnd_2187660 : Nat := 1123321088615016003889141

theorem tailTrace_2187660 : CollatzResearch.WordTrace tailWord_2187660 prefixEnd_2187660 1123321088615016003889141 := by
  unfold tailWord_2187660
  simp only [CollatzResearch.WordTrace]
  refine ⟨39895257627244458713748217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53193676836325944951664289 39895257627244458713748217)
  ·
    refine ⟨29921443220433344035311163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39895257627244458713748217 29921443220433344035311163)
    ·
      refine ⟨44882164830650016052966745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29921443220433344035311163 44882164830650016052966745)
      ·
        refine ⟨33661623622987512039725059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44882164830650016052966745 33661623622987512039725059)
        ·
          refine ⟨50492435434481268059587589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33661623622987512039725059 50492435434481268059587589)
          ·
            refine ⟨9467331643965237761172673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50492435434481268059587589 9467331643965237761172673)
            ·
              refine ⟨7100498732973928320879505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9467331643965237761172673 7100498732973928320879505)
              ·
                refine ⟨5325374049730446240659629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7100498732973928320879505 5325374049730446240659629)
                ·
                  refine ⟨1997015268648917340247361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5325374049730446240659629 1997015268648917340247361)
                  ·
                    refine ⟨1497761451486688005185521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1997015268648917340247361 1497761451486688005185521)
                    ·
                      refine ⟨1123321088615016003889141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1497761451486688005185521 1123321088615016003889141)
                      ·
                        rfl

theorem cell23_2187660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 3, 2, 2].length) (baseStart_2187660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187660 prefixEnd_2187660 := by exact prefixLift 2187660
  have htrace : WordTrace (prefixWord ++ tailWord_2187660) baseStart_2187660 baseEnd_2187660 := by
    simpa [prefixWord, tailWord_2187660, baseEnd_2187660] using wordTrace_append hprefix tailTrace_2187660
  have hstable : (prefixWord ++ tailWord_2187660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187660).length < 2 ^ (prefixWord ++ tailWord_2187660).sum := by decide
  have hdescent : baseEnd_2187660 < baseStart_2187660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187720 : List Nat := [2, 1, 3, 1, 3, 3, 1, 1, 3, 3, 2]
def baseStart_2187720 : Nat := 118140960795 + 2187720 * 2 ^ 59
def prefixEnd_2187720 : Nat := 4983230072969 + 3 ^ 40 * 2187720 * 2
def baseEnd_2187720 : Nat := 1123351897454285769138865

theorem tailTrace_2187720 : CollatzResearch.WordTrace tailWord_2187720 prefixEnd_2187720 1123351897454285769138865 := by
  unfold tailWord_2187720
  simp only [CollatzResearch.WordTrace]
  refine ⟨39896351817135773837340307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53195135756181031783120409 39896351817135773837340307)
  ·
    refine ⟨59844527725703660756010461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39896351817135773837340307 59844527725703660756010461)
    ·
      refine ⟨22441697897138872783503923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59844527725703660756010461 22441697897138872783503923)
      ·
        refine ⟨33662546845708309175255885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22441697897138872783503923 33662546845708309175255885)
        ·
          refine ⟨12623455067140615940720957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33662546845708309175255885 12623455067140615940720957)
          ·
            refine ⟨4733795650177730977770359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12623455067140615940720957 4733795650177730977770359)
            ·
              refine ⟨7100693475266596466655539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4733795650177730977770359 7100693475266596466655539)
              ·
                refine ⟨10651040212899894699983309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7100693475266596466655539 10651040212899894699983309)
                ·
                  refine ⟨3994140079837460512493741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10651040212899894699983309 3994140079837460512493741)
                  ·
                    refine ⟨1497802529939047692185153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3994140079837460512493741 1497802529939047692185153)
                    ·
                      refine ⟨1123351897454285769138865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1497802529939047692185153 1123351897454285769138865)
                      ·
                        rfl

theorem cell23_2187720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 3, 3, 2].length) (baseStart_2187720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187720 prefixEnd_2187720 := by exact prefixLift 2187720
  have htrace : WordTrace (prefixWord ++ tailWord_2187720) baseStart_2187720 baseEnd_2187720 := by
    simpa [prefixWord, tailWord_2187720, baseEnd_2187720] using wordTrace_append hprefix tailTrace_2187720
  have hstable : (prefixWord ++ tailWord_2187720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187720).length < 2 ^ (prefixWord ++ tailWord_2187720).sum := by decide
  have hdescent : baseEnd_2187720 < baseStart_2187720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187726 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 4, 6]
def baseStart_2187726 : Nat := 118140960795 + 2187726 * 2 ^ 59
def prefixEnd_2187726 : Nat := 4983230072969 + 3 ^ 40 * 2187726 * 2
def baseEnd_2187726 : Nat := 374451659446070915221279

theorem tailTrace_2187726 : CollatzResearch.WordTrace tailWord_2187726 prefixEnd_2187726 374451659446070915221279 := by
  unfold tailWord_2187726
  simp only [CollatzResearch.WordTrace]
  refine ⟨9974115309031226337424879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53195281648166540466266021 9974115309031226337424879)
  ·
    refine ⟨14961172963546839506137319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9974115309031226337424879 14961172963546839506137319)
    ·
      refine ⟨22441759445320259259205979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14961172963546839506137319 22441759445320259259205979)
      ·
        refine ⟨33662639167980388888808969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22441759445320259259205979 33662639167980388888808969)
        ·
          refine ⟨25246979375985291666606727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33662639167980388888808969 25246979375985291666606727)
          ·
            refine ⟨37870469063977937499910091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25246979375985291666606727 37870469063977937499910091)
            ·
              refine ⟨56805703595966906249865137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37870469063977937499910091 56805703595966906249865137)
              ·
                refine ⟨42604277696975179687398853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56805703595966906249865137 42604277696975179687398853)
                ·
                  refine ⟨7988302068182846191387285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42604277696975179687398853 7988302068182846191387285)
                  ·
                    refine ⟨374451659446070915221279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7988302068182846191387285 374451659446070915221279)
                    ·
                      rfl

theorem cell23_2187726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_2187726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187726 prefixEnd_2187726 := by exact prefixLift 2187726
  have htrace : WordTrace (prefixWord ++ tailWord_2187726) baseStart_2187726 baseEnd_2187726 := by
    simpa [prefixWord, tailWord_2187726, baseEnd_2187726] using wordTrace_append hprefix tailTrace_2187726
  have hstable : (prefixWord ++ tailWord_2187726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187726).length < 2 ^ (prefixWord ++ tailWord_2187726).sum := by decide
  have hdescent : baseEnd_2187726 < baseStart_2187726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187737 : List Nat := [1, 2, 1, 2, 4, 1, 5, 1, 1, 3, 2]
def baseStart_2187737 : Nat := 118140960795 + 2187737 * 2 ^ 59
def prefixEnd_2187737 : Nat := 4983230072969 + 3 ^ 40 * 2187737 * 2
def baseEnd_2187737 : Nat := 1123360626625412202626287

theorem tailTrace_2187737 : CollatzResearch.WordTrace tailWord_2187737 prefixEnd_2187737 1123360626625412202626287 := by
  unfold tailWord_2187737
  simp only [CollatzResearch.WordTrace]
  refine ⟨79793323675209959578049465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53195549116806639718699643 79793323675209959578049465)
  ·
    refine ⟨59844992756407469683537099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79793323675209959578049465 59844992756407469683537099)
    ·
      refine ⟨89767489134611204525305649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59844992756407469683537099 89767489134611204525305649)
      ·
        refine ⟨67325616850958403393979237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89767489134611204525305649 67325616850958403393979237)
        ·
          refine ⟨12623553159554700636371107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67325616850958403393979237 12623553159554700636371107)
          ·
            refine ⟨18935329739332050954556661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12623553159554700636371107 18935329739332050954556661)
            ·
              refine ⟨1775187163062379776989687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18935329739332050954556661 1775187163062379776989687)
              ·
                refine ⟨2662780744593569665484531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1775187163062379776989687 2662780744593569665484531)
                ·
                  refine ⟨3994171116890354498226797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2662780744593569665484531 3994171116890354498226797)
                  ·
                    refine ⟨1497814168833882936835049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3994171116890354498226797 1497814168833882936835049)
                    ·
                      refine ⟨1123360626625412202626287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1497814168833882936835049 1123360626625412202626287)
                      ·
                        rfl

theorem cell23_2187737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 1, 3, 2].length) (baseStart_2187737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187737 prefixEnd_2187737 := by exact prefixLift 2187737
  have htrace : WordTrace (prefixWord ++ tailWord_2187737) baseStart_2187737 baseEnd_2187737 := by
    simpa [prefixWord, tailWord_2187737, baseEnd_2187737] using wordTrace_append hprefix tailTrace_2187737
  have hstable : (prefixWord ++ tailWord_2187737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187737).length < 2 ^ (prefixWord ++ tailWord_2187737).sum := by decide
  have hdescent : baseEnd_2187737 < baseStart_2187737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187756 : List Nat := [2, 2, 1, 1, 2, 1, 4, 3, 7]
def baseStart_2187756 : Nat := 118140960795 + 2187756 * 2 ^ 59
def prefixEnd_2187756 : Nat := 4983230072969 + 3 ^ 40 * 2187756 * 2
def baseEnd_2187756 : Nat := 124818931417538625365411

theorem tailTrace_2187756 : CollatzResearch.WordTrace tailWord_2187756 prefixEnd_2187756 124818931417538625365411 := by
  unfold tailWord_2187756
  simp only [CollatzResearch.WordTrace]
  refine ⟨39897008331070562911495561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53196011108094083881994081 39897008331070562911495561)
  ·
    refine ⟨29922756248302922183621671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39897008331070562911495561 29922756248302922183621671)
    ·
      refine ⟨44884134372454383275432507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29922756248302922183621671 44884134372454383275432507)
      ·
        refine ⟨67326201558681574913148761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44884134372454383275432507 67326201558681574913148761)
        ·
          refine ⟨50494651169011181184861571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67326201558681574913148761 50494651169011181184861571)
          ·
            refine ⟨75741976753516771777292357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50494651169011181184861571 75741976753516771777292357)
            ·
              refine ⟨14201620641284394708242317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75741976753516771777292357 14201620641284394708242317)
              ·
                refine ⟨5325607740481648015590869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14201620641284394708242317 5325607740481648015590869)
                ·
                  refine ⟨124818931417538625365411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5325607740481648015590869 124818931417538625365411)
                  ·
                    rfl

theorem cell23_2187756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 7].length) (baseStart_2187756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187756 prefixEnd_2187756 := by exact prefixLift 2187756
  have htrace : WordTrace (prefixWord ++ tailWord_2187756) baseStart_2187756 baseEnd_2187756 := by
    simpa [prefixWord, tailWord_2187756, baseEnd_2187756] using wordTrace_append hprefix tailTrace_2187756
  have hstable : (prefixWord ++ tailWord_2187756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187756).length < 2 ^ (prefixWord ++ tailWord_2187756).sum := by decide
  have hdescent : baseEnd_2187756 < baseStart_2187756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187790 : List Nat := [4, 1, 1, 2, 3, 1, 1, 5, 5]
def baseStart_2187790 : Nat := 118140960795 + 2187790 * 2 ^ 59
def prefixEnd_2187790 : Nat := 4983230072969 + 3 ^ 40 * 2187790 * 2
def baseEnd_2187790 : Nat := 124820871233344499473727

theorem tailTrace_2187790 : CollatzResearch.WordTrace tailWord_2187790 prefixEnd_2187790 124820871233344499473727 := by
  unfold tailWord_2187790
  simp only [CollatzResearch.WordTrace]
  refine ⟨9974407093002243703716103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53196837829345299753152549 9974407093002243703716103)
  ·
    refine ⟨14961610639503365555574155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9974407093002243703716103 14961610639503365555574155)
    ·
      refine ⟨22442415959255048333361233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14961610639503365555574155 22442415959255048333361233)
      ·
        refine ⟨16831811969441286250020925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22442415959255048333361233 16831811969441286250020925)
        ·
          refine ⟨6311929488540482343757847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16831811969441286250020925 6311929488540482343757847)
          ·
            refine ⟨9467894232810723515636771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6311929488540482343757847 9467894232810723515636771)
            ·
              refine ⟨14201841349216085273455157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9467894232810723515636771 14201841349216085273455157)
              ·
                refine ⟨1331422626489007994386421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14201841349216085273455157 1331422626489007994386421)
                ·
                  refine ⟨124820871233344499473727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1331422626489007994386421 124820871233344499473727)
                  ·
                    rfl

theorem cell23_2187790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5, 5].length) (baseStart_2187790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187790 prefixEnd_2187790 := by exact prefixLift 2187790
  have htrace : WordTrace (prefixWord ++ tailWord_2187790) baseStart_2187790 baseEnd_2187790 := by
    simpa [prefixWord, tailWord_2187790, baseEnd_2187790] using wordTrace_append hprefix tailTrace_2187790
  have hstable : (prefixWord ++ tailWord_2187790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187790).length < 2 ^ (prefixWord ++ tailWord_2187790).sum := by decide
  have hdescent : baseEnd_2187790 < baseStart_2187790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187793 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 1, 7, 2]
def baseStart_2187793 : Nat := 118140960795 + 2187793 * 2 ^ 59
def prefixEnd_2187793 : Nat := 4983230072969 + 3 ^ 40 * 2187793 * 2
def baseEnd_2187793 : Nat := 1123389381542063983526029

theorem tailTrace_2187793 : CollatzResearch.WordTrace tailWord_2187793 prefixEnd_2187793 1123389381542063983526029 := by
  unfold tailWord_2187793
  simp only [CollatzResearch.WordTrace]
  refine ⟨79795366163007081142088033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53196910775338054094725355 79795366163007081142088033)
  ·
    refine ⟨59846524622255310856566025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79795366163007081142088033 59846524622255310856566025)
    ·
      refine ⟨44884893466691483142424519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59846524622255310856566025 44884893466691483142424519)
      ·
        refine ⟨67327340200037224713636779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44884893466691483142424519 67327340200037224713636779)
        ·
          refine ⟨100991010300055837070455169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67327340200037224713636779 100991010300055837070455169)
          ·
            refine ⟨75743257725041877802841377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100991010300055837070455169 75743257725041877802841377)
            ·
              refine ⟨56807443293781408352131033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75743257725041877802841377 56807443293781408352131033)
              ·
                refine ⟨42605582470336056264098275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56807443293781408352131033 42605582470336056264098275)
                ·
                  refine ⟨63908373705504084396147413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42605582470336056264098275 63908373705504084396147413)
                  ·
                    refine ⟨1497852508722751978034705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 63908373705504084396147413 1497852508722751978034705)
                    ·
                      refine ⟨1123389381542063983526029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1497852508722751978034705 1123389381542063983526029)
                      ·
                        rfl

theorem cell23_2187793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 7, 2].length) (baseStart_2187793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187793 prefixEnd_2187793 := by exact prefixLift 2187793
  have htrace : WordTrace (prefixWord ++ tailWord_2187793) baseStart_2187793 baseEnd_2187793 := by
    simpa [prefixWord, tailWord_2187793, baseEnd_2187793] using wordTrace_append hprefix tailTrace_2187793
  have hstable : (prefixWord ++ tailWord_2187793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187793).length < 2 ^ (prefixWord ++ tailWord_2187793).sum := by decide
  have hdescent : baseEnd_2187793 < baseStart_2187793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187843 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 6, 2, 3]
def baseStart_2187843 : Nat := 118140960795 + 2187843 * 2 ^ 59
def prefixEnd_2187843 : Nat := 4983230072969 + 3 ^ 40 * 2187843 * 2
def baseEnd_2187843 : Nat := 1123415055574788787900799

theorem tailTrace_2187843 : CollatzResearch.WordTrace tailWord_2187843 prefixEnd_2187843 1123415055574788787900799 := by
  unfold tailWord_2187843
  simp only [CollatzResearch.WordTrace]
  refine ⟨79797189812825939681408183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53198126541883959787605455 79797189812825939681408183)
  ·
    refine ⟨119695784719238909522112275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79797189812825939681408183 119695784719238909522112275)
    ·
      refine ⟨179543677078858364283168413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119695784719238909522112275 179543677078858364283168413)
      ·
        refine ⟨67328878904571886606188155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179543677078858364283168413 67328878904571886606188155)
        ·
          refine ⟨100993318356857829909282233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67328878904571886606188155 100993318356857829909282233)
          ·
            refine ⟨75744988767643372431961675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100993318356857829909282233 75744988767643372431961675)
            ·
              refine ⟨113617483151465058647942513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75744988767643372431961675 113617483151465058647942513)
              ·
                refine ⟨85213112363598793985956885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113617483151465058647942513 85213112363598793985956885)
                ·
                  refine ⟨3994364642043693468091729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 85213112363598793985956885 3994364642043693468091729)
                  ·
                    refine ⟨2995773481532770101068797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3994364642043693468091729 2995773481532770101068797)
                    ·
                      refine ⟨1123415055574788787900799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2995773481532770101068797 1123415055574788787900799)
                      ·
                        rfl

theorem cell23_2187843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2, 3].length) (baseStart_2187843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187843 prefixEnd_2187843 := by exact prefixLift 2187843
  have htrace : WordTrace (prefixWord ++ tailWord_2187843) baseStart_2187843 baseEnd_2187843 := by
    simpa [prefixWord, tailWord_2187843, baseEnd_2187843] using wordTrace_append hprefix tailTrace_2187843
  have hstable : (prefixWord ++ tailWord_2187843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187843).length < 2 ^ (prefixWord ++ tailWord_2187843).sum := by decide
  have hdescent : baseEnd_2187843 < baseStart_2187843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187860 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 4, 2, 3]
def baseStart_2187860 : Nat := 118140960795 + 2187860 * 2 ^ 59
def prefixEnd_2187860 : Nat := 4983230072969 + 3 ^ 40 * 2187860 * 2
def baseEnd_2187860 : Nat := 1123423784745915221388221

theorem tailTrace_2187860 : CollatzResearch.WordTrace tailWord_2187860 prefixEnd_2187860 1123423784745915221388221 := by
  unfold tailWord_2187860
  simp only [CollatzResearch.WordTrace]
  refine ⟨39898904926882175792388517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53198539902509567723184689 39898904926882175792388517)
  ·
    refine ⟨7481044673790407961072847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39898904926882175792388517 7481044673790407961072847)
    ·
      refine ⟨11221567010685611941609271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7481044673790407961072847 11221567010685611941609271)
      ·
        refine ⟨16832350516028417912413907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11221567010685611941609271 16832350516028417912413907)
        ·
          refine ⟨25248525774042626868620861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16832350516028417912413907 25248525774042626868620861)
          ·
            refine ⟨9468197165265985075732823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25248525774042626868620861 9468197165265985075732823)
            ·
              refine ⟨14202295747898977613599235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9468197165265985075732823 14202295747898977613599235)
              ·
                refine ⟨21303443621848466420398853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14202295747898977613599235 21303443621848466420398853)
                ·
                  refine ⟨3994395679096587453824785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21303443621848466420398853 3994395679096587453824785)
                  ·
                    refine ⟨2995796759322440590368589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3994395679096587453824785 2995796759322440590368589)
                    ·
                      refine ⟨1123423784745915221388221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2995796759322440590368589 1123423784745915221388221)
                      ·
                        rfl

theorem cell23_2187860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_2187860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187860 prefixEnd_2187860 := by exact prefixLift 2187860
  have htrace : WordTrace (prefixWord ++ tailWord_2187860) baseStart_2187860 baseEnd_2187860 := by
    simpa [prefixWord, tailWord_2187860, baseEnd_2187860] using wordTrace_append hprefix tailTrace_2187860
  have hstable : (prefixWord ++ tailWord_2187860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187860).length < 2 ^ (prefixWord ++ tailWord_2187860).sum := by decide
  have hdescent : baseEnd_2187860 < baseStart_2187860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187863 : List Nat := [1, 1, 3, 2, 2, 2, 2, 4, 6]
def baseStart_2187863 : Nat := 118140960795 + 2187863 * 2 ^ 59
def prefixEnd_2187863 : Nat := 4983230072969 + 3 ^ 40 * 2187863 * 2
def baseEnd_2187863 : Nat := 124825036131986523294523

theorem tailTrace_2187863 : CollatzResearch.WordTrace tailWord_2187863 prefixEnd_2187863 124825036131986523294523 := by
  unfold tailWord_2187863
  simp only [CollatzResearch.WordTrace]
  refine ⟨79797919272753483097136243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53198612848502322064757495 79797919272753483097136243)
  ·
    refine ⟨119696878909130224645704365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79797919272753483097136243 119696878909130224645704365)
    ·
      refine ⟨44886329590923834242139137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119696878909130224645704365 44886329590923834242139137)
      ·
        refine ⟨33664747193192875681604353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44886329590923834242139137 33664747193192875681604353)
        ·
          refine ⟨25248560394894656761203265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33664747193192875681604353 25248560394894656761203265)
          ·
            refine ⟨18936420296170992570902449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25248560394894656761203265 18936420296170992570902449)
            ·
              refine ⟨14202315222128244428176837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18936420296170992570902449 14202315222128244428176837)
              ·
                refine ⟨2662934104149045830283157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14202315222128244428176837 2662934104149045830283157)
                ·
                  refine ⟨124825036131986523294523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2662934104149045830283157 124825036131986523294523)
                  ·
                    rfl

theorem cell23_2187863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 6].length) (baseStart_2187863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187863 prefixEnd_2187863 := by exact prefixLift 2187863
  have htrace : WordTrace (prefixWord ++ tailWord_2187863) baseStart_2187863 baseEnd_2187863 := by
    simpa [prefixWord, tailWord_2187863, baseEnd_2187863] using wordTrace_append hprefix tailTrace_2187863
  have hstable : (prefixWord ++ tailWord_2187863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187863).length < 2 ^ (prefixWord ++ tailWord_2187863).sum := by decide
  have hdescent : baseEnd_2187863 < baseStart_2187863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187894 : List Nat := [5, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3]
def baseStart_2187894 : Nat := 118140960795 + 2187894 * 2 ^ 59
def prefixEnd_2187894 : Nat := 4983230072969 + 3 ^ 40 * 2187894 * 2
def baseEnd_2187894 : Nat := 1123441243088168088363065

theorem tailTrace_2187894 : CollatzResearch.WordTrace tailWord_2187894 prefixEnd_2187894 1123441243088168088363065 := by
  unfold tailWord_2187894
  simp only [CollatzResearch.WordTrace]
  refine ⟨4987440620977573461969671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53199366623760783594343157 4987440620977573461969671)
  ·
    refine ⟨7481160931466360192954507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4987440620977573461969671 7481160931466360192954507)
    ·
      refine ⟨11221741397199540289431761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7481160931466360192954507 11221741397199540289431761)
      ·
        refine ⟨8416306047899655217073821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11221741397199540289431761 8416306047899655217073821)
        ·
          refine ⟨3156114767962370706402683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8416306047899655217073821 3156114767962370706402683)
          ·
            refine ⟨4734172151943556059604025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3156114767962370706402683 4734172151943556059604025)
            ·
              refine ⟨3550629113957667044703019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4734172151943556059604025 3550629113957667044703019)
              ·
                refine ⟨5325943670936500567054529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3550629113957667044703019 5325943670936500567054529)
                ·
                  refine ⟨3994457753202375425290897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5325943670936500567054529 3994457753202375425290897)
                  ·
                    refine ⟨2995843314901781568968173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3994457753202375425290897 2995843314901781568968173)
                    ·
                      refine ⟨1123441243088168088363065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2995843314901781568968173 1123441243088168088363065)
                      ·
                        rfl

theorem cell23_2187894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_2187894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187894 prefixEnd_2187894 := by exact prefixLift 2187894
  have htrace : WordTrace (prefixWord ++ tailWord_2187894) baseStart_2187894 baseEnd_2187894 := by
    simpa [prefixWord, tailWord_2187894, baseEnd_2187894] using wordTrace_append hprefix tailTrace_2187894
  have hstable : (prefixWord ++ tailWord_2187894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187894).length < 2 ^ (prefixWord ++ tailWord_2187894).sum := by decide
  have hdescent : baseEnd_2187894 < baseStart_2187894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187900 : List Nat := [2, 2, 2, 1, 1, 2, 2, 3, 1, 5, 2]
def baseStart_2187900 : Nat := 118140960795 + 2187900 * 2 ^ 59
def prefixEnd_2187900 : Nat := 4983230072969 + 3 ^ 40 * 2187900 * 2
def baseEnd_2187900 : Nat := 1123444323972095064888037

theorem tailTrace_2187900 : CollatzResearch.WordTrace tailWord_2187900 prefixEnd_2187900 1123444323972095064888037 := by
  unfold tailWord_2187900
  simp only [CollatzResearch.WordTrace]
  refine ⟨39899634386809719208116577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53199512515746292277488769 39899634386809719208116577)
  ·
    refine ⟨29924725790107289406087433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39899634386809719208116577 29924725790107289406087433)
    ·
      refine ⟨22443544342580467054565575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29924725790107289406087433 22443544342580467054565575)
      ·
        refine ⟨33665316513870700581848363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22443544342580467054565575 33665316513870700581848363)
        ·
          refine ⟨50497974770806050872772545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33665316513870700581848363 50497974770806050872772545)
          ·
            refine ⟨37873481078104538154579409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50497974770806050872772545 37873481078104538154579409)
            ·
              refine ⟨28405110808578403615934557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37873481078104538154579409 28405110808578403615934557)
              ·
                refine ⟨10651916553216901355975459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28405110808578403615934557 10651916553216901355975459)
                ·
                  refine ⟨15977874829825352033963189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10651916553216901355975459 15977874829825352033963189)
                  ·
                    refine ⟨1497925765296126753184049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15977874829825352033963189 1497925765296126753184049)
                    ·
                      refine ⟨1123444323972095064888037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1497925765296126753184049 1123444323972095064888037)
                      ·
                        rfl

theorem cell23_2187900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 1, 5, 2].length) (baseStart_2187900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187900 prefixEnd_2187900 := by exact prefixLift 2187900
  have htrace : WordTrace (prefixWord ++ tailWord_2187900) baseStart_2187900 baseEnd_2187900 := by
    simpa [prefixWord, tailWord_2187900, baseEnd_2187900] using wordTrace_append hprefix tailTrace_2187900
  have hstable : (prefixWord ++ tailWord_2187900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187900).length < 2 ^ (prefixWord ++ tailWord_2187900).sum := by decide
  have hdescent : baseEnd_2187900 < baseStart_2187900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187940 : List Nat := [2, 3, 1, 2, 2, 1, 4, 1, 1, 6]
def baseStart_2187940 : Nat := 118140960795 + 2187940 * 2 ^ 59
def prefixEnd_2187940 : Nat := 4983230072969 + 3 ^ 40 * 2187940 * 2
def baseEnd_2187940 : Nat := 374488287732758302795951

theorem tailTrace_2187940 : CollatzResearch.WordTrace tailWord_2187940 prefixEnd_2187940 374488287732758302795951 := by
  unfold tailWord_2187940
  simp only [CollatzResearch.WordTrace]
  refine ⟨39900363846737262623844637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53200485128983016831792849 39900363846737262623844637)
  ·
    refine ⟨14962636442526473483941739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39900363846737262623844637 14962636442526473483941739)
    ·
      refine ⟨22443954663789710225912609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14962636442526473483941739 22443954663789710225912609)
      ·
        refine ⟨16832965997842282669434457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22443954663789710225912609 16832965997842282669434457)
        ·
          refine ⟨12624724498381712002075843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16832965997842282669434457 12624724498381712002075843)
          ·
            refine ⟨18937086747572568003113765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12624724498381712002075843 18937086747572568003113765)
            ·
              refine ⟨3550703765169856500583831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18937086747572568003113765 3550703765169856500583831)
              ·
                refine ⟨5326055647754784750875747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3550703765169856500583831 5326055647754784750875747)
                ·
                  refine ⟨7989083471632177126313621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5326055647754784750875747 7989083471632177126313621)
                  ·
                    refine ⟨374488287732758302795951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7989083471632177126313621 374488287732758302795951)
                    ·
                      rfl

theorem cell23_2187940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_2187940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187940 prefixEnd_2187940 := by exact prefixLift 2187940
  have htrace : WordTrace (prefixWord ++ tailWord_2187940) baseStart_2187940 baseEnd_2187940 := by
    simpa [prefixWord, tailWord_2187940, baseEnd_2187940] using wordTrace_append hprefix tailTrace_2187940
  have hstable : (prefixWord ++ tailWord_2187940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187940).length < 2 ^ (prefixWord ++ tailWord_2187940).sum := by decide
  have hdescent : baseEnd_2187940 < baseStart_2187940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187967 : List Nat := [1, 1, 2, 2, 2, 5, 1, 3, 1, 2, 3]
def baseStart_2187967 : Nat := 118140960795 + 2187967 * 2 ^ 59
def prefixEnd_2187967 : Nat := 4983230072969 + 3 ^ 40 * 2187967 * 2
def baseEnd_2187967 : Nat := 1123478727175946302750229

theorem tailTrace_2187967 : CollatzResearch.WordTrace tailWord_2187967 prefixEnd_2187967 1123478727175946302750229 := by
  unfold tailWord_2187967
  simp only [CollatzResearch.WordTrace]
  refine ⟨79801712464376708858922155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53201141642917805905948103 79801712464376708858922155)
  ·
    refine ⟨119702568696565063288383233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79801712464376708858922155 119702568696565063288383233)
    ·
      refine ⟨89776926522423797466287425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119702568696565063288383233 89776926522423797466287425)
      ·
        refine ⟨67332694891817848099715569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89776926522423797466287425 67332694891817848099715569)
        ·
          refine ⟨50499521168863386074786677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67332694891817848099715569 50499521168863386074786677)
          ·
            refine ⟨4734330109580942444511251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50499521168863386074786677 4734330109580942444511251)
            ·
              refine ⟨7101495164371413666766877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4734330109580942444511251 7101495164371413666766877)
              ·
                refine ⟨2663060686639280125037579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7101495164371413666766877 2663060686639280125037579)
                ·
                  refine ⟨3994591029958920187556369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2663060686639280125037579 3994591029958920187556369)
                  ·
                    refine ⟨2995943272469190140667277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3994591029958920187556369 2995943272469190140667277)
                    ·
                      refine ⟨1123478727175946302750229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2995943272469190140667277 1123478727175946302750229)
                      ·
                        rfl

theorem cell23_2187967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 2, 3].length) (baseStart_2187967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187967 prefixEnd_2187967 := by exact prefixLift 2187967
  have htrace : WordTrace (prefixWord ++ tailWord_2187967) baseStart_2187967 baseEnd_2187967 := by
    simpa [prefixWord, tailWord_2187967, baseEnd_2187967] using wordTrace_append hprefix tailTrace_2187967
  have hstable : (prefixWord ++ tailWord_2187967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187967).length < 2 ^ (prefixWord ++ tailWord_2187967).sum := by decide
  have hdescent : baseEnd_2187967 < baseStart_2187967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188021 : List Nat := [1, 3, 6, 1, 2, 1, 9]
def baseStart_2188021 : Nat := 118140960795 + 2188021 * 2 ^ 59
def prefixEnd_2188021 : Nat := 4983230072969 + 3 ^ 40 * 2188021 * 2
def baseEnd_2188021 : Nat := 13870450063349248042901

theorem tailTrace_2188021 : CollatzResearch.WordTrace tailWord_2188021 prefixEnd_2188021 13870450063349248042901 := by
  unfold tailWord_2188021
  simp only [CollatzResearch.WordTrace]
  refine ⟨79803682006181076081387917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53202454670787384054258611 79803682006181076081387917)
  ·
    refine ⟨29926380752317903530520469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79803682006181076081387917 29926380752317903530520469)
    ·
      refine ⟨1402799097764901727993147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29926380752317903530520469 1402799097764901727993147)
      ·
        refine ⟨2104198646647352591989721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1402799097764901727993147 2104198646647352591989721)
        ·
          refine ⟨1578148984985514443992291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2104198646647352591989721 1578148984985514443992291)
          ·
            refine ⟨2367223477478271665988437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1578148984985514443992291 2367223477478271665988437)
            ·
              refine ⟨13870450063349248042901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2367223477478271665988437 13870450063349248042901)
              ·
                rfl

theorem cell23_2188021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 9].length) (baseStart_2188021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188021 prefixEnd_2188021 := by exact prefixLift 2188021
  have htrace : WordTrace (prefixWord ++ tailWord_2188021) baseStart_2188021 baseEnd_2188021 := by
    simpa [prefixWord, tailWord_2188021, baseEnd_2188021] using wordTrace_append hprefix tailTrace_2188021
  have hstable : (prefixWord ++ tailWord_2188021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188021).length < 2 ^ (prefixWord ++ tailWord_2188021).sum := by decide
  have hdescent : baseEnd_2188021 < baseStart_2188021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188124 : List Nat := [2, 2, 4, 2, 1, 1, 3, 1, 2, 5]
def baseStart_2188124 : Nat := 118140960795 + 2188124 * 2 ^ 59
def prefixEnd_2188124 : Nat := 4983230072969 + 3 ^ 40 * 2188124 * 2
def baseEnd_2188124 : Nat := 374519781212900729495669

theorem tailTrace_2188124 : CollatzResearch.WordTrace tailWord_2188124 prefixEnd_2188124 374519781212900729495669 := by
  unfold tailWord_2188124
  simp only [CollatzResearch.WordTrace]
  refine ⟨39903719362403962336193713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53204959149871949781591617 39903719362403962336193713)
  ·
    refine ⟨29927789521802971752145285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39903719362403962336193713 29927789521802971752145285)
    ·
      refine ⟨5611460535338057203527241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29927789521802971752145285 5611460535338057203527241)
      ·
        refine ⟨4208595401503542902645431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5611460535338057203527241 4208595401503542902645431)
        ·
          refine ⟨6312893102255314353968147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4208595401503542902645431 6312893102255314353968147)
          ·
            refine ⟨9469339653382971530952221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6312893102255314353968147 9469339653382971530952221)
            ·
              refine ⟨3551002370018614324107083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9469339653382971530952221 3551002370018614324107083)
              ·
                refine ⟨5326503555027921486160625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3551002370018614324107083 5326503555027921486160625)
                ·
                  refine ⟨3994877666270941114620469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5326503555027921486160625 3994877666270941114620469)
                  ·
                    refine ⟨374519781212900729495669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3994877666270941114620469 374519781212900729495669)
                    ·
                      rfl

theorem cell23_2188124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_2188124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188124 prefixEnd_2188124 := by exact prefixLift 2188124
  have htrace : WordTrace (prefixWord ++ tailWord_2188124) baseStart_2188124 baseEnd_2188124 := by
    simpa [prefixWord, tailWord_2188124, baseEnd_2188124] using wordTrace_append hprefix tailTrace_2188124
  have hstable : (prefixWord ++ tailWord_2188124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188124).length < 2 ^ (prefixWord ++ tailWord_2188124).sum := by decide
  have hdescent : baseEnd_2188124 < baseStart_2188124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188127 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 1, 6, 2]
def baseStart_2188127 : Nat := 118140960795 + 2188127 * 2 ^ 59
def prefixEnd_2188127 : Nat := 4983230072969 + 3 ^ 40 * 2188127 * 2
def baseEnd_2188127 : Nat := 1123560884080665676749493

theorem tailTrace_2188127 : CollatzResearch.WordTrace tailWord_2188127 prefixEnd_2188127 1123560884080665676749493 := by
  unfold tailWord_2188127
  simp only [CollatzResearch.WordTrace]
  refine ⟨79807548143797056184746635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53205032095864704123164423 79807548143797056184746635)
  ·
    refine ⟨119711322215695584277119953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79807548143797056184746635 119711322215695584277119953)
    ·
      refine ⟨89783491661771688207839965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119711322215695584277119953 89783491661771688207839965)
      ·
        refine ⟨33668809373164383077939987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89783491661771688207839965 33668809373164383077939987)
        ·
          refine ⟨50503214059746574616909981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33668809373164383077939987 50503214059746574616909981)
          ·
            refine ⟨18938705272404965481341243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50503214059746574616909981 18938705272404965481341243)
            ·
              refine ⟨28408057908607448222011865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18938705272404965481341243 28408057908607448222011865)
              ·
                refine ⟨21306043431455586166508899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28408057908607448222011865 21306043431455586166508899)
                ·
                  refine ⟨31959065147183379249763349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21306043431455586166508899 31959065147183379249763349)
                  ·
                    refine ⟨1498081178774220902332657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31959065147183379249763349 1498081178774220902332657)
                    ·
                      refine ⟨1123560884080665676749493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1498081178774220902332657 1123560884080665676749493)
                      ·
                        rfl

theorem cell23_2188127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 6, 2].length) (baseStart_2188127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188127 prefixEnd_2188127 := by exact prefixLift 2188127
  have htrace : WordTrace (prefixWord ++ tailWord_2188127) baseStart_2188127 baseEnd_2188127 := by
    simpa [prefixWord, tailWord_2188127, baseEnd_2188127] using wordTrace_append hprefix tailTrace_2188127
  have hstable : (prefixWord ++ tailWord_2188127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188127).length < 2 ^ (prefixWord ++ tailWord_2188127).sum := by decide
  have hdescent : baseEnd_2188127 < baseStart_2188127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188140 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 6]
def baseStart_2188140 : Nat := 118140960795 + 2188140 * 2 ^ 59
def prefixEnd_2188140 : Nat := 4983230072969 + 3 ^ 40 * 2188140 * 2
def baseEnd_2188140 : Nat := 1123567559329174125886933

theorem tailTrace_2188140 : CollatzResearch.WordTrace tailWord_2188140 prefixEnd_2188140 1123567559329174125886933 := by
  unfold tailWord_2188140
  simp only [CollatzResearch.WordTrace]
  refine ⟨39904011146374979702484937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53205348195166639603313249 39904011146374979702484937)
  ·
    refine ⟨29928008359781234776863703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39904011146374979702484937 29928008359781234776863703)
    ·
      refine ⟨44892012539671852165295555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29928008359781234776863703 44892012539671852165295555)
      ·
        refine ⟨67338018809507778247943333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44892012539671852165295555 67338018809507778247943333)
        ·
          refine ⟨12625878526782708421489375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67338018809507778247943333 12625878526782708421489375)
          ·
            refine ⟨18938817790174062632234063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12625878526782708421489375 18938817790174062632234063)
            ·
              refine ⟨28408226685261093948351095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18938817790174062632234063 28408226685261093948351095)
              ·
                refine ⟨42612340027891640922526643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28408226685261093948351095 42612340027891640922526643)
                ·
                  refine ⟨63918510041837461383789965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42612340027891640922526643 63918510041837461383789965)
                  ·
                    refine ⟨23969441265689048018921237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63918510041837461383789965 23969441265689048018921237)
                    ·
                      refine ⟨1123567559329174125886933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23969441265689048018921237 1123567559329174125886933)
                      ·
                        rfl

theorem cell23_2188140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_2188140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188140 prefixEnd_2188140 := by exact prefixLift 2188140
  have htrace : WordTrace (prefixWord ++ tailWord_2188140) baseStart_2188140 baseEnd_2188140 := by
    simpa [prefixWord, tailWord_2188140, baseEnd_2188140] using wordTrace_append hprefix tailTrace_2188140
  have hstable : (prefixWord ++ tailWord_2188140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188140).length < 2 ^ (prefixWord ++ tailWord_2188140).sum := by decide
  have hdescent : baseEnd_2188140 < baseStart_2188140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188147 : List Nat := [1, 1, 1, 2, 2, 1, 4, 4, 2, 2, 3]
def baseStart_2188147 : Nat := 118140960795 + 2188147 * 2 ^ 59
def prefixEnd_2188147 : Nat := 4983230072969 + 3 ^ 40 * 2188147 * 2
def baseEnd_2188147 : Nat := 1123571153693755598499401

theorem tailTrace_2188147 : CollatzResearch.WordTrace tailWord_2188147 prefixEnd_2188147 1123571153693755598499401 := by
  unfold tailWord_2188147
  simp only [CollatzResearch.WordTrace]
  refine ⟨79808277603724599600474695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53205518402483066400316463 79808277603724599600474695)
  ·
    refine ⟨119712416405586899400712043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79808277603724599600474695 119712416405586899400712043)
    ·
      refine ⟨179568624608380349101068065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119712416405586899400712043 179568624608380349101068065)
      ·
        refine ⟨134676468456285261825801049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179568624608380349101068065 134676468456285261825801049)
        ·
          refine ⟨101007351342213946369350787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134676468456285261825801049 101007351342213946369350787)
          ·
            refine ⟨151511027013320919554026181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101007351342213946369350787 151511027013320919554026181)
            ·
              refine ⟨28408317564997672416379909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 151511027013320919554026181 28408317564997672416379909)
              ·
                refine ⟨5326559543437063578071233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28408317564997672416379909 5326559543437063578071233)
                ·
                  refine ⟨3994919657577797683553425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5326559543437063578071233 3994919657577797683553425)
                  ·
                    refine ⟨2996189743183348262665069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3994919657577797683553425 2996189743183348262665069)
                    ·
                      refine ⟨1123571153693755598499401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2996189743183348262665069 1123571153693755598499401)
                      ·
                        rfl

theorem cell23_2188147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2, 3].length) (baseStart_2188147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188147 prefixEnd_2188147 := by exact prefixLift 2188147
  have htrace : WordTrace (prefixWord ++ tailWord_2188147) baseStart_2188147 baseEnd_2188147 := by
    simpa [prefixWord, tailWord_2188147, baseEnd_2188147] using wordTrace_append hprefix tailTrace_2188147
  have hstable : (prefixWord ++ tailWord_2188147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188147).length < 2 ^ (prefixWord ++ tailWord_2188147).sum := by decide
  have hdescent : baseEnd_2188147 < baseStart_2188147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188204 : List Nat := [2, 2, 1, 1, 1, 1, 2, 6, 2, 3, 2]
def baseStart_2188204 : Nat := 118140960795 + 2188204 * 2 ^ 59
def prefixEnd_2188204 : Nat := 4983230072969 + 3 ^ 40 * 2188204 * 2
def baseEnd_2188204 : Nat := 1123600422091061875486639

theorem tailTrace_2188204 : CollatzResearch.WordTrace tailWord_2188204 prefixEnd_2188204 1123600422091061875486639 := by
  unfold tailWord_2188204
  simp only [CollatzResearch.WordTrace]
  refine ⟨39905178282259049167649833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53206904376345398890199777 39905178282259049167649833)
  ·
    refine ⟨29928883711694286875737375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39905178282259049167649833 29928883711694286875737375)
    ·
      refine ⟨44893325567541430313606063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29928883711694286875737375 44893325567541430313606063)
      ·
        refine ⟨67339988351312145470409095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44893325567541430313606063 67339988351312145470409095)
        ·
          refine ⟨101009982526968218205613643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67339988351312145470409095 101009982526968218205613643)
          ·
            refine ⟨151514973790452327308420465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101009982526968218205613643 151514973790452327308420465)
            ·
              refine ⟨113636230342839245481315349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151514973790452327308420465 113636230342839245481315349)
              ·
                refine ⟨5326698297320589631936657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 113636230342839245481315349 5326698297320589631936657)
                ·
                  refine ⟨3995023722990442223952493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5326698297320589631936657 3995023722990442223952493)
                  ·
                    refine ⟨1498133896121415833982185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3995023722990442223952493 1498133896121415833982185)
                    ·
                      refine ⟨1123600422091061875486639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1498133896121415833982185 1123600422091061875486639)
                      ·
                        rfl

theorem cell23_2188204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 3, 2].length) (baseStart_2188204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188204 prefixEnd_2188204 := by exact prefixLift 2188204
  have htrace : WordTrace (prefixWord ++ tailWord_2188204) baseStart_2188204 baseEnd_2188204 := by
    simpa [prefixWord, tailWord_2188204, baseEnd_2188204] using wordTrace_append hprefix tailTrace_2188204
  have hstable : (prefixWord ++ tailWord_2188204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188204).length < 2 ^ (prefixWord ++ tailWord_2188204).sum := by decide
  have hdescent : baseEnd_2188204 < baseStart_2188204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188205 : List Nat := [1, 5, 2, 3, 2, 1, 1, 1, 3, 4]
def baseStart_2188205 : Nat := 118140960795 + 2188205 * 2 ^ 59
def prefixEnd_2188205 : Nat := 4983230072969 + 3 ^ 40 * 2188205 * 2
def baseEnd_2188205 : Nat := 374533645190572123858045

theorem tailTrace_2188205 : CollatzResearch.WordTrace tailWord_2188205 prefixEnd_2188205 374533645190572123858045 := by
  unfold tailWord_2188205
  simp only [CollatzResearch.WordTrace]
  refine ⟨79810393037514475506086069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53206928691676317004057379 79810393037514475506086069)
  ·
    refine ⟨7482224347266982078695569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79810393037514475506086069 7482224347266982078695569)
    ·
      refine ⟨5611668260450236559021677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7482224347266982078695569 5611668260450236559021677)
      ·
        refine ⟨2104375597668838709633129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5611668260450236559021677 2104375597668838709633129)
        ·
          refine ⟨1578281698251629032224847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2104375597668838709633129 1578281698251629032224847)
          ·
            refine ⟨2367422547377443548337271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1578281698251629032224847 2367422547377443548337271)
            ·
              refine ⟨3551133821066165322505907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2367422547377443548337271 3551133821066165322505907)
              ·
                refine ⟨5326700731599247983758861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3551133821066165322505907 5326700731599247983758861)
                ·
                  refine ⟨1997512774349717993909573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5326700731599247983758861 1997512774349717993909573)
                  ·
                    refine ⟨374533645190572123858045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1997512774349717993909573 374533645190572123858045)
                    ·
                      rfl

theorem cell23_2188205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_2188205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188205 prefixEnd_2188205 := by exact prefixLift 2188205
  have htrace : WordTrace (prefixWord ++ tailWord_2188205) baseStart_2188205 baseEnd_2188205 := by
    simpa [prefixWord, tailWord_2188205, baseEnd_2188205] using wordTrace_append hprefix tailTrace_2188205
  have hstable : (prefixWord ++ tailWord_2188205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188205).length < 2 ^ (prefixWord ++ tailWord_2188205).sum := by decide
  have hdescent : baseEnd_2188205 < baseStart_2188205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188244 : List Nat := [2, 4, 1, 2, 1, 3, 1, 2, 1, 6]
def baseStart_2188244 : Nat := 118140960795 + 2188244 * 2 ^ 59
def prefixEnd_2188244 : Nat := 4983230072969 + 3 ^ 40 * 2188244 * 2
def baseEnd_2188244 : Nat := 374540320439080572995485

theorem tailTrace_2188244 : CollatzResearch.WordTrace tailWord_2188244 prefixEnd_2188244 374540320439080572995485 := by
  unfold tailWord_2188244
  simp only [CollatzResearch.WordTrace]
  refine ⟨39905907742186592583377893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53207876989582123444503857 39905907742186592583377893)
  ·
    refine ⟨7482357701659986109383355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39905907742186592583377893 7482357701659986109383355)
    ·
      refine ⟨11223536552489979164075033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7482357701659986109383355 11223536552489979164075033)
      ·
        refine ⟨8417652414367484373056275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11223536552489979164075033 8417652414367484373056275)
        ·
          refine ⟨12626478621551226559584413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8417652414367484373056275 12626478621551226559584413)
          ·
            refine ⟨4734929483081709959844155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12626478621551226559584413 4734929483081709959844155)
            ·
              refine ⟨7102394224622564939766233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4734929483081709959844155 7102394224622564939766233)
              ·
                refine ⟨5326795668466923704824675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7102394224622564939766233 5326795668466923704824675)
                ·
                  refine ⟨7990193502700385557237013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5326795668466923704824675 7990193502700385557237013)
                  ·
                    refine ⟨374540320439080572995485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7990193502700385557237013 374540320439080572995485)
                    ·
                      rfl

theorem cell23_2188244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_2188244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188244 prefixEnd_2188244 := by exact prefixLift 2188244
  have htrace : WordTrace (prefixWord ++ tailWord_2188244) baseStart_2188244 baseEnd_2188244 := by
    simpa [prefixWord, tailWord_2188244, baseEnd_2188244] using wordTrace_append hprefix tailTrace_2188244
  have hstable : (prefixWord ++ tailWord_2188244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188244).length < 2 ^ (prefixWord ++ tailWord_2188244).sum := by decide
  have hdescent : baseEnd_2188244 < baseStart_2188244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188284 : List Nat := [2, 2, 2, 1, 2, 3, 1, 3, 1, 3, 3]
def baseStart_2188284 : Nat := 118140960795 + 2188284 * 2 ^ 59
def prefixEnd_2188284 : Nat := 4983230072969 + 3 ^ 40 * 2188284 * 2
def baseEnd_2188284 : Nat := 1123641500543421562486271

theorem tailTrace_2188284 : CollatzResearch.WordTrace tailWord_2188284 prefixEnd_2188284 1123641500543421562486271 := by
  unfold tailWord_2188284
  simp only [CollatzResearch.WordTrace]
  refine ⟨39906637202114135999105953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53208849602818847998807937 39906637202114135999105953)
  ·
    refine ⟨29929977901585601999329465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39906637202114135999105953 29929977901585601999329465)
    ·
      refine ⟨22447483426189201499497099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29929977901585601999329465 22447483426189201499497099)
      ·
        refine ⟨33671225139283802249245649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22447483426189201499497099 33671225139283802249245649)
        ·
          refine ⟨25253418854462851686934237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33671225139283802249245649 25253418854462851686934237)
          ·
            refine ⟨9470032070423569382600339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25253418854462851686934237 9470032070423569382600339)
            ·
              refine ⟨14205048105635354073900509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9470032070423569382600339 14205048105635354073900509)
              ·
                refine ⟨5326893039613257777712691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14205048105635354073900509 5326893039613257777712691)
                ·
                  refine ⟨7990339559419886666569037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5326893039613257777712691 7990339559419886666569037)
                  ·
                    refine ⟨2996377334782457499963389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7990339559419886666569037 2996377334782457499963389)
                    ·
                      refine ⟨1123641500543421562486271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2996377334782457499963389 1123641500543421562486271)
                      ·
                        rfl

theorem cell23_2188284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_2188284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188284 prefixEnd_2188284 := by exact prefixLift 2188284
  have htrace : WordTrace (prefixWord ++ tailWord_2188284) baseStart_2188284 baseEnd_2188284 := by
    simpa [prefixWord, tailWord_2188284, baseEnd_2188284] using wordTrace_append hprefix tailTrace_2188284
  have hstable : (prefixWord ++ tailWord_2188284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188284).length < 2 ^ (prefixWord ++ tailWord_2188284).sum := by decide
  have hdescent : baseEnd_2188284 < baseStart_2188284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188334 : List Nat := [4, 1, 3, 1, 1, 1, 1, 3, 2, 6]
def baseStart_2188334 : Nat := 118140960795 + 2188334 * 2 ^ 59
def prefixEnd_2188334 : Nat := 4983230072969 + 3 ^ 40 * 2188334 * 2
def baseEnd_2188334 : Nat := 374555724858715455620347

theorem tailTrace_2188334 : CollatzResearch.WordTrace tailWord_2188334 prefixEnd_2188334 374555724858715455620347 := by
  unfold tailWord_2188334
  simp only [CollatzResearch.WordTrace]
  refine ⟨9976887256755891317191507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53210065369364753691688037 9976887256755891317191507)
  ·
    refine ⟨14965330885133836975787261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9976887256755891317191507 14965330885133836975787261)
    ·
      refine ⟨5611999081925188865920223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14965330885133836975787261 5611999081925188865920223)
      ·
        refine ⟨8417998622887783298880335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5611999081925188865920223 8417998622887783298880335)
        ·
          refine ⟨12626997934331674948320503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8417998622887783298880335 12626997934331674948320503)
          ·
            refine ⟨18940496901497512422480755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12626997934331674948320503 18940496901497512422480755)
            ·
              refine ⟨28410745352246268633721133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18940496901497512422480755 28410745352246268633721133)
              ·
                refine ⟨10654029507092350737645425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28410745352246268633721133 10654029507092350737645425)
                ·
                  refine ⟨7990522130319263053234069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10654029507092350737645425 7990522130319263053234069)
                  ·
                    refine ⟨374555724858715455620347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7990522130319263053234069 374555724858715455620347)
                    ·
                      rfl

theorem cell23_2188334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_2188334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188334 prefixEnd_2188334 := by exact prefixLift 2188334
  have htrace : WordTrace (prefixWord ++ tailWord_2188334) baseStart_2188334 baseEnd_2188334 := by
    simpa [prefixWord, tailWord_2188334, baseEnd_2188334] using wordTrace_append hprefix tailTrace_2188334
  have hstable : (prefixWord ++ tailWord_2188334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188334).length < 2 ^ (prefixWord ++ tailWord_2188334).sum := by decide
  have hdescent : baseEnd_2188334 < baseStart_2188334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188377 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 3, 7]
def baseStart_2188377 : Nat := 118140960795 + 2188377 * 2 ^ 59
def prefixEnd_2188377 : Nat := 4983230072969 + 3 ^ 40 * 2188377 * 2
def baseEnd_2188377 : Nat := 374563084748096566207781

theorem tailTrace_2188377 : CollatzResearch.WordTrace tailWord_2188377 prefixEnd_2188377 374563084748096566207781 := by
  unfold tailWord_2188377
  simp only [CollatzResearch.WordTrace]
  refine ⟨79816666392891348881347385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53211110928594232587564923 79816666392891348881347385)
  ·
    refine ⟨59862499794668511661010539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79816666392891348881347385 59862499794668511661010539)
    ·
      refine ⟨89793749692002767491515809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59862499794668511661010539 89793749692002767491515809)
      ·
        refine ⟨67345312269002075618636857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89793749692002767491515809 67345312269002075618636857)
        ·
          refine ⟨50508984201751556713977643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67345312269002075618636857 50508984201751556713977643)
          ·
            refine ⟨75763476302627335070966465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50508984201751556713977643 75763476302627335070966465)
            ·
              refine ⟨56822607226970501303224849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75763476302627335070966465 56822607226970501303224849)
              ·
                refine ⟨42616955420227875977418637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56822607226970501303224849 42616955420227875977418637)
                ·
                  refine ⟨15981358282585453491531989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42616955420227875977418637 15981358282585453491531989)
                  ·
                    refine ⟨374563084748096566207781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15981358282585453491531989 374563084748096566207781)
                    ·
                      rfl

theorem cell23_2188377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 7].length) (baseStart_2188377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188377 prefixEnd_2188377 := by exact prefixLift 2188377
  have htrace : WordTrace (prefixWord ++ tailWord_2188377) baseStart_2188377 baseEnd_2188377 := by
    simpa [prefixWord, tailWord_2188377, baseEnd_2188377] using wordTrace_append hprefix tailTrace_2188377
  have hstable : (prefixWord ++ tailWord_2188377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188377).length < 2 ^ (prefixWord ++ tailWord_2188377).sum := by decide
  have hdescent : baseEnd_2188377 < baseStart_2188377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188392 : List Nat := [2, 1, 4, 4, 1, 1, 1, 3, 2, 2, 2]
def baseStart_2188392 : Nat := 118140960795 + 2188392 * 2 ^ 59
def prefixEnd_2188392 : Nat := 4983230072969 + 3 ^ 40 * 2188392 * 2
def baseEnd_2188392 : Nat := 1123696956454107139935775

theorem tailTrace_2188392 : CollatzResearch.WordTrace tailWord_2188392 prefixEnd_2188392 1123696956454107139935775 := by
  unfold tailWord_2188392
  simp only [CollatzResearch.WordTrace]
  refine ⟨39908606743918503221571715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53211475658558004295428953 39908606743918503221571715)
  ·
    refine ⟨59862910115877754832357573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39908606743918503221571715 59862910115877754832357573)
    ·
      refine ⟨11224295646727079031067045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59862910115877754832357573 11224295646727079031067045)
      ·
        refine ⟨2104555433761327318325071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11224295646727079031067045 2104555433761327318325071)
        ·
          refine ⟨3156833150641990977487607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2104555433761327318325071 3156833150641990977487607)
          ·
            refine ⟨4735249725962986466231411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3156833150641990977487607 4735249725962986466231411)
            ·
              refine ⟨7102874588944479699347117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4735249725962986466231411 7102874588944479699347117)
              ·
                refine ⟨2663577970854179887255169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7102874588944479699347117 2663577970854179887255169)
                ·
                  refine ⟨1997683478140634915441377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2663577970854179887255169 1997683478140634915441377)
                  ·
                    refine ⟨1498262608605476186581033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1997683478140634915441377 1498262608605476186581033)
                    ·
                      refine ⟨1123696956454107139935775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1498262608605476186581033 1123696956454107139935775)
                      ·
                        rfl

theorem cell23_2188392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_2188392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188392 prefixEnd_2188392 := by exact prefixLift 2188392
  have htrace : WordTrace (prefixWord ++ tailWord_2188392) baseStart_2188392 baseEnd_2188392 := by
    simpa [prefixWord, tailWord_2188392, baseEnd_2188392] using wordTrace_append hprefix tailTrace_2188392
  have hstable : (prefixWord ++ tailWord_2188392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188392).length < 2 ^ (prefixWord ++ tailWord_2188392).sum := by decide
  have hdescent : baseEnd_2188392 < baseStart_2188392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188458 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 5, 4]
def baseStart_2188458 : Nat := 118140960795 + 2188458 * 2 ^ 59
def prefixEnd_2188458 : Nat := 4983230072969 + 3 ^ 40 * 2188458 * 2
def baseEnd_2188458 : Nat := 374576948725767960570157

theorem tailTrace_2188458 : CollatzResearch.WordTrace tailWord_2188458 prefixEnd_2188458 374576948725767960570157 := by
  unfold tailWord_2188458
  simp only [CollatzResearch.WordTrace]
  refine ⟨19954905176399474928761507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53213080470398599810030685 19954905176399474928761507)
  ·
    refine ⟨29932357764599212393142261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19954905176399474928761507 29932357764599212393142261)
    ·
      refine ⟨2806158540431176161857087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29932357764599212393142261 2806158540431176161857087)
      ·
        refine ⟨4209237810646764242785631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2806158540431176161857087 4209237810646764242785631)
        ·
          refine ⟨6313856715970146364178447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4209237810646764242785631 6313856715970146364178447)
          ·
            refine ⟨9470785073955219546267671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6313856715970146364178447 9470785073955219546267671)
            ·
              refine ⟨14206177610932829319401507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9470785073955219546267671 14206177610932829319401507)
              ·
                refine ⟨21309266416399243979102261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14206177610932829319401507 21309266416399243979102261)
                ·
                  refine ⟨1997743726537429123040837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21309266416399243979102261 1997743726537429123040837)
                  ·
                    refine ⟨374576948725767960570157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1997743726537429123040837 374576948725767960570157)
                    ·
                      rfl

theorem cell23_2188458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_2188458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188458 prefixEnd_2188458 := by exact prefixLift 2188458
  have htrace : WordTrace (prefixWord ++ tailWord_2188458) baseStart_2188458 baseEnd_2188458 := by
    simpa [prefixWord, tailWord_2188458, baseEnd_2188458] using wordTrace_append hprefix tailTrace_2188458
  have hstable : (prefixWord ++ tailWord_2188458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188458).length < 2 ^ (prefixWord ++ tailWord_2188458).sum := by decide
  have hdescent : baseEnd_2188458 < baseStart_2188458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188464 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 3]
def baseStart_2188464 : Nat := 118140960795 + 2188464 * 2 ^ 59
def prefixEnd_2188464 : Nat := 4983230072969 + 3 ^ 40 * 2188464 * 2
def baseEnd_2188464 : Nat := 1123733927061230858235443

theorem tailTrace_2188464 : CollatzResearch.WordTrace tailWord_2188464 prefixEnd_2188464 1123733927061230858235443 := by
  unfold tailWord_2188464
  simp only [CollatzResearch.WordTrace]
  refine ⟨39909919771788081369882223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53213226362384108493176297 39909919771788081369882223)
  ·
    refine ⟨59864879657682122054823335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39909919771788081369882223 59864879657682122054823335)
    ·
      refine ⟨89797319486523183082235003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59864879657682122054823335 89797319486523183082235003)
      ·
        refine ⟨134695979229784774623352505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89797319486523183082235003 134695979229784774623352505)
        ·
          refine ⟨101021984422338580967514379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134695979229784774623352505 101021984422338580967514379)
          ·
            refine ⟨151532976633507871451271569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101021984422338580967514379 151532976633507871451271569)
            ·
              refine ⟨113649732475130903588453677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151532976633507871451271569 113649732475130903588453677)
              ·
                refine ⟨42618649678174088845670129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113649732475130903588453677 42618649678174088845670129)
                ·
                  refine ⟨31963987258630566634252597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42618649678174088845670129 31963987258630566634252597)
                  ·
                    refine ⟨2996623805496615621961181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31963987258630566634252597 2996623805496615621961181)
                    ·
                      refine ⟨1123733927061230858235443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2996623805496615621961181 1123733927061230858235443)
                      ·
                        rfl

theorem cell23_2188464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 3].length) (baseStart_2188464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188464 prefixEnd_2188464 := by exact prefixLift 2188464
  have htrace : WordTrace (prefixWord ++ tailWord_2188464) baseStart_2188464 baseEnd_2188464 := by
    simpa [prefixWord, tailWord_2188464, baseEnd_2188464] using wordTrace_append hprefix tailTrace_2188464
  have hstable : (prefixWord ++ tailWord_2188464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188464).length < 2 ^ (prefixWord ++ tailWord_2188464).sum := by decide
  have hdescent : baseEnd_2188464 < baseStart_2188464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188531 : List Nat := [1, 1, 1, 2, 2, 5, 1, 2, 4, 4]
def baseStart_2188531 : Nat := 118140960795 + 2188531 * 2 ^ 59
def prefixEnd_2188531 : Nat := 4983230072969 + 3 ^ 40 * 2188531 * 2
def baseEnd_2188531 : Nat := 374589443421694032032545

theorem tailTrace_2188531 : CollatzResearch.WordTrace tailWord_2188531 prefixEnd_2188531 374589443421694032032545 := by
  unfold tailWord_2188531
  simp only [CollatzResearch.WordTrace]
  refine ⟨79822283234333433182453447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53214855489555622121635631 79822283234333433182453447)
  ·
    refine ⟨119733424851500149773680171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79822283234333433182453447 119733424851500149773680171)
    ·
      refine ⟨179600137277250224660520257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119733424851500149773680171 179600137277250224660520257)
      ·
        refine ⟨134700102957937668495390193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179600137277250224660520257 134700102957937668495390193)
        ·
          refine ⟨101025077218453251371542645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134700102957937668495390193 101025077218453251371542645)
          ·
            refine ⟨9471100989229992316082123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101025077218453251371542645 9471100989229992316082123)
            ·
              refine ⟨14206651483844988474123185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9471100989229992316082123 14206651483844988474123185)
              ·
                refine ⟨10654988612883741355592389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14206651483844988474123185 10654988612883741355592389)
                ·
                  refine ⟨1997810364915701504173573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10654988612883741355592389 1997810364915701504173573)
                  ·
                    refine ⟨374589443421694032032545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1997810364915701504173573 374589443421694032032545)
                    ·
                      rfl

theorem cell23_2188531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4, 4].length) (baseStart_2188531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188531 prefixEnd_2188531 := by exact prefixLift 2188531
  have htrace : WordTrace (prefixWord ++ tailWord_2188531) baseStart_2188531 baseEnd_2188531 := by
    simpa [prefixWord, tailWord_2188531, baseEnd_2188531] using wordTrace_append hprefix tailTrace_2188531
  have hstable : (prefixWord ++ tailWord_2188531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188531).length < 2 ^ (prefixWord ++ tailWord_2188531).sum := by decide
  have hdescent : baseEnd_2188531 < baseStart_2188531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188541 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 7, 2, 3]
def baseStart_2188541 : Nat := 118140960795 + 2188541 * 2 ^ 59
def prefixEnd_2188541 : Nat := 4983230072969 + 3 ^ 40 * 2188541 * 2
def baseEnd_2188541 : Nat := 1123773465071627056972589

theorem tailTrace_2188541 : CollatzResearch.WordTrace tailWord_2188541 prefixEnd_2188541 1123773465071627056972589 := by
  unfold tailWord_2188541
  simp only [CollatzResearch.WordTrace]
  refine ⟨79822647964297204890317477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53215098642864803260211651 79822647964297204890317477)
  ·
    refine ⟨14966746493305725916934527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79822647964297204890317477 14966746493305725916934527)
    ·
      refine ⟨22450119739958588875401791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14966746493305725916934527 22450119739958588875401791)
      ·
        refine ⟨33675179609937883313102687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22450119739958588875401791 33675179609937883313102687)
        ·
          refine ⟨50512769414906824969654031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33675179609937883313102687 50512769414906824969654031)
          ·
            refine ⟨75769154122360237454481047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50512769414906824969654031 75769154122360237454481047)
            ·
              refine ⟨113653731183540356181721571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75769154122360237454481047 113653731183540356181721571)
              ·
                refine ⟨170480596775310534272582357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113653731183540356181721571 170480596775310534272582357)
                ·
                  refine ⟨3995638986921340647013649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 170480596775310534272582357 3995638986921340647013649)
                  ·
                    refine ⟨2996729240191005485260237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3995638986921340647013649 2996729240191005485260237)
                    ·
                      refine ⟨1123773465071627056972589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2996729240191005485260237 1123773465071627056972589)
                      ·
                        rfl

theorem cell23_2188541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_2188541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188541 prefixEnd_2188541 := by exact prefixLift 2188541
  have htrace : WordTrace (prefixWord ++ tailWord_2188541) baseStart_2188541 baseEnd_2188541 := by
    simpa [prefixWord, tailWord_2188541, baseEnd_2188541] using wordTrace_append hprefix tailTrace_2188541
  have hstable : (prefixWord ++ tailWord_2188541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188541).length < 2 ^ (prefixWord ++ tailWord_2188541).sum := by decide
  have hdescent : baseEnd_2188541 < baseStart_2188541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188548 : List Nat := [2, 3, 2, 2, 2, 1, 2, 1, 4, 4]
def baseStart_2188548 : Nat := 118140960795 + 2188548 * 2 ^ 59
def prefixEnd_2188548 : Nat := 4983230072969 + 3 ^ 40 * 2188548 * 2
def baseEnd_2188548 : Nat := 374592353145402843195019

theorem tailTrace_2188548 : CollatzResearch.WordTrace tailWord_2188548 prefixEnd_2188548 374592353145402843195019 := by
  unfold tailWord_2188548
  simp only [CollatzResearch.WordTrace]
  refine ⟨39911451637635922542911149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53215268850181230057214865 39911451637635922542911149)
  ·
    refine ⟨14966794364113470953591681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39911451637635922542911149 14966794364113470953591681)
    ·
      refine ⟨11225095773085103215193761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14966794364113470953591681 11225095773085103215193761)
      ·
        refine ⟨8418821829813827411395321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11225095773085103215193761 8418821829813827411395321)
        ·
          refine ⟨6314116372360370558546491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8418821829813827411395321 6314116372360370558546491)
          ·
            refine ⟨9471174558540555837819737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6314116372360370558546491 9471174558540555837819737)
            ·
              refine ⟨7103380918905416878364803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9471174558540555837819737 7103380918905416878364803)
              ·
                refine ⟨10655071378358125317547205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7103380918905416878364803 10655071378358125317547205)
                ·
                  refine ⟨1997825883442148497040101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10655071378358125317547205 1997825883442148497040101)
                  ·
                    refine ⟨374592353145402843195019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1997825883442148497040101 374592353145402843195019)
                    ·
                      rfl

theorem cell23_2188548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_2188548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188548 prefixEnd_2188548 := by exact prefixLift 2188548
  have htrace : WordTrace (prefixWord ++ tailWord_2188548) baseStart_2188548 baseEnd_2188548 := by
    simpa [prefixWord, tailWord_2188548, baseEnd_2188548] using wordTrace_append hprefix tailTrace_2188548
  have hstable : (prefixWord ++ tailWord_2188548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188548).length < 2 ^ (prefixWord ++ tailWord_2188548).sum := by decide
  have hdescent : baseEnd_2188548 < baseStart_2188548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188555 : List Nat := [1, 1, 1, 1, 5, 3, 3, 1, 3, 2, 2]
def baseStart_2188555 : Nat := 118140960795 + 2188555 * 2 ^ 59
def prefixEnd_2188555 : Nat := 4983230072969 + 3 ^ 40 * 2188555 * 2
def baseEnd_2188555 : Nat := 1123780653800790002197525

theorem tailTrace_2188555 : CollatzResearch.WordTrace tailWord_2188555 prefixEnd_2188555 1123780653800790002197525 := by
  unfold tailWord_2188555
  simp only [CollatzResearch.WordTrace]
  refine ⟨79823158586246485281327119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53215439057497656854218079 79823158586246485281327119)
  ·
    refine ⟨119734737879369727921990679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79823158586246485281327119 119734737879369727921990679)
    ·
      refine ⟨179602106819054591882986019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119734737879369727921990679 179602106819054591882986019)
      ·
        refine ⟨269403160228581887824479029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179602106819054591882986019 269403160228581887824479029)
        ·
          refine ⟨25256546271429551983544909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 269403160228581887824479029 25256546271429551983544909)
          ·
            refine ⟨9471204851786081993829341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25256546271429551983544909 9471204851786081993829341)
            ·
              refine ⟨3551701819419780747686003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9471204851786081993829341 3551701819419780747686003)
              ·
                refine ⟨5327552729129671121529005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3551701819419780747686003 5327552729129671121529005)
                ·
                  refine ⟨1997832273423626670573377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5327552729129671121529005 1997832273423626670573377)
                  ·
                    refine ⟨1498374205067720002930033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1997832273423626670573377 1498374205067720002930033)
                    ·
                      refine ⟨1123780653800790002197525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1498374205067720002930033 1123780653800790002197525)
                      ·
                        rfl

theorem cell23_2188555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3, 2, 2].length) (baseStart_2188555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188555 prefixEnd_2188555 := by exact prefixLift 2188555
  have htrace : WordTrace (prefixWord ++ tailWord_2188555) baseStart_2188555 baseEnd_2188555 := by
    simpa [prefixWord, tailWord_2188555, baseEnd_2188555] using wordTrace_append hprefix tailTrace_2188555
  have hstable : (prefixWord ++ tailWord_2188555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188555).length < 2 ^ (prefixWord ++ tailWord_2188555).sum := by decide
  have hdescent : baseEnd_2188555 < baseStart_2188555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188571 : List Nat := [1, 1, 1, 1, 1, 1, 5, 5, 1, 3, 3]
def baseStart_2188571 : Nat := 118140960795 + 2188571 * 2 ^ 59
def prefixEnd_2188571 : Nat := 4983230072969 + 3 ^ 40 * 2188571 * 2
def baseEnd_2188571 : Nat := 1123788869491261939597451

theorem tailTrace_2188571 : CollatzResearch.WordTrace tailWord_2188571 prefixEnd_2188571 1123788869491261939597451 := by
  unfold tailWord_2188571
  simp only [CollatzResearch.WordTrace]
  refine ⟨79823742154188520013909567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53215828102792346675939711 79823742154188520013909567)
  ·
    refine ⟨119735613231282780020864351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79823742154188520013909567 119735613231282780020864351)
    ·
      refine ⟨179603419846924170031296527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119735613231282780020864351 179603419846924170031296527)
      ·
        refine ⟨269405129770386255046944791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179603419846924170031296527 269405129770386255046944791)
        ·
          refine ⟨404107694655579382570417187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269405129770386255046944791 404107694655579382570417187)
          ·
            refine ⟨606161541983369073855625781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404107694655579382570417187 606161541983369073855625781)
            ·
              refine ⟨56827644560940850673964917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 606161541983369073855625781 56827644560940850673964917)
              ·
                refine ⟨5327591677588204750684211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56827644560940850673964917 5327591677588204750684211)
                ·
                  refine ⟨7991387516382307126026317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5327591677588204750684211 7991387516382307126026317)
                  ·
                    refine ⟨2996770318643365172259869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7991387516382307126026317 2996770318643365172259869)
                    ·
                      refine ⟨1123788869491261939597451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2996770318643365172259869 1123788869491261939597451)
                      ·
                        rfl

theorem cell23_2188571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3, 3].length) (baseStart_2188571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188571 prefixEnd_2188571 := by exact prefixLift 2188571
  have htrace : WordTrace (prefixWord ++ tailWord_2188571) baseStart_2188571 baseEnd_2188571 := by
    simpa [prefixWord, tailWord_2188571, baseEnd_2188571] using wordTrace_append hprefix tailTrace_2188571
  have hstable : (prefixWord ++ tailWord_2188571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188571).length < 2 ^ (prefixWord ++ tailWord_2188571).sum := by decide
  have hdescent : baseEnd_2188571 < baseStart_2188571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188645 : List Nat := [1, 3, 1, 3, 1, 2, 2, 2, 4, 2, 2]
def baseStart_2188645 : Nat := 118140960795 + 2188645 * 2 ^ 59
def prefixEnd_2188645 : Nat := 4983230072969 + 3 ^ 40 * 2188645 * 2
def baseEnd_2188645 : Nat := 1123826867059694650072111

theorem tailTrace_2188645 : CollatzResearch.WordTrace tailWord_2188645 prefixEnd_2188645 1123826867059694650072111 := by
  unfold tailWord_2188645
  simp only [CollatzResearch.WordTrace]
  refine ⟨79826441155920430652103389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53217627437280287101402259 79826441155920430652103389)
  ·
    refine ⟨29934915433470161494538771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79826441155920430652103389 29934915433470161494538771)
    ·
      refine ⟨44902373150205242241808157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29934915433470161494538771 44902373150205242241808157)
      ·
        refine ⟨16838389931326965840678059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44902373150205242241808157 16838389931326965840678059)
        ·
          refine ⟨25257584896990448761017089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16838389931326965840678059 25257584896990448761017089)
          ·
            refine ⟨18943188672742836570762817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25257584896990448761017089 18943188672742836570762817)
            ·
              refine ⟨14207391504557127428072113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18943188672742836570762817 14207391504557127428072113)
              ·
                refine ⟨10655543628417845571054085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14207391504557127428072113 10655543628417845571054085)
                ·
                  refine ⟨1997914430328346044572641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10655543628417845571054085 1997914430328346044572641)
                  ·
                    refine ⟨1498435822746259533429481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1997914430328346044572641 1498435822746259533429481)
                    ·
                      refine ⟨1123826867059694650072111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1498435822746259533429481 1123826867059694650072111)
                      ·
                        rfl

theorem cell23_2188645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_2188645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188645 prefixEnd_2188645 := by exact prefixLift 2188645
  have htrace : WordTrace (prefixWord ++ tailWord_2188645) baseStart_2188645 baseEnd_2188645 := by
    simpa [prefixWord, tailWord_2188645, baseEnd_2188645] using wordTrace_append hprefix tailTrace_2188645
  have hstable : (prefixWord ++ tailWord_2188645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188645).length < 2 ^ (prefixWord ++ tailWord_2188645).sum := by decide
  have hdescent : baseEnd_2188645 < baseStart_2188645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188668 : List Nat := [2, 2, 2, 1, 1, 1, 3, 6, 5]
def baseStart_2188668 : Nat := 118140960795 + 2188668 * 2 ^ 59
def prefixEnd_2188668 : Nat := 4983230072969 + 3 ^ 40 * 2188668 * 2
def baseEnd_2188668 : Nat := 124870964123860895564945

theorem tailTrace_2188668 : CollatzResearch.WordTrace tailWord_2188668 prefixEnd_2188668 124870964123860895564945 := by
  unfold tailWord_2188668
  simp only [CollatzResearch.WordTrace]
  refine ⟨39913640017418552790095329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53218186689891403720127105 39913640017418552790095329)
  ·
    refine ⟨29935230013063914592571497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39913640017418552790095329 29935230013063914592571497)
    ·
      refine ⟨22451422509797935944428623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29935230013063914592571497 22451422509797935944428623)
      ·
        refine ⟨33677133764696903916642935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22451422509797935944428623 33677133764696903916642935)
        ·
          refine ⟨50515700647045355874964403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33677133764696903916642935 50515700647045355874964403)
          ·
            refine ⟨75773550970568033812446605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50515700647045355874964403 75773550970568033812446605)
            ·
              refine ⟨28415081613963012679667477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75773550970568033812446605 28415081613963012679667477)
              ·
                refine ⟨1331956950654516219359413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28415081613963012679667477 1331956950654516219359413)
                ·
                  refine ⟨124870964123860895564945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1331956950654516219359413 124870964123860895564945)
                  ·
                    rfl

theorem cell23_2188668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6, 5].length) (baseStart_2188668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188668 prefixEnd_2188668 := by exact prefixLift 2188668
  have htrace : WordTrace (prefixWord ++ tailWord_2188668) baseStart_2188668 baseEnd_2188668 := by
    simpa [prefixWord, tailWord_2188668, baseEnd_2188668] using wordTrace_append hprefix tailTrace_2188668
  have hstable : (prefixWord ++ tailWord_2188668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188668).length < 2 ^ (prefixWord ++ tailWord_2188668).sum := by decide
  have hdescent : baseEnd_2188668 < baseStart_2188668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188679 : List Nat := [1, 1, 4, 2, 2, 3, 3, 1, 2, 2, 2]
def baseStart_2188679 : Nat := 118140960795 + 2188679 * 2 ^ 59
def prefixEnd_2188679 : Nat := 4983230072969 + 3 ^ 40 * 2188679 * 2
def baseEnd_2188679 : Nat := 1123844325401947517046955

theorem tailTrace_2188679 : CollatzResearch.WordTrace tailWord_2188679 prefixEnd_2188679 1123844325401947517046955 := by
  unfold tailWord_2188679
  simp only [CollatzResearch.WordTrace]
  refine ⟨79827681237797254458841091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53218454158531502972560727 79827681237797254458841091)
  ·
    refine ⟨119741521856695881688261637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79827681237797254458841091 119741521856695881688261637)
    ·
      refine ⟨22451535348130477816549057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119741521856695881688261637 22451535348130477816549057)
      ·
        refine ⟨16838651511097858362411793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22451535348130477816549057 16838651511097858362411793)
        ·
          refine ⟨12628988633323393771808845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16838651511097858362411793 12628988633323393771808845)
          ·
            refine ⟨4735870737496272664428317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12628988633323393771808845 4735870737496272664428317)
            ·
              refine ⟨1775951526561102249160619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4735870737496272664428317 1775951526561102249160619)
              ·
                refine ⟨2663927289841653373740929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1775951526561102249160619 2663927289841653373740929)
                ·
                  refine ⟨1997945467381240030305697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2663927289841653373740929 1997945467381240030305697)
                  ·
                    refine ⟨1498459100535930022729273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1997945467381240030305697 1498459100535930022729273)
                    ·
                      refine ⟨1123844325401947517046955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1498459100535930022729273 1123844325401947517046955)
                      ·
                        rfl

theorem cell23_2188679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_2188679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188679 prefixEnd_2188679 := by exact prefixLift 2188679
  have htrace : WordTrace (prefixWord ++ tailWord_2188679) baseStart_2188679 baseEnd_2188679 := by
    simpa [prefixWord, tailWord_2188679, baseEnd_2188679] using wordTrace_append hprefix tailTrace_2188679
  have hstable : (prefixWord ++ tailWord_2188679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188679).length < 2 ^ (prefixWord ++ tailWord_2188679).sum := by decide
  have hdescent : baseEnd_2188679 < baseStart_2188679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188698 : List Nat := [3, 1, 1, 4, 1, 1, 2, 3, 2, 5]
def baseStart_2188698 : Nat := 118140960795 + 2188698 * 2 ^ 59
def prefixEnd_2188698 : Nat := 4983230072969 + 3 ^ 40 * 2188698 * 2
def baseEnd_2188698 : Nat := 374618027178127647569789

theorem tailTrace_2188698 : CollatzResearch.WordTrace tailWord_2188698 prefixEnd_2188698 374618027178127647569789 := by
  unfold tailWord_2188698
  simp only [CollatzResearch.WordTrace]
  refine ⟨19957093556182105175945687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53218916149818947135855165 19957093556182105175945687)
  ·
    refine ⟨29935640334273157763918531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19957093556182105175945687 29935640334273157763918531)
    ·
      refine ⟨44903460501409736645877797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29935640334273157763918531 44903460501409736645877797)
      ·
        refine ⟨8419398844014325621102087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44903460501409736645877797 8419398844014325621102087)
        ·
          refine ⟨12629098266021488431653131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8419398844014325621102087 12629098266021488431653131)
          ·
            refine ⟨18943647399032232647479697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12629098266021488431653131 18943647399032232647479697)
            ·
              refine ⟨14207735549274174485609773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18943647399032232647479697 14207735549274174485609773)
              ·
                refine ⟨5327900830977815432103665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14207735549274174485609773 5327900830977815432103665)
                ·
                  refine ⟨3995925623233361574077749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5327900830977815432103665 3995925623233361574077749)
                  ·
                    refine ⟨374618027178127647569789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3995925623233361574077749 374618027178127647569789)
                    ·
                      rfl

theorem cell23_2188698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 2, 5].length) (baseStart_2188698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188698 prefixEnd_2188698 := by exact prefixLift 2188698
  have htrace : WordTrace (prefixWord ++ tailWord_2188698) baseStart_2188698 baseEnd_2188698 := by
    simpa [prefixWord, tailWord_2188698, baseEnd_2188698] using wordTrace_append hprefix tailTrace_2188698
  have hstable : (prefixWord ++ tailWord_2188698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188698).length < 2 ^ (prefixWord ++ tailWord_2188698).sum := by decide
  have hdescent : baseEnd_2188698 < baseStart_2188698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188775 : List Nat := [1, 1, 5, 2, 1, 3, 2, 2, 6]
def baseStart_2188775 : Nat := 118140960795 + 2188775 * 2 ^ 59
def prefixEnd_2188775 : Nat := 4983230072969 + 3 ^ 40 * 2188775 * 2
def baseEnd_2188775 : Nat := 124877068838308793494057

theorem tailTrace_2188775 : CollatzResearch.WordTrace tailWord_2188775 prefixEnd_2188775 124877068838308793494057 := by
  unfold tailWord_2188775
  simp only [CollatzResearch.WordTrace]
  refine ⟨79831182645449462854335779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53220788430299641902890519 79831182645449462854335779)
  ·
    refine ⟨119746773968174194281503669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79831182645449462854335779 119746773968174194281503669)
    ·
      refine ⟨11226260059516330713890969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119746773968174194281503669 11226260059516330713890969)
      ·
        refine ⟨8419695044637248035418227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11226260059516330713890969 8419695044637248035418227)
        ·
          refine ⟨12629542566955872053127341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8419695044637248035418227 12629542566955872053127341)
          ·
            refine ⟨4736078462608452019922753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12629542566955872053127341 4736078462608452019922753)
            ·
              refine ⟨3552058846956339014942065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4736078462608452019922753 3552058846956339014942065)
              ·
                refine ⟨2664044135217254261206549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3552058846956339014942065 2664044135217254261206549)
                ·
                  refine ⟨124877068838308793494057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2664044135217254261206549 124877068838308793494057)
                  ·
                    rfl

theorem cell23_2188775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 6].length) (baseStart_2188775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188775 prefixEnd_2188775 := by exact prefixLift 2188775
  have htrace : WordTrace (prefixWord ++ tailWord_2188775) baseStart_2188775 baseEnd_2188775 := by
    simpa [prefixWord, tailWord_2188775, baseEnd_2188775] using wordTrace_append hprefix tailTrace_2188775
  have hstable : (prefixWord ++ tailWord_2188775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188775).length < 2 ^ (prefixWord ++ tailWord_2188775).sum := by decide
  have hdescent : baseEnd_2188775 < baseStart_2188775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188806 : List Nat := [6, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_2188806 : Nat := 118140960795 + 2188806 * 2 ^ 59
def prefixEnd_2188806 : Nat := 4983230072969 + 3 ^ 40 * 2188806 * 2
def baseEnd_2188806 : Nat := 1123909537445068520158871

theorem tailTrace_2188806 : CollatzResearch.WordTrace tailWord_2188806 prefixEnd_2188806 1123909537445068520158871 := by
  unfold tailWord_2188806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2494759790885536098397321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53221542205558103432476181 2494759790885536098397321)
  ·
    refine ⟨1871069843164152073797991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2494759790885536098397321 1871069843164152073797991)
    ·
      refine ⟨2806604764746228110696987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1871069843164152073797991 2806604764746228110696987)
      ·
        refine ⟨4209907147119342166045481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2806604764746228110696987 4209907147119342166045481)
        ·
          refine ⟨3157430360339506624534111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4209907147119342166045481 3157430360339506624534111)
          ·
            refine ⟨4736145540509259936801167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3157430360339506624534111 4736145540509259936801167)
            ·
              refine ⟨7104218310763889905201751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4736145540509259936801167 7104218310763889905201751)
              ·
                refine ⟨10656327466145834857802627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7104218310763889905201751 10656327466145834857802627)
                ·
                  refine ⟨15984491199218752286703941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10656327466145834857802627 15984491199218752286703941)
                  ·
                    refine ⟨2997092099853516053756989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15984491199218752286703941 2997092099853516053756989)
                    ·
                      refine ⟨1123909537445068520158871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2997092099853516053756989 1123909537445068520158871)
                      ·
                        rfl

theorem cell23_2188806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_2188806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188806 prefixEnd_2188806 := by exact prefixLift 2188806
  have htrace : WordTrace (prefixWord ++ tailWord_2188806) baseStart_2188806 baseEnd_2188806 := by
    simpa [prefixWord, tailWord_2188806, baseEnd_2188806] using wordTrace_append hprefix tailTrace_2188806
  have hstable : (prefixWord ++ tailWord_2188806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188806).length < 2 ^ (prefixWord ++ tailWord_2188806).sum := by decide
  have hdescent : baseEnd_2188806 < baseStart_2188806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188812 : List Nat := [2, 2, 1, 2, 5, 1, 1, 1, 1, 5, 2]
def baseStart_2188812 : Nat := 118140960795 + 2188812 * 2 ^ 59
def prefixEnd_2188812 : Nat := 4983230072969 + 3 ^ 40 * 2188812 * 2
def baseEnd_2188812 : Nat := 1123912618328995496683843

theorem tailTrace_2188812 : CollatzResearch.WordTrace tailWord_2188812 prefixEnd_2188812 1123912618328995496683843 := by
  unfold tailWord_2188812
  simp only [CollatzResearch.WordTrace]
  refine ⟨39916266073157709086716345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53221688097543612115621793 39916266073157709086716345)
  ·
    refine ⟨29937199554868281815037259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39916266073157709086716345 29937199554868281815037259)
    ·
      refine ⟨44905799332302422722555889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29937199554868281815037259 44905799332302422722555889)
      ·
        refine ⟨33679349499226817041916917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44905799332302422722555889 33679349499226817041916917)
        ·
          refine ⟨3157439015552514097679711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33679349499226817041916917 3157439015552514097679711)
          ·
            refine ⟨4736158523328771146519567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3157439015552514097679711 4736158523328771146519567)
            ·
              refine ⟨7104237784993156719779351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4736158523328771146519567 7104237784993156719779351)
              ·
                refine ⟨10656356677489735079669027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7104237784993156719779351 10656356677489735079669027)
                ·
                  refine ⟨15984535016234602619503541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10656356677489735079669027 15984535016234602619503541)
                  ·
                    refine ⟨1498550157771993995578457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15984535016234602619503541 1498550157771993995578457)
                    ·
                      refine ⟨1123912618328995496683843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1498550157771993995578457 1123912618328995496683843)
                      ·
                        rfl

theorem cell23_2188812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 1, 5, 2].length) (baseStart_2188812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188812 prefixEnd_2188812 := by exact prefixLift 2188812
  have htrace : WordTrace (prefixWord ++ tailWord_2188812) baseStart_2188812 baseEnd_2188812 := by
    simpa [prefixWord, tailWord_2188812, baseEnd_2188812] using wordTrace_append hprefix tailTrace_2188812
  have hstable : (prefixWord ++ tailWord_2188812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188812).length < 2 ^ (prefixWord ++ tailWord_2188812).sum := by decide
  have hdescent : baseEnd_2188812 < baseStart_2188812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188813 : List Nat := [1, 7, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_2188813 : Nat := 118140960795 + 2188813 * 2 ^ 59
def prefixEnd_2188813 : Nat := 4983230072969 + 3 ^ 40 * 2188813 * 2
def baseEnd_2188813 : Nat := 374637710603216664257113

theorem tailTrace_2188813 : CollatzResearch.WordTrace tailWord_2188813 prefixEnd_2188813 374637710603216664257113 := by
  unfold tailWord_2188813
  simp only [CollatzResearch.WordTrace]
  refine ⟨79832568619311795344219093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53221712412874530229479395 79832568619311795344219093)
  ·
    refine ⟨1871075827015120203380135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 79832568619311795344219093 1871075827015120203380135)
    ·
      refine ⟨2806613740522680305070203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1871075827015120203380135 2806613740522680305070203)
      ·
        refine ⟨4209920610784020457605305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2806613740522680305070203 4209920610784020457605305)
        ·
          refine ⟨3157440458088015343203979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4209920610784020457605305 3157440458088015343203979)
          ·
            refine ⟨4736160687132023014805969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3157440458088015343203979 4736160687132023014805969)
            ·
              refine ⟨3552120515349017261104477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4736160687132023014805969 3552120515349017261104477)
              ·
                refine ⟨1332045193255881472914179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3552120515349017261104477 1332045193255881472914179)
                ·
                  refine ⟨1998067789883822209371269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1332045193255881472914179 1998067789883822209371269)
                  ·
                    refine ⟨374637710603216664257113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1998067789883822209371269 374637710603216664257113)
                    ·
                      rfl

theorem cell23_2188813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_2188813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188813 prefixEnd_2188813 := by exact prefixLift 2188813
  have htrace : WordTrace (prefixWord ++ tailWord_2188813) baseStart_2188813 baseEnd_2188813 := by
    simpa [prefixWord, tailWord_2188813, baseEnd_2188813] using wordTrace_append hprefix tailTrace_2188813
  have hstable : (prefixWord ++ tailWord_2188813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188813).length < 2 ^ (prefixWord ++ tailWord_2188813).sum := by decide
  have hdescent : baseEnd_2188813 < baseStart_2188813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188819 : List Nat := [1, 1, 1, 2, 1, 7, 2, 3, 1, 1, 3]
def baseStart_2188819 : Nat := 118140960795 + 2188819 * 2 ^ 59
def prefixEnd_2188819 : Nat := 4983230072969 + 3 ^ 40 * 2188819 * 2
def baseEnd_2188819 : Nat := 1123916212693576969296311

theorem tailTrace_2188819 : CollatzResearch.WordTrace tailWord_2188819 prefixEnd_2188819 1123916212693576969296311 := by
  unfold tailWord_2188819
  simp only [CollatzResearch.WordTrace]
  refine ⟨79832787457290058368937511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53221858304860038912625007 79832787457290058368937511)
  ·
    refine ⟨119749181185935087553406267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79832787457290058368937511 119749181185935087553406267)
    ·
      refine ⟨179623771778902631330109401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119749181185935087553406267 179623771778902631330109401)
      ·
        refine ⟨134717828834176973497582051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179623771778902631330109401 134717828834176973497582051)
        ·
          refine ⟨202076743251265460246373077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134717828834176973497582051 202076743251265460246373077)
          ·
            refine ⟨4736173669951534224524369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 202076743251265460246373077 4736173669951534224524369)
            ·
              refine ⟨3552130252463650668393277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4736173669951534224524369 3552130252463650668393277)
              ·
                refine ⟨1332048844673869000647479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3552130252463650668393277 1332048844673869000647479)
                ·
                  refine ⟨1998073267010803500971219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1332048844673869000647479 1998073267010803500971219)
                  ·
                    refine ⟨2997109900516205251456829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1998073267010803500971219 2997109900516205251456829)
                    ·
                      refine ⟨1123916212693576969296311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2997109900516205251456829 1123916212693576969296311)
                      ·
                        rfl

theorem cell23_2188819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3, 1, 1, 3].length) (baseStart_2188819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188819 prefixEnd_2188819 := by exact prefixLift 2188819
  have htrace : WordTrace (prefixWord ++ tailWord_2188819) baseStart_2188819 baseEnd_2188819 := by
    simpa [prefixWord, tailWord_2188819, baseEnd_2188819] using wordTrace_append hprefix tailTrace_2188819
  have hstable : (prefixWord ++ tailWord_2188819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188819).length < 2 ^ (prefixWord ++ tailWord_2188819).sum := by decide
  have hdescent : baseEnd_2188819 < baseStart_2188819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188855 : List Nat := [1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 4]
def baseStart_2188855 : Nat := 118140960795 + 2188855 * 2 ^ 59
def prefixEnd_2188855 : Nat := 4983230072969 + 3 ^ 40 * 2188855 * 2
def baseEnd_2188855 : Nat := 1123934697997138828446145

theorem tailTrace_2188855 : CollatzResearch.WordTrace tailWord_2188855 prefixEnd_2188855 1123934697997138828446145 := by
  unfold tailWord_2188855
  simp only [CollatzResearch.WordTrace]
  refine ⟨79834100485159636517248019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53222733656773091011498679 79834100485159636517248019)
  ·
    refine ⟨119751150727739454775872029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79834100485159636517248019 119751150727739454775872029)
    ·
      refine ⟨44906681522902295540952011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119751150727739454775872029 44906681522902295540952011)
      ·
        refine ⟨67360022284353443311428017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44906681522902295540952011 67360022284353443311428017)
        ·
          refine ⟨50520016713265082483571013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67360022284353443311428017 50520016713265082483571013)
          ·
            refine ⟨9472503133737202965669565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50520016713265082483571013 9472503133737202965669565)
            ·
              refine ⟨3552188675151451112126087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9472503133737202965669565 3552188675151451112126087)
              ·
                refine ⟨5328283012727176668189131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3552188675151451112126087 5328283012727176668189131)
                ·
                  refine ⟨7992424519090765002283697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5328283012727176668189131 7992424519090765002283697)
                  ·
                    refine ⟨5994318389318073751712773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7992424519090765002283697 5994318389318073751712773)
                    ·
                      refine ⟨1123934697997138828446145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5994318389318073751712773 1123934697997138828446145)
                      ·
                        rfl

theorem cell23_2188855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 4].length) (baseStart_2188855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188855 prefixEnd_2188855 := by exact prefixLift 2188855
  have htrace : WordTrace (prefixWord ++ tailWord_2188855) baseStart_2188855 baseEnd_2188855 := by
    simpa [prefixWord, tailWord_2188855, baseEnd_2188855] using wordTrace_append hprefix tailTrace_2188855
  have hstable : (prefixWord ++ tailWord_2188855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188855).length < 2 ^ (prefixWord ++ tailWord_2188855).sum := by decide
  have hdescent : baseEnd_2188855 < baseStart_2188855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188870 : List Nat := [6, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3]
def baseStart_2188870 : Nat := 118140960795 + 2188870 * 2 ^ 59
def prefixEnd_2188870 : Nat := 4983230072969 + 3 ^ 40 * 2188870 * 2
def baseEnd_2188870 : Nat := 1123942400206956269758577

theorem tailTrace_2188870 : CollatzResearch.WordTrace tailWord_2188870 prefixEnd_2188870 1123942400206956269758577 := by
  unfold tailWord_2188870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2494832736878290439970127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53223098386736862719362709 2494832736878290439970127)
  ·
    refine ⟨3742249105317435659955191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2494832736878290439970127 3742249105317435659955191)
    ·
      refine ⟨5613373657976153489932787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3742249105317435659955191 5613373657976153489932787)
      ·
        refine ⟨8420060486964230234899181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5613373657976153489932787 8420060486964230234899181)
        ·
          refine ⟨3157522682611586338087193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8420060486964230234899181 3157522682611586338087193)
          ·
            refine ⟨2368142011958689753565395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3157522682611586338087193 2368142011958689753565395)
            ·
              refine ⟨3552213017938034630348093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2368142011958689753565395 3552213017938034630348093)
              ·
                refine ⟨1332079881726762986380535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3552213017938034630348093 1332079881726762986380535)
                ·
                  refine ⟨1998119822590144479570803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1332079881726762986380535 1998119822590144479570803)
                  ·
                    refine ⟨2997179733885216719356205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1998119822590144479570803 2997179733885216719356205)
                    ·
                      refine ⟨1123942400206956269758577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2997179733885216719356205 1123942400206956269758577)
                      ·
                        rfl

theorem cell23_2188870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_2188870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188870 prefixEnd_2188870 := by exact prefixLift 2188870
  have htrace : WordTrace (prefixWord ++ tailWord_2188870) baseStart_2188870 baseEnd_2188870 := by
    simpa [prefixWord, tailWord_2188870, baseEnd_2188870] using wordTrace_append hprefix tailTrace_2188870
  have hstable : (prefixWord ++ tailWord_2188870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188870).length < 2 ^ (prefixWord ++ tailWord_2188870).sum := by decide
  have hdescent : baseEnd_2188870 < baseStart_2188870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188876 : List Nat := [2, 2, 1, 3, 1, 3, 3, 3, 1, 2, 2]
def baseStart_2188876 : Nat := 118140960795 + 2188876 * 2 ^ 59
def prefixEnd_2188876 : Nat := 4983230072969 + 3 ^ 40 * 2188876 * 2
def baseEnd_2188876 : Nat := 1123945481090883246283549

theorem tailTrace_2188876 : CollatzResearch.WordTrace tailWord_2188876 prefixEnd_2188876 1123945481090883246283549 := by
  unfold tailWord_2188876
  simp only [CollatzResearch.WordTrace]
  refine ⟨39917433209041778551881241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53223244278722371402508321 39917433209041778551881241)
  ·
    refine ⟨29938074906781333913910931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39917433209041778551881241 29938074906781333913910931)
    ·
      refine ⟨44907112360172000870866397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29938074906781333913910931 44907112360172000870866397)
      ·
        refine ⟨16840167135064500326574899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44907112360172000870866397 16840167135064500326574899)
        ·
          refine ⟨25260250702596750489862349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16840167135064500326574899 25260250702596750489862349)
          ·
            refine ⟨9472594013473781433698381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25260250702596750489862349 9472594013473781433698381)
            ·
              refine ⟨3552222755052668037636893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9472594013473781433698381 3552222755052668037636893)
              ·
                refine ⟨1332083533144750514113835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3552222755052668037636893 1332083533144750514113835)
                ·
                  refine ⟨1998125299717125771170753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1332083533144750514113835 1998125299717125771170753)
                  ·
                    refine ⟨1498593974787844328378065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1998125299717125771170753 1498593974787844328378065)
                    ·
                      refine ⟨1123945481090883246283549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1498593974787844328378065 1123945481090883246283549)
                      ·
                        rfl

theorem cell23_2188876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_2188876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188876 prefixEnd_2188876 := by exact prefixLift 2188876
  have htrace : WordTrace (prefixWord ++ tailWord_2188876) baseStart_2188876 baseEnd_2188876 := by
    simpa [prefixWord, tailWord_2188876, baseEnd_2188876] using wordTrace_append hprefix tailTrace_2188876
  have hstable : (prefixWord ++ tailWord_2188876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188876).length < 2 ^ (prefixWord ++ tailWord_2188876).sum := by decide
  have hdescent : baseEnd_2188876 < baseStart_2188876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188878 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 1, 9]
def baseStart_2188878 : Nat := 118140960795 + 2188878 * 2 ^ 59
def prefixEnd_2188878 : Nat := 4983230072969 + 3 ^ 40 * 2188878 * 2
def baseEnd_2188878 : Nat := 374648836017397412819513

theorem tailTrace_2188878 : CollatzResearch.WordTrace tailWord_2188878 prefixEnd_2188878 374648836017397412819513 := by
  unfold tailWord_2188878
  simp only [CollatzResearch.WordTrace]
  refine ⟨9979367420509538930666911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53223292909384207630223525 9979367420509538930666911)
  ·
    refine ⟨14969051130764308396000367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9979367420509538930666911 14969051130764308396000367)
    ·
      refine ⟨22453576696146462594000551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14969051130764308396000367 22453576696146462594000551)
      ·
        refine ⟨33680365044219693891000827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22453576696146462594000551 33680365044219693891000827)
        ·
          refine ⟨50520547566329540836501241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33680365044219693891000827 50520547566329540836501241)
          ·
            refine ⟨37890410674747155627375931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50520547566329540836501241 37890410674747155627375931)
            ·
              refine ⟨56835616012120733441063897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37890410674747155627375931 56835616012120733441063897)
              ·
                refine ⟨42626712009090550080797923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56835616012120733441063897 42626712009090550080797923)
                ·
                  refine ⟨63940068013635825121196885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42626712009090550080797923 63940068013635825121196885)
                  ·
                    refine ⟨374648836017397412819513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 63940068013635825121196885 374648836017397412819513)
                    ·
                      rfl

theorem cell23_2188878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_2188878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188878 prefixEnd_2188878 := by exact prefixLift 2188878
  have htrace : WordTrace (prefixWord ++ tailWord_2188878) baseStart_2188878 baseEnd_2188878 := by
    simpa [prefixWord, tailWord_2188878, baseEnd_2188878] using wordTrace_append hprefix tailTrace_2188878
  have hstable : (prefixWord ++ tailWord_2188878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188878).length < 2 ^ (prefixWord ++ tailWord_2188878).sum := by decide
  have hdescent : baseEnd_2188878 < baseStart_2188878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188888 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 4, 2, 5]
def baseStart_2188888 : Nat := 118140960795 + 2188888 * 2 ^ 59
def prefixEnd_2188888 : Nat := 4983230072969 + 3 ^ 40 * 2188888 * 2
def baseEnd_2188888 : Nat := 1123951642858737199333493

theorem tailTrace_2188888 : CollatzResearch.WordTrace tailWord_2188888 prefixEnd_2188888 1123951642858737199333493 := by
  unfold tailWord_2188888
  simp only [CollatzResearch.WordTrace]
  refine ⟨39917652047020041576599659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53223536062693388768799545 39917652047020041576599659)
  ·
    refine ⟨59876478070530062364899489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39917652047020041576599659 59876478070530062364899489)
    ·
      refine ⟨44907358552897546773674617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59876478070530062364899489 44907358552897546773674617)
      ·
        refine ⟨33680518914673160080255963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44907358552897546773674617 33680518914673160080255963)
        ·
          refine ⟨50520778372009740120383945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33680518914673160080255963 50520778372009740120383945)
          ·
            refine ⟨37890583779007305090287959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50520778372009740120383945 37890583779007305090287959)
            ·
              refine ⟨56835875668510957635431939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37890583779007305090287959 56835875668510957635431939)
              ·
                refine ⟨85253813502766436453147909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56835875668510957635431939 85253813502766436453147909)
                ·
                  refine ⟨15985090031768706834965233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85253813502766436453147909 15985090031768706834965233)
                  ·
                    refine ⟨11988817523826530126223925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15985090031768706834965233 11988817523826530126223925)
                    ·
                      refine ⟨1123951642858737199333493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11988817523826530126223925 1123951642858737199333493)
                      ·
                        rfl

theorem cell23_2188888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_2188888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188888 prefixEnd_2188888 := by exact prefixLift 2188888
  have htrace : WordTrace (prefixWord ++ tailWord_2188888) baseStart_2188888 baseEnd_2188888 := by
    simpa [prefixWord, tailWord_2188888, baseEnd_2188888] using wordTrace_append hprefix tailTrace_2188888
  have hstable : (prefixWord ++ tailWord_2188888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188888).length < 2 ^ (prefixWord ++ tailWord_2188888).sum := by decide
  have hdescent : baseEnd_2188888 < baseStart_2188888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188908 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 1, 8]
def baseStart_2188908 : Nat := 118140960795 + 2188908 * 2 ^ 59
def prefixEnd_2188908 : Nat := 4983230072969 + 3 ^ 40 * 2188908 * 2
def baseEnd_2188908 : Nat := 374653970823942373694467

theorem tailTrace_2188908 : CollatzResearch.WordTrace tailWord_2188908 prefixEnd_2188908 374653970823942373694467 := by
  unfold tailWord_2188908
  simp only [CollatzResearch.WordTrace]
  refine ⟨39918016776983813284463689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53224022369311751045951585 39918016776983813284463689)
  ·
    refine ⟨29938512582737859963347767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39918016776983813284463689 29938512582737859963347767)
    ·
      refine ⟨44907768874106789945021651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29938512582737859963347767 44907768874106789945021651)
      ·
        refine ⟨67361653311160184917532477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44907768874106789945021651 67361653311160184917532477)
        ·
          refine ⟨25260619991685069344074679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67361653311160184917532477 25260619991685069344074679)
          ·
            refine ⟨37890929987527604016112019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25260619991685069344074679 37890929987527604016112019)
            ·
              refine ⟨56836394981291406024168029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37890929987527604016112019 56836394981291406024168029)
              ·
                refine ⟨21313648117984277259063011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56836394981291406024168029 21313648117984277259063011)
                ·
                  refine ⟨31970472176976415888594517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21313648117984277259063011 31970472176976415888594517)
                  ·
                    refine ⟨374653970823942373694467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31970472176976415888594517 374653970823942373694467)
                    ·
                      rfl

theorem cell23_2188908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_2188908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188908 prefixEnd_2188908 := by exact prefixLift 2188908
  have htrace : WordTrace (prefixWord ++ tailWord_2188908) baseStart_2188908 baseEnd_2188908 := by
    simpa [prefixWord, tailWord_2188908, baseEnd_2188908] using wordTrace_append hprefix tailTrace_2188908
  have hstable : (prefixWord ++ tailWord_2188908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188908).length < 2 ^ (prefixWord ++ tailWord_2188908).sum := by decide
  have hdescent : baseEnd_2188908 < baseStart_2188908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188935 : List Nat := [1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 5]
def baseStart_2188935 : Nat := 118140960795 + 2188935 * 2 ^ 59
def prefixEnd_2188935 : Nat := 4983230072969 + 3 ^ 40 * 2188935 * 2
def baseEnd_2188935 : Nat := 1123975776449498515445777

theorem tailTrace_2188935 : CollatzResearch.WordTrace tailWord_2188935 prefixEnd_2188935 1123975776449498515445777 := by
  unfold tailWord_2188935
  simp only [CollatzResearch.WordTrace]
  refine ⟨79837018324869810180160259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53224678883246540120106839 79837018324869810180160259)
  ·
    refine ⟨119755527487304715270240389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79837018324869810180160259 119755527487304715270240389)
    ·
      refine ⟨22454161403869634113170073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119755527487304715270240389 22454161403869634113170073)
      ·
        refine ⟨16840621052902225584877555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22454161403869634113170073 16840621052902225584877555)
        ·
          refine ⟨25260931579353338377316333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16840621052902225584877555 25260931579353338377316333)
          ·
            refine ⟨9472849342257501891493625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25260931579353338377316333 9472849342257501891493625)
            ·
              refine ⟨7104637006693126418620219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9472849342257501891493625 7104637006693126418620219)
              ·
                refine ⟨10656955510039689627930329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7104637006693126418620219 10656955510039689627930329)
                ·
                  refine ⟨7992716632529767220947747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10656955510039689627930329 7992716632529767220947747)
                  ·
                    refine ⟨11989074948794650831421621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7992716632529767220947747 11989074948794650831421621)
                    ·
                      refine ⟨1123975776449498515445777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11989074948794650831421621 1123975776449498515445777)
                      ·
                        rfl

theorem cell23_2188935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_2188935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188935 prefixEnd_2188935 := by exact prefixLift 2188935
  have htrace : WordTrace (prefixWord ++ tailWord_2188935) baseStart_2188935 baseEnd_2188935 := by
    simpa [prefixWord, tailWord_2188935, baseEnd_2188935] using wordTrace_append hprefix tailTrace_2188935
  have hstable : (prefixWord ++ tailWord_2188935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188935).length < 2 ^ (prefixWord ++ tailWord_2188935).sum := by decide
  have hdescent : baseEnd_2188935 < baseStart_2188935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2188965 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 1, 5, 3]
def baseStart_2188965 : Nat := 118140960795 + 2188965 * 2 ^ 59
def prefixEnd_2188965 : Nat := 4983230072969 + 3 ^ 40 * 2188965 * 2
def baseEnd_2188965 : Nat := 1123991180869133398070639

theorem tailTrace_2188965 : CollatzResearch.WordTrace tailWord_2188965 prefixEnd_2188965 1123991180869133398070639 := by
  unfold tailWord_2188965
  simp only [CollatzResearch.WordTrace]
  refine ⟨79838112514761125303752349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53225408343174083535834899 79838112514761125303752349)
  ·
    refine ⟨29939292193035421988907131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79838112514761125303752349 29939292193035421988907131)
    ·
      refine ⟨44908938289553132983360697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29939292193035421988907131 44908938289553132983360697)
      ·
        refine ⟨33681703717164849737520523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44908938289553132983360697 33681703717164849737520523)
        ·
          refine ⟨50522555575747274606280785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33681703717164849737520523 50522555575747274606280785)
          ·
            refine ⟨37891916681810455954710589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50522555575747274606280785 37891916681810455954710589)
            ·
              refine ⟨14209468755678920983016471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37891916681810455954710589 14209468755678920983016471)
              ·
                refine ⟨21314203133518381474524707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14209468755678920983016471 21314203133518381474524707)
                ·
                  refine ⟨31971304700277572211787061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21314203133518381474524707 31971304700277572211787061)
                  ·
                    refine ⟨2997309815651022394855037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31971304700277572211787061 2997309815651022394855037)
                    ·
                      refine ⟨1123991180869133398070639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2997309815651022394855037 1123991180869133398070639)
                      ·
                        rfl

theorem cell23_2188965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_2188965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2188965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2188965 prefixEnd_2188965 := by exact prefixLift 2188965
  have htrace : WordTrace (prefixWord ++ tailWord_2188965) baseStart_2188965 baseEnd_2188965 := by
    simpa [prefixWord, tailWord_2188965, baseEnd_2188965] using wordTrace_append hprefix tailTrace_2188965
  have hstable : (prefixWord ++ tailWord_2188965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2188965).length < 2 ^ (prefixWord ++ tailWord_2188965).sum := by decide
  have hdescent : baseEnd_2188965 < baseStart_2188965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2188965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189042 : List Nat := [3, 2, 1, 3, 1, 1, 1, 3, 1, 4, 3]
def baseStart_2189042 : Nat := 118140960795 + 2189042 * 2 ^ 59
def prefixEnd_2189042 : Nat := 4983230072969 + 3 ^ 40 * 2189042 * 2
def baseEnd_2189042 : Nat := 1124030718879529596807785

theorem tailTrace_2189042 : CollatzResearch.WordTrace tailWord_2189042 prefixEnd_2189042 1124030718879529596807785 := by
  unfold tailWord_2189042
  simp only [CollatzResearch.WordTrace]
  refine ⟨19960230233870541863576345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53227280623654778302870253 19960230233870541863576345)
  ·
    refine ⟨14970172675402906397682259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19960230233870541863576345 14970172675402906397682259)
    ·
      refine ⟨22455259013104359596523389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14970172675402906397682259 22455259013104359596523389)
      ·
        refine ⟨8420722129914134848696271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22455259013104359596523389 8420722129914134848696271)
        ·
          refine ⟨12631083194871202273044407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8420722129914134848696271 12631083194871202273044407)
          ·
            refine ⟨18946624792306803409566611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12631083194871202273044407 18946624792306803409566611)
            ·
              refine ⟨28419937188460205114349917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18946624792306803409566611 28419937188460205114349917)
              ·
                refine ⟨10657476445672576917881219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28419937188460205114349917 10657476445672576917881219)
                ·
                  refine ⟨15986214668508865376821829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10657476445672576917881219 15986214668508865376821829)
                  ·
                    refine ⟨2997415250345412258154093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15986214668508865376821829 2997415250345412258154093)
                    ·
                      refine ⟨1124030718879529596807785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2997415250345412258154093 1124030718879529596807785)
                      ·
                        rfl

theorem cell23_2189042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_2189042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189042 prefixEnd_2189042 := by exact prefixLift 2189042
  have htrace : WordTrace (prefixWord ++ tailWord_2189042) baseStart_2189042 baseEnd_2189042 := by
    simpa [prefixWord, tailWord_2189042, baseEnd_2189042] using wordTrace_append hprefix tailTrace_2189042
  have hstable : (prefixWord ++ tailWord_2189042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189042).length < 2 ^ (prefixWord ++ tailWord_2189042).sum := by decide
  have hdescent : baseEnd_2189042 < baseStart_2189042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189079 : List Nat := [1, 1, 3, 4, 2, 1, 4, 1, 6]
def baseStart_2189079 : Nat := 118140960795 + 2189079 * 2 ^ 59
def prefixEnd_2189079 : Nat := 4983230072969 + 3 ^ 40 * 2189079 * 2
def baseEnd_2189079 : Nat := 124894413073749550227235

theorem tailTrace_2189079 : CollatzResearch.WordTrace tailWord_2189079 prefixEnd_2189079 124894413073749550227235 := by
  unfold tailWord_2189079
  simp only [CollatzResearch.WordTrace]
  refine ⟨79842270436348122773402291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53228180290898748515601527 79842270436348122773402291)
  ·
    refine ⟨119763405654522184160103437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79842270436348122773402291 119763405654522184160103437)
    ·
      refine ⟨44911277120445819060038789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119763405654522184160103437 44911277120445819060038789)
      ·
        refine ⟨8420864460083591073757273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44911277120445819060038789 8420864460083591073757273)
        ·
          refine ⟨6315648345062693305317955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8420864460083591073757273 6315648345062693305317955)
          ·
            refine ⟨9473472517594039957976933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6315648345062693305317955 9473472517594039957976933)
            ·
              refine ⟨1776276097048882492120675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9473472517594039957976933 1776276097048882492120675)
              ·
                refine ⟨2664414145573323738181013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1776276097048882492120675 2664414145573323738181013)
                ·
                  refine ⟨124894413073749550227235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2664414145573323738181013 124894413073749550227235)
                  ·
                    rfl

theorem cell23_2189079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 6].length) (baseStart_2189079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189079 prefixEnd_2189079 := by exact prefixLift 2189079
  have htrace : WordTrace (prefixWord ++ tailWord_2189079) baseStart_2189079 baseEnd_2189079 := by
    simpa [prefixWord, tailWord_2189079, baseEnd_2189079] using wordTrace_append hprefix tailTrace_2189079
  have hstable : (prefixWord ++ tailWord_2189079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189079).length < 2 ^ (prefixWord ++ tailWord_2189079).sum := by decide
  have hdescent : baseEnd_2189079 < baseStart_2189079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189123 : List Nat := [1, 1, 1, 3, 1, 5, 4, 2, 1, 1, 3]
def baseStart_2189123 : Nat := 118140960795 + 2189123 * 2 ^ 59
def prefixEnd_2189123 : Nat := 4983230072969 + 3 ^ 40 * 2189123 * 2
def baseEnd_2189123 : Nat := 1124072310812543779894913

theorem tailTrace_2189123 : CollatzResearch.WordTrace tailWord_2189123 prefixEnd_2189123 1124072310812543779894913 := by
  unfold tailWord_2189123
  simp only [CollatzResearch.WordTrace]
  refine ⟨79843875248188718288004023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53229250165459145525336015 79843875248188718288004023)
  ·
    refine ⟨119765812872283077432006035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79843875248188718288004023 119765812872283077432006035)
    ·
      refine ⟨179648719308424616148009053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119765812872283077432006035 179648719308424616148009053)
      ·
        refine ⟨67368269740659231055503395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179648719308424616148009053 67368269740659231055503395)
        ·
          refine ⟨101052404610988846583255093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67368269740659231055503395 101052404610988846583255093)
          ·
            refine ⟨9473662932280204367180165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101052404610988846583255093 9473662932280204367180165)
            ·
              refine ⟨1776311799802538318846281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9473662932280204367180165 1776311799802538318846281)
              ·
                refine ⟨1332233849851903739134711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1776311799802538318846281 1332233849851903739134711)
                ·
                  refine ⟨1998350774777855608702067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1332233849851903739134711 1998350774777855608702067)
                  ·
                    refine ⟨2997526162166783413053101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1998350774777855608702067 2997526162166783413053101)
                    ·
                      refine ⟨1124072310812543779894913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2997526162166783413053101 1124072310812543779894913)
                      ·
                        rfl

theorem cell23_2189123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2, 1, 1, 3].length) (baseStart_2189123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189123 prefixEnd_2189123 := by exact prefixLift 2189123
  have htrace : WordTrace (prefixWord ++ tailWord_2189123) baseStart_2189123 baseEnd_2189123 := by
    simpa [prefixWord, tailWord_2189123, baseEnd_2189123] using wordTrace_append hprefix tailTrace_2189123
  have hstable : (prefixWord ++ tailWord_2189123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189123).length < 2 ^ (prefixWord ++ tailWord_2189123).sum := by decide
  have hdescent : baseEnd_2189123 < baseStart_2189123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189126 : List Nat := [6, 1, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_2189126 : Nat := 118140960795 + 2189126 * 2 ^ 59
def prefixEnd_2189126 : Nat := 4983230072969 + 3 ^ 40 * 2189126 * 2
def baseEnd_2189126 : Nat := 374691283751502422719133

theorem tailTrace_2189126 : CollatzResearch.WordTrace tailWord_2189126 prefixEnd_2189126 374691283751502422719133 := by
  unfold tailWord_2189126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2495124520849307806261351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53229323111451899866908821 2495124520849307806261351)
  ·
    refine ⟨3742686781273961709392027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2495124520849307806261351 3742686781273961709392027)
    ·
      refine ⟨5614030171910942564088041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3742686781273961709392027 5614030171910942564088041)
      ·
        refine ⟨4210522628933206923066031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5614030171910942564088041 4210522628933206923066031)
        ·
          refine ⟨6315783943399810384599047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4210522628933206923066031 6315783943399810384599047)
          ·
            refine ⟨9473675915099715576898571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6315783943399810384599047 9473675915099715576898571)
            ·
              refine ⟨14210513872649573365347857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9473675915099715576898571 14210513872649573365347857)
              ·
                refine ⟨10657885404487180024010893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14210513872649573365347857 10657885404487180024010893)
                ·
                  refine ⟨3996707026682692509004085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10657885404487180024010893 3996707026682692509004085)
                  ·
                    refine ⟨374691283751502422719133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3996707026682692509004085 374691283751502422719133)
                    ·
                      rfl

theorem cell23_2189126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_2189126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189126 prefixEnd_2189126 := by exact prefixLift 2189126
  have htrace : WordTrace (prefixWord ++ tailWord_2189126) baseStart_2189126 baseEnd_2189126 := by
    simpa [prefixWord, tailWord_2189126, baseEnd_2189126] using wordTrace_append hprefix tailTrace_2189126
  have hstable : (prefixWord ++ tailWord_2189126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189126).length < 2 ^ (prefixWord ++ tailWord_2189126).sum := by decide
  have hdescent : baseEnd_2189126 < baseStart_2189126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189146 : List Nat := [3, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2]
def baseStart_2189146 : Nat := 118140960795 + 2189146 * 2 ^ 59
def prefixEnd_2189146 : Nat := 4983230072969 + 3 ^ 40 * 2189146 * 2
def baseEnd_2189146 : Nat := 1124084120867597189907307

theorem tailTrace_2189146 : CollatzResearch.WordTrace tailWord_2189146 prefixEnd_2189146 1124084120867597189907307 := by
  unfold tailWord_2189146
  simp only [CollatzResearch.WordTrace]
  refine ⟨19961178531776348304022823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53229809418070262144060861 19961178531776348304022823)
  ·
    refine ⟨29941767797664522456034235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19961178531776348304022823 29941767797664522456034235)
    ·
      refine ⟨44912651696496783684051353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29941767797664522456034235 44912651696496783684051353)
      ·
        refine ⟨33684488772372587763038515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44912651696496783684051353 33684488772372587763038515)
        ·
          refine ⟨50526733158558881644557773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33684488772372587763038515 50526733158558881644557773)
          ·
            refine ⟨18947524934459580616709165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50526733158558881644557773 18947524934459580616709165)
            ·
              refine ⟨7105321850422342731265937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18947524934459580616709165 7105321850422342731265937)
              ·
                refine ⟨5328991387816757048449453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7105321850422342731265937 5328991387816757048449453)
                ·
                  refine ⟨1998371770431283893168545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5328991387816757048449453 1998371770431283893168545)
                  ·
                    refine ⟨1498778827823462919876409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1998371770431283893168545 1498778827823462919876409)
                    ·
                      refine ⟨1124084120867597189907307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1498778827823462919876409 1124084120867597189907307)
                      ·
                        rfl

theorem cell23_2189146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2].length) (baseStart_2189146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189146 prefixEnd_2189146 := by exact prefixLift 2189146
  have htrace : WordTrace (prefixWord ++ tailWord_2189146) baseStart_2189146 baseEnd_2189146 := by
    simpa [prefixWord, tailWord_2189146, baseEnd_2189146] using wordTrace_append hprefix tailTrace_2189146
  have hstable : (prefixWord ++ tailWord_2189146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189146).length < 2 ^ (prefixWord ++ tailWord_2189146).sum := by decide
  have hdescent : baseEnd_2189146 < baseStart_2189146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189219 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 3, 4, 2]
def baseStart_2189219 : Nat := 118140960795 + 2189219 * 2 ^ 59
def prefixEnd_2189219 : Nat := 4983230072969 + 3 ^ 40 * 2189219 * 2
def baseEnd_2189219 : Nat := 1124121604955375404294471

theorem tailTrace_2189219 : CollatzResearch.WordTrace tailWord_2189219 prefixEnd_2189219 1124121604955375404294471 := by
  unfold tailWord_2189219
  simp only [CollatzResearch.WordTrace]
  refine ⟨79847376655840926683498711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53231584437227284455665807 79847376655840926683498711)
  ·
    refine ⟨119771064983761390025248067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79847376655840926683498711 119771064983761390025248067)
    ·
      refine ⟨179656597475642085037872101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119771064983761390025248067 179656597475642085037872101)
      ·
        refine ⟨33685612026682890944601019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 179656597475642085037872101 33685612026682890944601019)
        ·
          refine ⟨50528418040024336416901529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33685612026682890944601019 50528418040024336416901529)
          ·
            refine ⟨37896313530018252312676147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50528418040024336416901529 37896313530018252312676147)
            ·
              refine ⟨56844470295027378469014221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37896313530018252312676147 56844470295027378469014221)
              ·
                refine ⟨21316676360635266925880333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56844470295027378469014221 21316676360635266925880333)
                ·
                  refine ⟨7993753635238225097205125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21316676360635266925880333 7993753635238225097205125)
                  ·
                    refine ⟨1498828806607167205725961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7993753635238225097205125 1498828806607167205725961)
                    ·
                      refine ⟨1124121604955375404294471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1498828806607167205725961 1124121604955375404294471)
                      ·
                        rfl

theorem cell23_2189219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 4, 2].length) (baseStart_2189219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189219 prefixEnd_2189219 := by exact prefixLift 2189219
  have htrace : WordTrace (prefixWord ++ tailWord_2189219) baseStart_2189219 baseEnd_2189219 := by
    simpa [prefixWord, tailWord_2189219, baseEnd_2189219] using wordTrace_append hprefix tailTrace_2189219
  have hstable : (prefixWord ++ tailWord_2189219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189219).length < 2 ^ (prefixWord ++ tailWord_2189219).sum := by decide
  have hdescent : baseEnd_2189219 < baseStart_2189219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189223 : List Nat := [1, 1, 6, 1, 2, 1, 2, 3, 1, 3, 2]
def baseStart_2189223 : Nat := 118140960795 + 2189223 * 2 ^ 59
def prefixEnd_2189223 : Nat := 4983230072969 + 3 ^ 40 * 2189223 * 2
def baseEnd_2189223 : Nat := 1124123658877993388644453

theorem tailTrace_2189223 : CollatzResearch.WordTrace tailWord_2189223 prefixEnd_2189223 1124123658877993388644453 := by
  unfold tailWord_2189223
  simp only [CollatzResearch.WordTrace]
  refine ⟨79847522547826435366644323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53231681698550956911096215 79847522547826435366644323)
  ·
    refine ⟨119771283821739653049966485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79847522547826435366644323 119771283821739653049966485)
    ·
      refine ⟨5614278929144046236717179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 119771283821739653049966485 5614278929144046236717179)
      ·
        refine ⟨8421418393716069355075769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5614278929144046236717179 8421418393716069355075769)
        ·
          refine ⟨6316063795287052016306827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8421418393716069355075769 6316063795287052016306827)
          ·
            refine ⟨9474095692930578024460241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6316063795287052016306827 9474095692930578024460241)
            ·
              refine ⟨7105571769697933518345181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9474095692930578024460241 7105571769697933518345181)
              ·
                refine ⟨2664589413636725069379443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7105571769697933518345181 2664589413636725069379443)
                ·
                  refine ⟨3996884120455087604069165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2664589413636725069379443 3996884120455087604069165)
                  ·
                    refine ⟨1498831545170657851525937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3996884120455087604069165 1498831545170657851525937)
                    ·
                      refine ⟨1124123658877993388644453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1498831545170657851525937 1124123658877993388644453)
                      ·
                        rfl

theorem cell23_2189223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_2189223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189223 prefixEnd_2189223 := by exact prefixLift 2189223
  have htrace : WordTrace (prefixWord ++ tailWord_2189223) baseStart_2189223 baseEnd_2189223 := by
    simpa [prefixWord, tailWord_2189223, baseEnd_2189223] using wordTrace_append hprefix tailTrace_2189223
  have hstable : (prefixWord ++ tailWord_2189223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189223).length < 2 ^ (prefixWord ++ tailWord_2189223).sum := by decide
  have hdescent : baseEnd_2189223 < baseStart_2189223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189242 : List Nat := [3, 1, 1, 1, 2, 1, 2, 5, 7]
def baseStart_2189242 : Nat := 118140960795 + 2189242 * 2 ^ 59
def prefixEnd_2189242 : Nat := 4983230072969 + 3 ^ 40 * 2189242 * 2
def baseEnd_2189242 : Nat := 124903712778936534922985

theorem tailTrace_2189242 : CollatzResearch.WordTrace tailWord_2189242 prefixEnd_2189242 124903712778936534922985 := by
  unfold tailWord_2189242
  simp only [CollatzResearch.WordTrace]
  refine ⟨19962053883689400402896495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53232143689838401074390653 19962053883689400402896495)
  ·
    refine ⟨29943080825534100604344743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19962053883689400402896495 29943080825534100604344743)
    ·
      refine ⟨44914621238301150906517115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29943080825534100604344743 44914621238301150906517115)
      ·
        refine ⟨67371931857451726359775673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44914621238301150906517115 67371931857451726359775673)
        ·
          refine ⟨50528948893088794769831755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67371931857451726359775673 50528948893088794769831755)
          ·
            refine ⟨75793423339633192154747633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50528948893088794769831755 75793423339633192154747633)
            ·
              refine ⟨56845067504724894116060725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75793423339633192154747633 56845067504724894116060725)
              ·
                refine ⟨5329225078567958823380693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56845067504724894116060725 5329225078567958823380693)
                ·
                  refine ⟨124903712778936534922985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5329225078567958823380693 124903712778936534922985)
                  ·
                    rfl

theorem cell23_2189242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 7].length) (baseStart_2189242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189242 prefixEnd_2189242 := by exact prefixLift 2189242
  have htrace : WordTrace (prefixWord ++ tailWord_2189242) baseStart_2189242 baseEnd_2189242 := by
    simpa [prefixWord, tailWord_2189242, baseEnd_2189242] using wordTrace_append hprefix tailTrace_2189242
  have hstable : (prefixWord ++ tailWord_2189242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189242).length < 2 ^ (prefixWord ++ tailWord_2189242).sum := by decide
  have hdescent : baseEnd_2189242 < baseStart_2189242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189270 : List Nat := [5, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2]
def baseStart_2189270 : Nat := 118140960795 + 2189270 * 2 ^ 59
def prefixEnd_2189270 : Nat := 4983230072969 + 3 ^ 40 * 2189270 * 2
def baseEnd_2189270 : Nat := 1124147792468754704756737

theorem tailTrace_2189270 : CollatzResearch.WordTrace tailWord_2189270 prefixEnd_2189270 1124147792468754704756737 := by
  unfold tailWord_2189270
  simp only [CollatzResearch.WordTrace]
  refine ⟨4990577298666010149600329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53232824519104108262403509 4990577298666010149600329)
  ·
    refine ⟨3742932973999507612200247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4990577298666010149600329 3742932973999507612200247)
    ·
      refine ⟨5614399460999261418300371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3742932973999507612200247 5614399460999261418300371)
      ·
        refine ⟨8421599191498892127450557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5614399460999261418300371 8421599191498892127450557)
        ·
          refine ⟨3158099696812084547793959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8421599191498892127450557 3158099696812084547793959)
          ·
            refine ⟨4737149545218126821690939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3158099696812084547793959 4737149545218126821690939)
            ·
              refine ⟨7105724317827190232536409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4737149545218126821690939 7105724317827190232536409)
              ·
                refine ⟨5329293238370392674402307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7105724317827190232536409 5329293238370392674402307)
                ·
                  refine ⟨7993939857555589011603461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5329293238370392674402307 7993939857555589011603461)
                  ·
                    refine ⟨1498863723291672939675649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7993939857555589011603461 1498863723291672939675649)
                    ·
                      refine ⟨1124147792468754704756737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1498863723291672939675649 1124147792468754704756737)
                      ·
                        rfl

theorem cell23_2189270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_2189270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189270 prefixEnd_2189270 := by exact prefixLift 2189270
  have htrace : WordTrace (prefixWord ++ tailWord_2189270) baseStart_2189270 baseEnd_2189270 := by
    simpa [prefixWord, tailWord_2189270, baseEnd_2189270] using wordTrace_append hprefix tailTrace_2189270
  have hstable : (prefixWord ++ tailWord_2189270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189270).length < 2 ^ (prefixWord ++ tailWord_2189270).sum := by decide
  have hdescent : baseEnd_2189270 < baseStart_2189270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189309 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 4, 1, 4]
def baseStart_2189309 : Nat := 118140960795 + 2189309 * 2 ^ 59
def prefixEnd_2189309 : Nat := 4983230072969 + 3 ^ 40 * 2189309 * 2
def baseEnd_2189309 : Nat := 1124167818214280052169057

theorem tailTrace_2189309 : CollatzResearch.WordTrace tailWord_2189309 prefixEnd_2189309 1124167818214280052169057 := by
  unfold tailWord_2189309
  simp only [CollatzResearch.WordTrace]
  refine ⟨79850659225514872054274981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53233772817009914702849987 79850659225514872054274981)
  ·
    refine ⟨14971998604784038510176559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79850659225514872054274981 14971998604784038510176559)
    ·
      refine ⟨22457997907176057765264839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14971998604784038510176559 22457997907176057765264839)
      ·
        refine ⟨33686996860764086647897259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22457997907176057765264839 33686996860764086647897259)
        ·
          refine ⟨50530495291146129971845889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33686996860764086647897259 50530495291146129971845889)
          ·
            refine ⟨37897871468359597478884417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50530495291146129971845889 37897871468359597478884417)
            ·
              refine ⟨28423403601269698109163313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37897871468359597478884417 28423403601269698109163313)
              ·
                refine ⟨21317552700952273581872485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28423403601269698109163313 21317552700952273581872485)
                ·
                  refine ⟨3997041131428551296601091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21317552700952273581872485 3997041131428551296601091)
                  ·
                    refine ⟨5995561697142826944901637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3997041131428551296601091 5995561697142826944901637)
                    ·
                      refine ⟨1124167818214280052169057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5995561697142826944901637 1124167818214280052169057)
                      ·
                        rfl

theorem cell23_2189309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_2189309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189309 prefixEnd_2189309 := by exact prefixLift 2189309
  have htrace : WordTrace (prefixWord ++ tailWord_2189309) baseStart_2189309 baseEnd_2189309 := by
    simpa [prefixWord, tailWord_2189309, baseEnd_2189309] using wordTrace_append hprefix tailTrace_2189309
  have hstable : (prefixWord ++ tailWord_2189309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189309).length < 2 ^ (prefixWord ++ tailWord_2189309).sum := by decide
  have hdescent : baseEnd_2189309 < baseStart_2189309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189326 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2]
def baseStart_2189326 : Nat := 118140960795 + 2189326 * 2 ^ 59
def prefixEnd_2189326 : Nat := 4983230072969 + 3 ^ 40 * 2189326 * 2
def baseEnd_2189326 : Nat := 1124176547385406485656479

theorem tailTrace_2189326 : CollatzResearch.WordTrace tailWord_2189326 prefixEnd_2189326 1124176547385406485656479 := by
  unfold tailWord_2189326
  simp only [CollatzResearch.WordTrace]
  refine ⟨9981409908306660494705479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53234186177635522638429221 9981409908306660494705479)
  ·
    refine ⟨14972114862459990742058219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9981409908306660494705479 14972114862459990742058219)
    ·
      refine ⟨22458172293689986113087329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14972114862459990742058219 22458172293689986113087329)
      ·
        refine ⟨16843629220267489584815497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22458172293689986113087329 16843629220267489584815497)
        ·
          refine ⟨12632721915200617188611623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16843629220267489584815497 12632721915200617188611623)
          ·
            refine ⟨18949082872800925782917435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12632721915200617188611623 18949082872800925782917435)
            ·
              refine ⟨28423624309201388674376153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18949082872800925782917435 28423624309201388674376153)
              ·
                refine ⟨21317718231901041505782115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28423624309201388674376153 21317718231901041505782115)
                ·
                  refine ⟨31976577347851562258673173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21317718231901041505782115 31976577347851562258673173)
                  ·
                    refine ⟨1498902063180541980875305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31976577347851562258673173 1498902063180541980875305)
                    ·
                      refine ⟨1124176547385406485656479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1498902063180541980875305 1124176547385406485656479)
                      ·
                        rfl

theorem cell23_2189326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_2189326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189326 prefixEnd_2189326 := by exact prefixLift 2189326
  have htrace : WordTrace (prefixWord ++ tailWord_2189326) baseStart_2189326 baseEnd_2189326 := by
    simpa [prefixWord, tailWord_2189326, baseEnd_2189326] using wordTrace_append hprefix tailTrace_2189326
  have hstable : (prefixWord ++ tailWord_2189326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189326).length < 2 ^ (prefixWord ++ tailWord_2189326).sum := by decide
  have hdescent : baseEnd_2189326 < baseStart_2189326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189346 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 4, 2, 3]
def baseStart_2189346 : Nat := 118140960795 + 2189346 * 2 ^ 59
def prefixEnd_2189346 : Nat := 4983230072969 + 3 ^ 40 * 2189346 * 2
def baseEnd_2189346 : Nat := 1124186816998496407406387

theorem tailTrace_2189346 : CollatzResearch.WordTrace tailWord_2189346 prefixEnd_2189346 1124186816998496407406387 := by
  unfold tailWord_2189346
  simp only [CollatzResearch.WordTrace]
  refine ⟨19963002181595206843342973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53234672484253884915581261 19963002181595206843342973)
  ·
    refine ⟨7486125818098202566253615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19963002181595206843342973 7486125818098202566253615)
    ·
      refine ⟨11229188727147303849380423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7486125818098202566253615 11229188727147303849380423)
      ·
        refine ⟨16843783090720955774070635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11229188727147303849380423 16843783090720955774070635)
        ·
          refine ⟨25265674636081433661105953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16843783090720955774070635 25265674636081433661105953)
          ·
            refine ⟨18949255977061075245829465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25265674636081433661105953 18949255977061075245829465)
            ·
              refine ⟨14211941982795806434372099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18949255977061075245829465 14211941982795806434372099)
              ·
                refine ⟨21317912974193709651558149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14211941982795806434372099 21317912974193709651558149)
                ·
                  refine ⟨3997108682661320559667153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21317912974193709651558149 3997108682661320559667153)
                  ·
                    refine ⟨2997831511995990419750365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3997108682661320559667153 2997831511995990419750365)
                    ·
                      refine ⟨1124186816998496407406387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2997831511995990419750365 1124186816998496407406387)
                      ·
                        rfl

theorem cell23_2189346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_2189346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189346 prefixEnd_2189346 := by exact prefixLift 2189346
  have htrace : WordTrace (prefixWord ++ tailWord_2189346) baseStart_2189346 baseEnd_2189346 := by
    simpa [prefixWord, tailWord_2189346, baseEnd_2189346] using wordTrace_append hprefix tailTrace_2189346
  have hstable : (prefixWord ++ tailWord_2189346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189346).length < 2 ^ (prefixWord ++ tailWord_2189346).sum := by decide
  have hdescent : baseEnd_2189346 < baseStart_2189346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189349 : List Nat := [1, 3, 1, 2, 2, 4, 1, 1, 8]
def baseStart_2189349 : Nat := 118140960795 + 2189349 * 2 ^ 59
def prefixEnd_2189349 : Nat := 4983230072969 + 3 ^ 40 * 2189349 * 2
def baseEnd_2189349 : Nat := 124909817493384432852097

theorem tailTrace_2189349 : CollatzResearch.WordTrace tailWord_2189349 prefixEnd_2189349 124909817493384432852097 := by
  unfold tailWord_2189349
  simp only [CollatzResearch.WordTrace]
  refine ⟨79852118145369958885731101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53234745430246639257154067 79852118145369958885731101)
  ·
    refine ⟨29944544304513734582149163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79852118145369958885731101 29944544304513734582149163)
    ·
      refine ⟨44916816456770601873223745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29944544304513734582149163 44916816456770601873223745)
      ·
        refine ⟨33687612342577951404917809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44916816456770601873223745 33687612342577951404917809)
        ·
          refine ⟨25265709256933463553688357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33687612342577951404917809 25265709256933463553688357)
          ·
            refine ⟨4737320485675024416316567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25265709256933463553688357 4737320485675024416316567)
            ·
              refine ⟨7105980728512536624474851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4737320485675024416316567 7105980728512536624474851)
              ·
                refine ⟨10658971092768804936712277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7105980728512536624474851 10658971092768804936712277)
                ·
                  refine ⟨124909817493384432852097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10658971092768804936712277 124909817493384432852097)
                  ·
                    rfl

theorem cell23_2189349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 8].length) (baseStart_2189349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189349 prefixEnd_2189349 := by exact prefixLift 2189349
  have htrace : WordTrace (prefixWord ++ tailWord_2189349) baseStart_2189349 baseEnd_2189349 := by
    simpa [prefixWord, tailWord_2189349, baseEnd_2189349] using wordTrace_append hprefix tailTrace_2189349
  have hstable : (prefixWord ++ tailWord_2189349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189349).length < 2 ^ (prefixWord ++ tailWord_2189349).sum := by decide
  have hdescent : baseEnd_2189349 < baseStart_2189349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189430 : List Nat := [5, 1, 1, 2, 1, 4, 1, 2, 1, 5]
def baseStart_2189430 : Nat := 118140960795 + 2189430 * 2 ^ 59
def prefixEnd_2189430 : Nat := 4983230072969 + 3 ^ 40 * 2189430 * 2
def baseEnd_2189430 : Nat := 374743316457824692918667

theorem tailTrace_2189430 : CollatzResearch.WordTrace tailWord_2189430 prefixEnd_2189430 374743316457824692918667 := by
  unfold tailWord_2189430
  simp only [CollatzResearch.WordTrace]
  refine ⟨4990942028629781857464359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53236714972051006479619829 4990942028629781857464359)
  ·
    refine ⟨7486413042944672786196539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4990942028629781857464359 7486413042944672786196539)
    ·
      refine ⟨11229619564417009179294809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7486413042944672786196539 11229619564417009179294809)
      ·
        refine ⟨8422214673312756884471107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11229619564417009179294809 8422214673312756884471107)
        ·
          refine ⟨12633322009969135326706661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8422214673312756884471107 12633322009969135326706661)
          ·
            refine ⟨2368747876869212873757499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12633322009969135326706661 2368747876869212873757499)
            ·
              refine ⟨3553121815303819310636249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2368747876869212873757499 3553121815303819310636249)
              ·
                refine ⟨2664841361477864482977187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3553121815303819310636249 2664841361477864482977187)
                ·
                  refine ⟨3997262042216796724465781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2664841361477864482977187 3997262042216796724465781)
                  ·
                    refine ⟨374743316457824692918667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3997262042216796724465781 374743316457824692918667)
                    ·
                      rfl

theorem cell23_2189430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_2189430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189430 prefixEnd_2189430 := by exact prefixLift 2189430
  have htrace : WordTrace (prefixWord ++ tailWord_2189430) baseStart_2189430 baseEnd_2189430 := by
    simpa [prefixWord, tailWord_2189430, baseEnd_2189430] using wordTrace_append hprefix tailTrace_2189430
  have hstable : (prefixWord ++ tailWord_2189430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189430).length < 2 ^ (prefixWord ++ tailWord_2189430).sum := by decide
  have hdescent : baseEnd_2189430 < baseStart_2189430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189433 : List Nat := [1, 2, 1, 3, 4, 1, 3, 2, 1, 1, 4]
def baseStart_2189433 : Nat := 118140960795 + 2189433 * 2 ^ 59
def prefixEnd_2189433 : Nat := 4983230072969 + 3 ^ 40 * 2189433 * 2
def baseEnd_2189433 : Nat := 1124231489815437567018487

theorem tailTrace_2189433 : CollatzResearch.WordTrace tailWord_2189433 prefixEnd_2189433 1124231489815437567018487 := by
  unfold tailWord_2189433
  simp only [CollatzResearch.WordTrace]
  refine ⟨79855181877065641231788953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53236787918043760821192635 79855181877065641231788953)
  ·
    refine ⟨59891386407799230923841715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79855181877065641231788953 59891386407799230923841715)
    ·
      refine ⟨89837079611698846385762573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59891386407799230923841715 89837079611698846385762573)
      ·
        refine ⟨33688904854387067394660965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89837079611698846385762573 33688904854387067394660965)
        ·
          refine ⟨6316669660197575136498931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33688904854387067394660965 6316669660197575136498931)
          ·
            refine ⟨9475004490296362704748397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6316669660197575136498931 9475004490296362704748397)
            ·
              refine ⟨3553126683861136014280649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9475004490296362704748397 3553126683861136014280649)
              ·
                refine ⟨2664845012895852010710487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3553126683861136014280649 2664845012895852010710487)
                ·
                  refine ⟨3997267519343778016065731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2664845012895852010710487 3997267519343778016065731)
                  ·
                    refine ⟨5995901279015667024098597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3997267519343778016065731 5995901279015667024098597)
                    ·
                      refine ⟨1124231489815437567018487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5995901279015667024098597 1124231489815437567018487)
                      ·
                        rfl

theorem cell23_2189433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_2189433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189433 prefixEnd_2189433 := by exact prefixLift 2189433
  have htrace : WordTrace (prefixWord ++ tailWord_2189433) baseStart_2189433 baseEnd_2189433 := by
    simpa [prefixWord, tailWord_2189433, baseEnd_2189433] using wordTrace_append hprefix tailTrace_2189433
  have hstable : (prefixWord ++ tailWord_2189433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189433).length < 2 ^ (prefixWord ++ tailWord_2189433).sum := by decide
  have hdescent : baseEnd_2189433 < baseStart_2189433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189450 : List Nat := [3, 1, 2, 3, 1, 3, 3, 1, 1, 1, 4]
def baseStart_2189450 : Nat := 118140960795 + 2189450 * 2 ^ 59
def prefixEnd_2189450 : Nat := 4983230072969 + 3 ^ 40 * 2189450 * 2
def baseEnd_2189450 : Nat := 1124240218986564000505909

theorem tailTrace_2189450 : CollatzResearch.WordTrace tailWord_2189450 prefixEnd_2189450 1124240218986564000505909 := by
  unfold tailWord_2189450
  simp only [CollatzResearch.WordTrace]
  refine ⟨19963950479501013283789451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53237201278669368756771869 19963950479501013283789451)
  ·
    refine ⟨29945925719251519925684177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19963950479501013283789451 29945925719251519925684177)
    ·
      refine ⟨22459444289438639944263133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29945925719251519925684177 22459444289438639944263133)
      ·
        refine ⟨8422291608539489979098675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22459444289438639944263133 8422291608539489979098675)
        ·
          refine ⟨12633437412809234968648013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8422291608539489979098675 12633437412809234968648013)
          ·
            refine ⟨4737539029803463113243005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12633437412809234968648013 4737539029803463113243005)
            ·
              refine ⟨1776577136176298667466127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4737539029803463113243005 1776577136176298667466127)
              ·
                refine ⟨2664865704264448001199191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1776577136176298667466127 2664865704264448001199191)
                ·
                  refine ⟨3997298556396672001798787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2664865704264448001199191 3997298556396672001798787)
                  ·
                    refine ⟨5995947834595008002698181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3997298556396672001798787 5995947834595008002698181)
                    ·
                      refine ⟨1124240218986564000505909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5995947834595008002698181 1124240218986564000505909)
                      ·
                        rfl

theorem cell23_2189450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_2189450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189450 prefixEnd_2189450 := by exact prefixLift 2189450
  have htrace : WordTrace (prefixWord ++ tailWord_2189450) baseStart_2189450 baseEnd_2189450 := by
    simpa [prefixWord, tailWord_2189450, baseEnd_2189450] using wordTrace_append hprefix tailTrace_2189450
  have hstable : (prefixWord ++ tailWord_2189450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189450).length < 2 ^ (prefixWord ++ tailWord_2189450).sum := by decide
  have hdescent : baseEnd_2189450 < baseStart_2189450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189499 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 1, 8]
def baseStart_2189499 : Nat := 118140960795 + 2189499 * 2 ^ 59
def prefixEnd_2189499 : Nat := 4983230072969 + 3 ^ 40 * 2189499 * 2
def baseEnd_2189499 : Nat := 374755126512878102931061

theorem tailTrace_2189499 : CollatzResearch.WordTrace tailWord_2189499 prefixEnd_2189499 374755126512878102931061 := by
  unfold tailWord_2189499
  simp only [CollatzResearch.WordTrace]
  refine ⟨79857589094826534503691551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53238392729884356335794367 79857589094826534503691551)
  ·
    refine ⟨119786383642239801755537327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79857589094826534503691551 119786383642239801755537327)
    ·
      refine ⟨179679575463359702633305991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119786383642239801755537327 179679575463359702633305991)
      ·
        refine ⟨269519363195039553949958987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179679575463359702633305991 269519363195039553949958987)
        ·
          refine ⟨404279044792559330924938481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269519363195039553949958987 404279044792559330924938481)
          ·
            refine ⟨303209283594419498193703861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 404279044792559330924938481 303209283594419498193703861)
            ·
              refine ⟨28425870336976827955659737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 303209283594419498193703861 28425870336976827955659737)
              ·
                refine ⟨21319402752732620966744803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28425870336976827955659737 21319402752732620966744803)
                ·
                  refine ⟨31979104129098931450117205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21319402752732620966744803 31979104129098931450117205)
                  ·
                    refine ⟨374755126512878102931061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31979104129098931450117205 374755126512878102931061)
                    ·
                      rfl

theorem cell23_2189499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 8].length) (baseStart_2189499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189499 prefixEnd_2189499 := by exact prefixLift 2189499
  have htrace : WordTrace (prefixWord ++ tailWord_2189499) baseStart_2189499 baseEnd_2189499 := by
    simpa [prefixWord, tailWord_2189499, baseEnd_2189499] using wordTrace_append hprefix tailTrace_2189499
  have hstable : (prefixWord ++ tailWord_2189499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189499).length < 2 ^ (prefixWord ++ tailWord_2189499).sum := by decide
  have hdescent : baseEnd_2189499 < baseStart_2189499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189533 : List Nat := [1, 4, 3, 2, 1, 1, 2, 1, 2, 6]
def baseStart_2189533 : Nat := 118140960795 + 2189533 * 2 ^ 59
def prefixEnd_2189533 : Nat := 4983230072969 + 3 ^ 40 * 2189533 * 2
def baseEnd_2189533 : Nat := 374760945960295725256009

theorem tailTrace_2189533 : CollatzResearch.WordTrace tailWord_2189533 prefixEnd_2189533 374760945960295725256009 := by
  unfold tailWord_2189533
  simp only [CollatzResearch.WordTrace]
  refine ⟨79858829176703358310429253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53239219451135572206952835 79858829176703358310429253)
  ·
    refine ⟨14973530470631879683205485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79858829176703358310429253 14973530470631879683205485)
    ·
      refine ⟨5615073926486954881202057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14973530470631879683205485 5615073926486954881202057)
      ·
        refine ⟨4211305444865216160901543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5615073926486954881202057 4211305444865216160901543)
        ·
          refine ⟨6316958167297824241352315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4211305444865216160901543 6316958167297824241352315)
          ·
            refine ⟨9475437250946736362028473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6316958167297824241352315 9475437250946736362028473)
            ·
              refine ⟨7106577938210052271521355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9475437250946736362028473 7106577938210052271521355)
              ·
                refine ⟨10659866907315078407282033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7106577938210052271521355 10659866907315078407282033)
                ·
                  refine ⟨7994900180486308805461525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10659866907315078407282033 7994900180486308805461525)
                  ·
                    refine ⟨374760945960295725256009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7994900180486308805461525 374760945960295725256009)
                    ·
                      rfl

theorem cell23_2189533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_2189533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189533 prefixEnd_2189533 := by exact prefixLift 2189533
  have htrace : WordTrace (prefixWord ++ tailWord_2189533) baseStart_2189533 baseEnd_2189533 := by
    simpa [prefixWord, tailWord_2189533, baseEnd_2189533] using wordTrace_append hprefix tailTrace_2189533
  have hstable : (prefixWord ++ tailWord_2189533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189533).length < 2 ^ (prefixWord ++ tailWord_2189533).sum := by decide
  have hdescent : baseEnd_2189533 < baseStart_2189533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189536 : List Nat := [2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 4]
def baseStart_2189536 : Nat := 118140960795 + 2189536 * 2 ^ 59
def prefixEnd_2189536 : Nat := 4983230072969 + 3 ^ 40 * 2189536 * 2
def baseEnd_2189536 : Nat := 1124284378322850664030513

theorem tailTrace_2189536 : CollatzResearch.WordTrace tailWord_2189536 prefixEnd_2189536 1124284378322850664030513 := by
  unfold tailWord_2189536
  simp only [CollatzResearch.WordTrace]
  refine ⟨39929469297846244911394231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53239292397128326548525641 39929469297846244911394231)
  ·
    refine ⟨59894203946769367367091347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39929469297846244911394231 59894203946769367367091347)
    ·
      refine ⟨89841305920154051050637021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59894203946769367367091347 89841305920154051050637021)
      ·
        refine ⟨33690489720057769143988883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89841305920154051050637021 33690489720057769143988883)
        ·
          refine ⟨50535734580086653715983325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33690489720057769143988883 50535734580086653715983325)
          ·
            refine ⟨18950900467532495143493747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50535734580086653715983325 18950900467532495143493747)
            ·
              refine ⟨28426350701298742715240621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18950900467532495143493747 28426350701298742715240621)
              ·
                refine ⟨10659881512987028518215233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28426350701298742715240621 10659881512987028518215233)
                ·
                  refine ⟨7994911134740271388661425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10659881512987028518215233 7994911134740271388661425)
                  ·
                    refine ⟨5996183351055203541496069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7994911134740271388661425 5996183351055203541496069)
                    ·
                      refine ⟨1124284378322850664030513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5996183351055203541496069 1124284378322850664030513)
                      ·
                        rfl

theorem cell23_2189536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_2189536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189536 prefixEnd_2189536 := by exact prefixLift 2189536
  have htrace : WordTrace (prefixWord ++ tailWord_2189536) baseStart_2189536 baseEnd_2189536 := by
    simpa [prefixWord, tailWord_2189536, baseEnd_2189536] using wordTrace_append hprefix tailTrace_2189536
  have hstable : (prefixWord ++ tailWord_2189536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189536).length < 2 ^ (prefixWord ++ tailWord_2189536).sum := by decide
  have hdescent : baseEnd_2189536 < baseStart_2189536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189546 : List Nat := [3, 1, 3, 1, 1, 2, 1, 4, 7]
def baseStart_2189546 : Nat := 118140960795 + 2189546 * 2 ^ 59
def prefixEnd_2189546 : Nat := 4983230072969 + 3 ^ 40 * 2189546 * 2
def baseEnd_2189546 : Nat := 124921057014377291656163

theorem tailTrace_2189546 : CollatzResearch.WordTrace tailWord_2189546 prefixEnd_2189546 124921057014377291656163 := by
  unfold tailWord_2189546
  simp only [CollatzResearch.WordTrace]
  refine ⟨19964825831414065382663123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53239535550437507687101661 19964825831414065382663123)
  ·
    refine ⟨29947238747121098073994685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19964825831414065382663123 29947238747121098073994685)
    ·
      refine ⟨11230214530170411777748007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29947238747121098073994685 11230214530170411777748007)
      ·
        refine ⟨16845321795255617666622011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11230214530170411777748007 16845321795255617666622011)
        ·
          refine ⟨25267982692883426499933017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16845321795255617666622011 25267982692883426499933017)
          ·
            refine ⟨18950987019662569874949763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25267982692883426499933017 18950987019662569874949763)
            ·
              refine ⟨28426480529493854812424645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18950987019662569874949763 28426480529493854812424645)
              ·
                refine ⟨5329965099280097777329621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28426480529493854812424645 5329965099280097777329621)
                ·
                  refine ⟨124921057014377291656163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5329965099280097777329621 124921057014377291656163)
                  ·
                    rfl

theorem cell23_2189546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 7].length) (baseStart_2189546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189546 prefixEnd_2189546 := by exact prefixLift 2189546
  have htrace : WordTrace (prefixWord ++ tailWord_2189546) baseStart_2189546 baseEnd_2189546 := by
    simpa [prefixWord, tailWord_2189546, baseEnd_2189546] using wordTrace_append hprefix tailTrace_2189546
  have hstable : (prefixWord ++ tailWord_2189546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189546).length < 2 ^ (prefixWord ++ tailWord_2189546).sum := by decide
  have hdescent : baseEnd_2189546 < baseStart_2189546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189580 : List Nat := [2, 2, 1, 2, 2, 2, 5, 2, 5]
def baseStart_2189580 : Nat := 118140960795 + 2189580 * 2 ^ 59
def prefixEnd_2189580 : Nat := 4983230072969 + 3 ^ 40 * 2189580 * 2
def baseEnd_2189580 : Nat := 124922996830183165764479

theorem tailTrace_2189580 : CollatzResearch.WordTrace tailWord_2189580 prefixEnd_2189580 124922996830183165764479 := by
  unfold tailWord_2189580
  simp only [CollatzResearch.WordTrace]
  refine ⟨39930271703766542668695097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53240362271688723558260129 39930271703766542668695097)
  ·
    refine ⟨29947703777824907001521323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39930271703766542668695097 29947703777824907001521323)
    ·
      refine ⟨44921555666737360502281985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29947703777824907001521323 44921555666737360502281985)
      ·
        refine ⟨33691166750053020376711489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44921555666737360502281985 33691166750053020376711489)
        ·
          refine ⟨25268375062539765282533617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33691166750053020376711489 25268375062539765282533617)
          ·
            refine ⟨18951281296904823961900213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25268375062539765282533617 18951281296904823961900213)
            ·
              refine ⟨1776682621584827246428145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18951281296904823961900213 1776682621584827246428145)
              ·
                refine ⟨1332511966188620434821109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1776682621584827246428145 1332511966188620434821109)
                ·
                  refine ⟨124922996830183165764479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1332511966188620434821109 124922996830183165764479)
                  ·
                    rfl

theorem cell23_2189580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2, 5].length) (baseStart_2189580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189580 prefixEnd_2189580 := by exact prefixLift 2189580
  have htrace : WordTrace (prefixWord ++ tailWord_2189580) baseStart_2189580 baseEnd_2189580 := by
    simpa [prefixWord, tailWord_2189580, baseEnd_2189580] using wordTrace_append hprefix tailTrace_2189580
  have hstable : (prefixWord ++ tailWord_2189580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189580).length < 2 ^ (prefixWord ++ tailWord_2189580).sum := by decide
  have hdescent : baseEnd_2189580 < baseStart_2189580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189630 : List Nat := [4, 2, 1, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_2189630 : Nat := 118140960795 + 2189630 * 2 ^ 59
def prefixEnd_2189630 : Nat := 4983230072969 + 3 ^ 40 * 2189630 * 2
def baseEnd_2189630 : Nat := 1124332645504373296255081

theorem tailTrace_2189630 : CollatzResearch.WordTrace tailWord_2189630 prefixEnd_2189630 1124332645504373296255081 := by
  unfold tailWord_2189630
  simp only [CollatzResearch.WordTrace]
  refine ⟨9982795882168992984588793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53241578038234629251140229 9982795882168992984588793)
  ·
    refine ⟨7487096911626744738441595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9982795882168992984588793 7487096911626744738441595)
    ·
      refine ⟨11230645367440117107662393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7487096911626744738441595 11230645367440117107662393)
      ·
        refine ⟨8422984025580087830746795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11230645367440117107662393 8422984025580087830746795)
        ·
          refine ⟨12634476038370131746120193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8422984025580087830746795 12634476038370131746120193)
          ·
            refine ⟨9475857028777598809590145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12634476038370131746120193 9475857028777598809590145)
            ·
              refine ⟨7106892771583199107192609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9475857028777598809590145 7106892771583199107192609)
              ·
                refine ⟨5330169578687399330394457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7106892771583199107192609 5330169578687399330394457)
                ·
                  refine ⟨3997627184015549497795843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5330169578687399330394457 3997627184015549497795843)
                  ·
                    refine ⟨5996440776023324246693765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3997627184015549497795843 5996440776023324246693765)
                    ·
                      refine ⟨1124332645504373296255081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5996440776023324246693765 1124332645504373296255081)
                      ·
                        rfl

theorem cell23_2189630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_2189630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189630 prefixEnd_2189630 := by exact prefixLift 2189630
  have htrace : WordTrace (prefixWord ++ tailWord_2189630) baseStart_2189630 baseEnd_2189630 := by
    simpa [prefixWord, tailWord_2189630, baseEnd_2189630] using wordTrace_append hprefix tailTrace_2189630
  have hstable : (prefixWord ++ tailWord_2189630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189630).length < 2 ^ (prefixWord ++ tailWord_2189630).sum := by decide
  have hdescent : baseEnd_2189630 < baseStart_2189630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189656 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 3, 2, 6]
def baseStart_2189656 : Nat := 118140960795 + 2189656 * 2 ^ 59
def prefixEnd_2189656 : Nat := 4983230072969 + 3 ^ 40 * 2189656 * 2
def baseEnd_2189656 : Nat := 1124345996001390194529961

theorem tailTrace_2189656 : CollatzResearch.WordTrace tailWord_2189656 prefixEnd_2189656 1124345996001390194529961 := by
  unfold tailWord_2189656
  simp only [CollatzResearch.WordTrace]
  refine ⟨39931657677628875158578411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53242210236838500211437881 39931657677628875158578411)
  ·
    refine ⟨59897486516443312737867617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39931657677628875158578411 59897486516443312737867617)
    ·
      refine ⟨44923114887332484553400713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59897486516443312737867617 44923114887332484553400713)
      ·
        refine ⟨33692336165499363415050535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44923114887332484553400713 33692336165499363415050535)
        ·
          refine ⟨50538504248249045122575803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33692336165499363415050535 50538504248249045122575803)
          ·
            refine ⟨75807756372373567683863705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50538504248249045122575803 75807756372373567683863705)
            ·
              refine ⟨56855817279280175762897779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75807756372373567683863705 56855817279280175762897779)
              ·
                refine ⟨85283725918920263644346669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56855817279280175762897779 85283725918920263644346669)
                ·
                  refine ⟨31981397219595098866630001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85283725918920263644346669 31981397219595098866630001)
                  ·
                    refine ⟨23986047914696324149972501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31981397219595098866630001 23986047914696324149972501)
                    ·
                      refine ⟨1124345996001390194529961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23986047914696324149972501 1124345996001390194529961)
                      ·
                        rfl

theorem cell23_2189656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_2189656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189656 prefixEnd_2189656 := by exact prefixLift 2189656
  have htrace : WordTrace (prefixWord ++ tailWord_2189656) baseStart_2189656 baseEnd_2189656 := by
    simpa [prefixWord, tailWord_2189656, baseEnd_2189656] using wordTrace_append hprefix tailTrace_2189656
  have hstable : (prefixWord ++ tailWord_2189656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189656).length < 2 ^ (prefixWord ++ tailWord_2189656).sum := by decide
  have hdescent : baseEnd_2189656 < baseStart_2189656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189674 : List Nat := [3, 1, 3, 3, 1, 2, 2, 3, 1, 4]
def baseStart_2189674 : Nat := 118140960795 + 2189674 * 2 ^ 59
def prefixEnd_2189674 : Nat := 4983230072969 + 3 ^ 40 * 2189674 * 2
def baseEnd_2189674 : Nat := 374785079551057041368293

theorem tailTrace_2189674 : CollatzResearch.WordTrace tailWord_2189674 prefixEnd_2189674 374785079551057041368293 := by
  unfold tailWord_2189674
  simp only [CollatzResearch.WordTrace]
  refine ⟨19965992967298134847828019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53242647912795026260874717 19965992967298134847828019)
  ·
    refine ⟨29948989450947202271742029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19965992967298134847828019 29948989450947202271742029)
    ·
      refine ⟨11230871044105200851903261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29948989450947202271742029 11230871044105200851903261)
      ·
        refine ⟨4211576641539450319463723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11230871044105200851903261 4211576641539450319463723)
        ·
          refine ⟨6317364962309175479195585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4211576641539450319463723 6317364962309175479195585)
          ·
            refine ⟨4738023721731881609396689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6317364962309175479195585 4738023721731881609396689)
            ·
              refine ⟨3553517791298911207047517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4738023721731881609396689 3553517791298911207047517)
              ·
                refine ⟨1332569171737091702642819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3553517791298911207047517 1332569171737091702642819)
                ·
                  refine ⟨1998853757605637553964229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1332569171737091702642819 1998853757605637553964229)
                  ·
                    refine ⟨374785079551057041368293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1998853757605637553964229 374785079551057041368293)
                    ·
                      rfl

theorem cell23_2189674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_2189674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189674 prefixEnd_2189674 := by exact prefixLift 2189674
  have htrace : WordTrace (prefixWord ++ tailWord_2189674) baseStart_2189674 baseEnd_2189674 := by
    simpa [prefixWord, tailWord_2189674, baseEnd_2189674] using wordTrace_append hprefix tailTrace_2189674
  have hstable : (prefixWord ++ tailWord_2189674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189674).length < 2 ^ (prefixWord ++ tailWord_2189674).sum := by decide
  have hdescent : baseEnd_2189674 < baseStart_2189674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189683 : List Nat := [1, 1, 1, 2, 2, 1, 2, 7, 1, 5]
def baseStart_2189683 : Nat := 118140960795 + 2189683 * 2 ^ 59
def prefixEnd_2189683 : Nat := 4983230072969 + 3 ^ 40 * 2189683 * 2
def baseEnd_2189683 : Nat := 374786619993020529630779

theorem tailTrace_2189683 : CollatzResearch.WordTrace tailWord_2189683 prefixEnd_2189683 374786619993020529630779 := by
  unfold tailWord_2189683
  simp only [CollatzResearch.WordTrace]
  refine ⟨79864300126159933928389703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53242866750773289285593135 79864300126159933928389703)
  ·
    refine ⟨119796450189239900892584555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79864300126159933928389703 119796450189239900892584555)
    ·
      refine ⟨179694675283859851338876833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119796450189239900892584555 179694675283859851338876833)
      ·
        refine ⟨134771006462894888504157625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179694675283859851338876833 134771006462894888504157625)
        ·
          refine ⟨101078254847171166378118219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134771006462894888504157625 101078254847171166378118219)
          ·
            refine ⟨151617382270756749567177329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101078254847171166378118219 151617382270756749567177329)
            ·
              refine ⟨113713036703067562175382997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151617382270756749567177329 113713036703067562175382997)
              ·
                refine ⟨2665149297728145988485539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 113713036703067562175382997 2665149297728145988485539)
                ·
                  refine ⟨3997723946592218982728309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2665149297728145988485539 3997723946592218982728309)
                  ·
                    refine ⟨374786619993020529630779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3997723946592218982728309 374786619993020529630779)
                    ·
                      rfl

theorem cell23_2189683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 5].length) (baseStart_2189683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189683 prefixEnd_2189683 := by exact prefixLift 2189683
  have htrace : WordTrace (prefixWord ++ tailWord_2189683) baseStart_2189683 baseEnd_2189683 := by
    simpa [prefixWord, tailWord_2189683, baseEnd_2189683] using wordTrace_append hprefix tailTrace_2189683
  have hstable : (prefixWord ++ tailWord_2189683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189683).length < 2 ^ (prefixWord ++ tailWord_2189683).sum := by decide
  have hdescent : baseEnd_2189683 < baseStart_2189683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189696 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 2, 10]
def baseStart_2189696 : Nat := 118140960795 + 2189696 * 2 ^ 59
def prefixEnd_2189696 : Nat := 4983230072969 + 3 ^ 40 * 2189696 * 2
def baseEnd_2189696 : Nat := 374788845075856679343259

theorem tailTrace_2189696 : CollatzResearch.WordTrace tailWord_2189696 prefixEnd_2189696 374788845075856679343259 := by
  unfold tailWord_2189696
  simp only [CollatzResearch.WordTrace]
  refine ⟨39932387137556418574306471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53243182850075224765741961 39932387137556418574306471)
  ·
    refine ⟨59898580706334627861459707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39932387137556418574306471 59898580706334627861459707)
    ·
      refine ⟨89847871059501941792189561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59898580706334627861459707 89847871059501941792189561)
      ·
        refine ⟨67385903294626456344142171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89847871059501941792189561 67385903294626456344142171)
        ·
          refine ⟨101078854941939684516213257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67385903294626456344142171 101078854941939684516213257)
          ·
            refine ⟨75809141206454763387159943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101078854941939684516213257 75809141206454763387159943)
            ·
              refine ⟨113713711809682145080739915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75809141206454763387159943 113713711809682145080739915)
              ·
                refine ⟨170570567714523217621109873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113713711809682145080739915 170570567714523217621109873)
                ·
                  refine ⟨127927925785892413215832405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170570567714523217621109873 127927925785892413215832405)
                  ·
                    refine ⟨374788845075856679343259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 127927925785892413215832405 374788845075856679343259)
                    ·
                      rfl

theorem cell23_2189696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 10].length) (baseStart_2189696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189696 prefixEnd_2189696 := by exact prefixLift 2189696
  have htrace : WordTrace (prefixWord ++ tailWord_2189696) baseStart_2189696 baseEnd_2189696 := by
    simpa [prefixWord, tailWord_2189696, baseEnd_2189696] using wordTrace_append hprefix tailTrace_2189696
  have hstable : (prefixWord ++ tailWord_2189696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189696).length < 2 ^ (prefixWord ++ tailWord_2189696).sum := by decide
  have hdescent : baseEnd_2189696 < baseStart_2189696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189697 : List Nat := [1, 2, 4, 3, 1, 1, 1, 3, 3, 1, 3]
def baseStart_2189697 : Nat := 118140960795 + 2189697 * 2 ^ 59
def prefixEnd_2189697 : Nat := 4983230072969 + 3 ^ 40 * 2189697 * 2
def baseEnd_2189697 : Nat := 1124367048708224534117273

theorem tailTrace_2189697 : CollatzResearch.WordTrace tailWord_2189697 prefixEnd_2189697 1124367048708224534117273 := by
  unfold tailWord_2189697
  simp only [CollatzResearch.WordTrace]
  refine ⟨79864810748109214319399345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53243207165406142879599563 79864810748109214319399345)
  ·
    refine ⟨59898608061081910739549509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79864810748109214319399345 59898608061081910739549509)
    ·
      refine ⟨11230989011452858263665533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59898608061081910739549509 11230989011452858263665533)
      ·
        refine ⟨4211620879294821848874575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11230989011452858263665533 4211620879294821848874575)
        ·
          refine ⟨6317431318942232773311863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4211620879294821848874575 6317431318942232773311863)
          ·
            refine ⟨9476146978413349159967795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6317431318942232773311863 9476146978413349159967795)
            ·
              refine ⟨14214220467620023739951693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9476146978413349159967795 14214220467620023739951693)
              ·
                refine ⟨5330332675357508902481885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14214220467620023739951693 5330332675357508902481885)
                ·
                  refine ⟨1998874753259065838430707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5330332675357508902481885 1998874753259065838430707)
                  ·
                    refine ⟨2998312129888598757646061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1998874753259065838430707 2998312129888598757646061)
                    ·
                      refine ⟨1124367048708224534117273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2998312129888598757646061 1124367048708224534117273)
                      ·
                        rfl

theorem cell23_2189697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_2189697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189697 prefixEnd_2189697 := by exact prefixLift 2189697
  have htrace : WordTrace (prefixWord ++ tailWord_2189697) baseStart_2189697 baseEnd_2189697 := by
    simpa [prefixWord, tailWord_2189697, baseEnd_2189697] using wordTrace_append hprefix tailTrace_2189697
  have hstable : (prefixWord ++ tailWord_2189697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189697).length < 2 ^ (prefixWord ++ tailWord_2189697).sum := by decide
  have hdescent : baseEnd_2189697 < baseStart_2189697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189713 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 8, 4]
def baseStart_2189713 : Nat := 118140960795 + 2189713 * 2 ^ 59
def prefixEnd_2189713 : Nat := 4983230072969 + 3 ^ 40 * 2189713 * 2
def baseEnd_2189713 : Nat := 374791754799565490505733

theorem tailTrace_2189713 : CollatzResearch.WordTrace tailWord_2189713 prefixEnd_2189713 374791754799565490505733 := by
  unfold tailWord_2189713
  simp only [CollatzResearch.WordTrace]
  refine ⟨79865394316051249051981793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53243596210700832701321195 79865394316051249051981793)
  ·
    refine ⟨59899045737038436788986345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79865394316051249051981793 59899045737038436788986345)
    ·
      refine ⟨44924284302778827591739759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59899045737038436788986345 44924284302778827591739759)
      ·
        refine ⟨67386426454168241387609639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44924284302778827591739759 67386426454168241387609639)
        ·
          refine ⟨101079639681252362081414459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67386426454168241387609639 101079639681252362081414459)
          ·
            refine ⟨151619459521878543122121689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101079639681252362081414459 151619459521878543122121689)
            ·
              refine ⟨113714594641408907341591267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151619459521878543122121689 113714594641408907341591267)
              ·
                refine ⟨170571891962113361012386901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113714594641408907341591267 170571891962113361012386901)
                ·
                  refine ⟨1998889358931015949363909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 170571891962113361012386901 1998889358931015949363909)
                  ·
                    refine ⟨374791754799565490505733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1998889358931015949363909 374791754799565490505733)
                    ·
                      rfl

theorem cell23_2189713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8, 4].length) (baseStart_2189713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189713 prefixEnd_2189713 := by exact prefixLift 2189713
  have htrace : WordTrace (prefixWord ++ tailWord_2189713) baseStart_2189713 baseEnd_2189713 := by
    simpa [prefixWord, tailWord_2189713, baseEnd_2189713] using wordTrace_append hprefix tailTrace_2189713
  have hstable : (prefixWord ++ tailWord_2189713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189713).length < 2 ^ (prefixWord ++ tailWord_2189713).sum := by decide
  have hdescent : baseEnd_2189713 < baseStart_2189713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189730 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 6, 4]
def baseStart_2189730 : Nat := 118140960795 + 2189730 * 2 ^ 59
def prefixEnd_2189730 : Nat := 4983230072969 + 3 ^ 40 * 2189730 * 2
def baseEnd_2189730 : Nat := 374794664523274301668207

theorem tailTrace_2189730 : CollatzResearch.WordTrace tailWord_2189730 prefixEnd_2189730 374794664523274301668207 := by
  unfold tailWord_2189730
  simp only [CollatzResearch.WordTrace]
  refine ⟨19966503589247415238837661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53244009571326440636900429 19966503589247415238837661)
  ·
    refine ⟨7487438845967780714564123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19966503589247415238837661 7487438845967780714564123)
    ·
      refine ⟨11231158268951671071846185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7487438845967780714564123 11231158268951671071846185)
      ·
        refine ⟨8423368701713753303884639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11231158268951671071846185 8423368701713753303884639)
        ·
          refine ⟨12635053052570629955826959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8423368701713753303884639 12635053052570629955826959)
          ·
            refine ⟨18952579578855944933740439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12635053052570629955826959 18952579578855944933740439)
            ·
              refine ⟨28428869368283917400610659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18952579578855944933740439 28428869368283917400610659)
              ·
                refine ⟨42643304052425876100915989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28428869368283917400610659 42643304052425876100915989)
                ·
                  refine ⟨1998904877457462942230437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42643304052425876100915989 1998904877457462942230437)
                  ·
                    refine ⟨374794664523274301668207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1998904877457462942230437 374794664523274301668207)
                    ·
                      rfl

theorem cell23_2189730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_2189730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189730 prefixEnd_2189730 := by exact prefixLift 2189730
  have htrace : WordTrace (prefixWord ++ tailWord_2189730) baseStart_2189730 baseEnd_2189730 := by
    simpa [prefixWord, tailWord_2189730, baseEnd_2189730] using wordTrace_append hprefix tailTrace_2189730
  have hstable : (prefixWord ++ tailWord_2189730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189730).length < 2 ^ (prefixWord ++ tailWord_2189730).sum := by decide
  have hdescent : baseEnd_2189730 < baseStart_2189730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189733 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 3, 2, 4]
def baseStart_2189733 : Nat := 118140960795 + 2189733 * 2 ^ 59
def prefixEnd_2189733 : Nat := 4983230072969 + 3 ^ 40 * 2189733 * 2
def baseEnd_2189733 : Nat := 1124385534011786393267107

theorem tailTrace_2189733 : CollatzResearch.WordTrace tailWord_2189733 prefixEnd_2189733 1124385534011786393267107 := by
  unfold tailWord_2189733
  simp only [CollatzResearch.WordTrace]
  refine ⟨79866123775978792467709853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53244082517319194978473235 79866123775978792467709853)
  ·
    refine ⟨29949796415992047175391195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79866123775978792467709853 29949796415992047175391195)
    ·
      refine ⟨44924694623988070763086793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29949796415992047175391195 44924694623988070763086793)
      ·
        refine ⟨33693520967991053072315095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44924694623988070763086793 33693520967991053072315095)
        ·
          refine ⟨50540281451986579608472643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33693520967991053072315095 50540281451986579608472643)
          ·
            refine ⟨75810422177979869412708965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50540281451986579608472643 75810422177979869412708965)
            ·
              refine ⟨14214454158371225514882931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75810422177979869412708965 14214454158371225514882931)
              ·
                refine ⟨21321681237556838272324397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14214454158371225514882931 21321681237556838272324397)
                ·
                  refine ⟨7995630464083814352121649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21321681237556838272324397 7995630464083814352121649)
                  ·
                    refine ⟨5996722848062860764091237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7995630464083814352121649 5996722848062860764091237)
                    ·
                      refine ⟨1124385534011786393267107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5996722848062860764091237 1124385534011786393267107)
                      ·
                        rfl

theorem cell23_2189733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_2189733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189733 prefixEnd_2189733 := by exact prefixLift 2189733
  have htrace : WordTrace (prefixWord ++ tailWord_2189733) baseStart_2189733 baseEnd_2189733 := by
    simpa [prefixWord, tailWord_2189733, baseEnd_2189733] using wordTrace_append hprefix tailTrace_2189733
  have hstable : (prefixWord ++ tailWord_2189733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189733).length < 2 ^ (prefixWord ++ tailWord_2189733).sum := by decide
  have hdescent : baseEnd_2189733 < baseStart_2189733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189748 : List Nat := [2, 5, 2, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_2189748 : Nat := 118140960795 + 2189748 * 2 ^ 59
def prefixEnd_2189748 : Nat := 4983230072969 + 3 ^ 40 * 2189748 * 2
def baseEnd_2189748 : Nat := 1124393236221603834579539

theorem tailTrace_2189748 : CollatzResearch.WordTrace tailWord_2189748 prefixEnd_2189748 1124393236221603834579539 := by
  unfold tailWord_2189748
  simp only [CollatzResearch.WordTrace]
  refine ⟨39933335435462225014752949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53244447247282966686337265 39933335435462225014752949)
  ·
    refine ⟨3743750197074583595133089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39933335435462225014752949 3743750197074583595133089)
    ·
      refine ⟨2807812647805937696349817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3743750197074583595133089 2807812647805937696349817)
      ·
        refine ⟨2105859485854453272262363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2807812647805937696349817 2105859485854453272262363)
        ·
          refine ⟨3158789228781679908393545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2105859485854453272262363 3158789228781679908393545)
          ·
            refine ⟨2369091921586259931295159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3158789228781679908393545 2369091921586259931295159)
            ·
              refine ⟨3553637882379389896942739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2369091921586259931295159 3553637882379389896942739)
              ·
                refine ⟨5330456823569084845414109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3553637882379389896942739 5330456823569084845414109)
                ·
                  refine ⟨1998921308838406817030291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5330456823569084845414109 1998921308838406817030291)
                  ·
                    refine ⟨2998381963257610225545437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1998921308838406817030291 2998381963257610225545437)
                    ·
                      refine ⟨1124393236221603834579539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2998381963257610225545437 1124393236221603834579539)
                      ·
                        rfl

theorem cell23_2189748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_2189748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189748 prefixEnd_2189748 := by exact prefixLift 2189748
  have htrace : WordTrace (prefixWord ++ tailWord_2189748) baseStart_2189748 baseEnd_2189748 := by
    simpa [prefixWord, tailWord_2189748, baseEnd_2189748] using wordTrace_append hprefix tailTrace_2189748
  have hstable : (prefixWord ++ tailWord_2189748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189748).length < 2 ^ (prefixWord ++ tailWord_2189748).sum := by decide
  have hdescent : baseEnd_2189748 < baseStart_2189748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189754 : List Nat := [3, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2]
def baseStart_2189754 : Nat := 118140960795 + 2189754 * 2 ^ 59
def prefixEnd_2189754 : Nat := 4983230072969 + 3 ^ 40 * 2189754 * 2
def baseEnd_2189754 : Nat := 1124396317105530811104511

theorem tailTrace_2189754 : CollatzResearch.WordTrace tailWord_2189754 prefixEnd_2189754 1124396317105530811104511 := by
  unfold tailWord_2189754
  simp only [CollatzResearch.WordTrace]
  refine ⟨19966722427225678263556079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53244593139268475369482877 19966722427225678263556079)
  ·
    refine ⟨29950083640838517395334119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19966722427225678263556079 29950083640838517395334119)
    ·
      refine ⟨44925125461257776093001179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29950083640838517395334119 44925125461257776093001179)
      ·
        refine ⟨67387688191886664139501769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44925125461257776093001179 67387688191886664139501769)
        ·
          refine ⟨50540766143914998104626327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67387688191886664139501769 50540766143914998104626327)
          ·
            refine ⟨75811149215872497156939491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50540766143914998104626327 75811149215872497156939491)
            ·
              refine ⟨113716723823808745735409237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75811149215872497156939491 113716723823808745735409237)
              ·
                refine ⟨1332617857310258739086827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 113716723823808745735409237 1332617857310258739086827)
                ·
                  refine ⟨1998926785965388108630241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1332617857310258739086827 1998926785965388108630241)
                  ·
                    refine ⟨1499195089474041081472681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1998926785965388108630241 1499195089474041081472681)
                    ·
                      refine ⟨1124396317105530811104511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1499195089474041081472681 1124396317105530811104511)
                      ·
                        rfl

theorem cell23_2189754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2].length) (baseStart_2189754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189754 prefixEnd_2189754 := by exact prefixLift 2189754
  have htrace : WordTrace (prefixWord ++ tailWord_2189754) baseStart_2189754 baseEnd_2189754 := by
    simpa [prefixWord, tailWord_2189754, baseEnd_2189754] using wordTrace_append hprefix tailTrace_2189754
  have hstable : (prefixWord ++ tailWord_2189754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189754).length < 2 ^ (prefixWord ++ tailWord_2189754).sum := by decide
  have hdescent : baseEnd_2189754 < baseStart_2189754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189764 : List Nat := [2, 3, 3, 2, 2, 1, 1, 3, 2, 4]
def baseStart_2189764 : Nat := 118140960795 + 2189764 * 2 ^ 59
def prefixEnd_2189764 : Nat := 4983230072969 + 3 ^ 40 * 2189764 * 2
def baseEnd_2189764 : Nat := 374800483970691923993155

theorem tailTrace_2189764 : CollatzResearch.WordTrace tailWord_2189764 prefixEnd_2189764 374800483970691923993155 := by
  unfold tailWord_2189764
  simp only [CollatzResearch.WordTrace]
  refine ⟨39933627219433242381044173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53244836292577656508058897 39933627219433242381044173)
  ·
    refine ⟨14975110207287465892891565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39933627219433242381044173 14975110207287465892891565)
    ·
      refine ⟨5615666327732799709834337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14975110207287465892891565 5615666327732799709834337)
      ·
        refine ⟨4211749745799599782375753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5615666327732799709834337 4211749745799599782375753)
        ·
          refine ⟨3158812309349699836781815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4211749745799599782375753 3158812309349699836781815)
          ·
            refine ⟨4738218464024549755172723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3158812309349699836781815 4738218464024549755172723)
            ·
              refine ⟨7107327696036824632759085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4738218464024549755172723 7107327696036824632759085)
              ·
                refine ⟨2665247886013809237284657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7107327696036824632759085 2665247886013809237284657)
                ·
                  refine ⟨1998935914510356927963493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2665247886013809237284657 1998935914510356927963493)
                  ·
                    refine ⟨374800483970691923993155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1998935914510356927963493 374800483970691923993155)
                    ·
                      rfl

theorem cell23_2189764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_2189764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189764 prefixEnd_2189764 := by exact prefixLift 2189764
  have htrace : WordTrace (prefixWord ++ tailWord_2189764) baseStart_2189764 baseEnd_2189764 := by
    simpa [prefixWord, tailWord_2189764, baseEnd_2189764] using wordTrace_append hprefix tailTrace_2189764
  have hstable : (prefixWord ++ tailWord_2189764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189764).length < 2 ^ (prefixWord ++ tailWord_2189764).sum := by decide
  have hdescent : baseEnd_2189764 < baseStart_2189764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189770 : List Nat := [3, 1, 2, 1, 2, 2, 2, 3, 1, 3, 3]
def baseStart_2189770 : Nat := 118140960795 + 2189770 * 2 ^ 59
def prefixEnd_2189770 : Nat := 4983230072969 + 3 ^ 40 * 2189770 * 2
def baseEnd_2189770 : Nat := 1124404532796002748504437

theorem tailTrace_2189770 : CollatzResearch.WordTrace tailWord_2189770 prefixEnd_2189770 1124404532796002748504437 := by
  unfold tailWord_2189770
  simp only [CollatzResearch.WordTrace]
  refine ⟨19966868319211186946701691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53244982184563165191204509 19966868319211186946701691)
  ·
    refine ⟨29950302478816780420052537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19966868319211186946701691 29950302478816780420052537)
    ·
      refine ⟨22462726859112585315039403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29950302478816780420052537 22462726859112585315039403)
      ·
        refine ⟨33694090288668877972559105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22462726859112585315039403 33694090288668877972559105)
        ·
          refine ⟨25270567716501658479419329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33694090288668877972559105 25270567716501658479419329)
          ·
            refine ⟨18952925787376243859564497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25270567716501658479419329 18952925787376243859564497)
            ·
              refine ⟨14214694340532182894673373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18952925787376243859564497 14214694340532182894673373)
              ·
                refine ⟨5330510377699568585502515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14214694340532182894673373 5330510377699568585502515)
                ·
                  refine ⟨7995765566549352878253773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5330510377699568585502515 7995765566549352878253773)
                  ·
                    refine ⟨2998412087456007329345165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7995765566549352878253773 2998412087456007329345165)
                    ·
                      refine ⟨1124404532796002748504437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2998412087456007329345165 1124404532796002748504437)
                      ·
                        rfl

theorem cell23_2189770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_2189770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189770 prefixEnd_2189770 := by exact prefixLift 2189770
  have htrace : WordTrace (prefixWord ++ tailWord_2189770) baseStart_2189770 baseEnd_2189770 := by
    simpa [prefixWord, tailWord_2189770, baseEnd_2189770] using wordTrace_append hprefix tailTrace_2189770
  have hstable : (prefixWord ++ tailWord_2189770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189770).length < 2 ^ (prefixWord ++ tailWord_2189770).sum := by decide
  have hdescent : baseEnd_2189770 < baseStart_2189770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189803 : List Nat := [1, 1, 1, 1, 2, 3, 4, 2, 2, 6]
def baseStart_2189803 : Nat := 118140960795 + 2189803 * 2 ^ 59
def prefixEnd_2189803 : Nat := 4983230072969 + 3 ^ 40 * 2189803 * 2
def baseEnd_2189803 : Nat := 374807159219200373130595

theorem tailTrace_2189803 : CollatzResearch.WordTrace tailWord_2189803 prefixEnd_2189803 374807159219200373130595 := by
  unfold tailWord_2189803
  simp only [CollatzResearch.WordTrace]
  refine ⟨79868676885725194422758063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53245784590483462948505375 79868676885725194422758063)
  ·
    refine ⟨119803015328587791634137095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79868676885725194422758063 119803015328587791634137095)
    ·
      refine ⟨179704522992881687451205643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119803015328587791634137095 179704522992881687451205643)
      ·
        refine ⟨269556784489322531176808465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179704522992881687451205643 269556784489322531176808465)
        ·
          refine ⟨202167588366991898382606349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269556784489322531176808465 202167588366991898382606349)
          ·
            refine ⟨75812845637621961893477381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 202167588366991898382606349 75812845637621961893477381)
            ·
              refine ⟨14214908557054117855027009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75812845637621961893477381 14214908557054117855027009)
              ·
                refine ⟨10661181417790588391270257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14214908557054117855027009 10661181417790588391270257)
                ·
                  refine ⟨7995886063342941293452693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10661181417790588391270257 7995886063342941293452693)
                  ·
                    refine ⟨374807159219200373130595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7995886063342941293452693 374807159219200373130595)
                    ·
                      rfl

theorem cell23_2189803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 6].length) (baseStart_2189803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189803 prefixEnd_2189803 := by exact prefixLift 2189803
  have htrace : WordTrace (prefixWord ++ tailWord_2189803) baseStart_2189803 baseEnd_2189803 := by
    simpa [prefixWord, tailWord_2189803, baseEnd_2189803] using wordTrace_append hprefix tailTrace_2189803
  have hstable : (prefixWord ++ tailWord_2189803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189803).length < 2 ^ (prefixWord ++ tailWord_2189803).sum := by decide
  have hdescent : baseEnd_2189803 < baseStart_2189803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189805 : List Nat := [1, 5, 1, 3, 1, 3, 2, 2, 1, 2, 2]
def baseStart_2189805 : Nat := 118140960795 + 2189805 * 2 ^ 59
def prefixEnd_2189805 : Nat := 4983230072969 + 3 ^ 40 * 2189805 * 2
def baseEnd_2189805 : Nat := 1124422504618910111566777

theorem tailTrace_2189805 : CollatzResearch.WordTrace tailWord_2189805 prefixEnd_2189805 1124422504618910111566777 := by
  unfold tailWord_2189805
  simp only [CollatzResearch.WordTrace]
  refine ⟨79868749831717948764330869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53245833221145299176220579 79868749831717948764330869)
  ·
    refine ⟨7487695296723557696656019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79868749831717948764330869 7487695296723557696656019)
    ·
      refine ⟨11231542945085336544984029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7487695296723557696656019 11231542945085336544984029)
      ·
        refine ⟨4211828604407001204369011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11231542945085336544984029 4211828604407001204369011)
        ·
          refine ⟨6317742906610501806553517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4211828604407001204369011 6317742906610501806553517)
          ·
            refine ⟨2369153589978938177457569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6317742906610501806553517 2369153589978938177457569)
            ·
              refine ⟨1776865192484203633093177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2369153589978938177457569 1776865192484203633093177)
              ·
                refine ⟨1332648894363152724819883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1776865192484203633093177 1332648894363152724819883)
                ·
                  refine ⟨1998973341544729087229825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1332648894363152724819883 1998973341544729087229825)
                  ·
                    refine ⟨1499230006158546815422369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1998973341544729087229825 1499230006158546815422369)
                    ·
                      refine ⟨1124422504618910111566777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1499230006158546815422369 1124422504618910111566777)
                      ·
                        rfl

theorem cell23_2189805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_2189805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189805 prefixEnd_2189805 := by exact prefixLift 2189805
  have htrace : WordTrace (prefixWord ++ tailWord_2189805) baseStart_2189805 baseEnd_2189805 := by
    simpa [prefixWord, tailWord_2189805, baseEnd_2189805] using wordTrace_append hprefix tailTrace_2189805
  have hstable : (prefixWord ++ tailWord_2189805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189805).length < 2 ^ (prefixWord ++ tailWord_2189805).sum := by decide
  have hdescent : baseEnd_2189805 < baseStart_2189805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189827 : List Nat := [1, 1, 1, 3, 2, 1, 6, 1, 1, 4, 2]
def baseStart_2189827 : Nat := 118140960795 + 2189827 * 2 ^ 59
def prefixEnd_2189827 : Nat := 4983230072969 + 3 ^ 40 * 2189827 * 2
def baseEnd_2189827 : Nat := 1124433801193309025491675

theorem tailTrace_2189827 : CollatzResearch.WordTrace tailWord_2189827 prefixEnd_2189827 1124433801193309025491675 := by
  unfold tailWord_2189827
  simp only [CollatzResearch.WordTrace]
  refine ⟨79869552237638246521631735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53246368158425497681087823 79869552237638246521631735)
  ·
    refine ⟨119804328356457369782447603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79869552237638246521631735 119804328356457369782447603)
    ·
      refine ⟨179706492534686054673671405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119804328356457369782447603 179706492534686054673671405)
      ·
        refine ⟨67389934700507270502626777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179706492534686054673671405 67389934700507270502626777)
        ·
          refine ⟨50542451025380452876970083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67389934700507270502626777 50542451025380452876970083)
          ·
            refine ⟨75813676538070679315455125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50542451025380452876970083 75813676538070679315455125)
            ·
              refine ⟨3553766087722063092911959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75813676538070679315455125 3553766087722063092911959)
              ·
                refine ⟨5330649131583094639367939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3553766087722063092911959 5330649131583094639367939)
                ·
                  refine ⟨7995973697374641959051909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5330649131583094639367939 7995973697374641959051909)
                  ·
                    refine ⟨1499245068257745367322233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7995973697374641959051909 1499245068257745367322233)
                    ·
                      refine ⟨1124433801193309025491675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1499245068257745367322233 1124433801193309025491675)
                      ·
                        rfl

theorem cell23_2189827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 4, 2].length) (baseStart_2189827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189827 prefixEnd_2189827 := by exact prefixLift 2189827
  have htrace : WordTrace (prefixWord ++ tailWord_2189827) baseStart_2189827 baseEnd_2189827 := by
    simpa [prefixWord, tailWord_2189827, baseEnd_2189827] using wordTrace_append hprefix tailTrace_2189827
  have hstable : (prefixWord ++ tailWord_2189827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189827).length < 2 ^ (prefixWord ++ tailWord_2189827).sum := by decide
  have hdescent : baseEnd_2189827 < baseStart_2189827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189900 : List Nat := [2, 2, 1, 3, 1, 2, 1, 3, 1, 3, 4]
def baseStart_2189900 : Nat := 118140960795 + 2189900 * 2 ^ 59
def prefixEnd_2189900 : Nat := 4983230072969 + 3 ^ 40 * 2189900 * 2
def baseEnd_2189900 : Nat := 1124471285281087239878839

theorem tailTrace_2189900 : CollatzResearch.WordTrace tailWord_2189900 prefixEnd_2189900 1124471285281087239878839 := by
  unfold tailWord_2189900
  simp only [CollatzResearch.WordTrace]
  refine ⟨39936107383186889994519577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53248143177582519992692769 39936107383186889994519577)
  ·
    refine ⟨29952080537390167495889683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39936107383186889994519577 29952080537390167495889683)
    ·
      refine ⟨44928120806085251243834525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29952080537390167495889683 44928120806085251243834525)
      ·
        refine ⟨16848045302281969216437947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44928120806085251243834525 16848045302281969216437947)
        ·
          refine ⟨25272067953422953824656921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16848045302281969216437947 25272067953422953824656921)
          ·
            refine ⟨18954050965067215368492691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25272067953422953824656921 18954050965067215368492691)
            ·
              refine ⟨28431076447600823052739037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18954050965067215368492691 28431076447600823052739037)
              ·
                refine ⟨10661653667850308644777139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28431076447600823052739037 10661653667850308644777139)
                ·
                  refine ⟨15992480501775462967165709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10661653667850308644777139 15992480501775462967165709)
                  ·
                    refine ⟨5997180188165798612687141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15992480501775462967165709 5997180188165798612687141)
                    ·
                      refine ⟨1124471285281087239878839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5997180188165798612687141 1124471285281087239878839)
                      ·
                        rfl

theorem cell23_2189900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_2189900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189900 prefixEnd_2189900 := by exact prefixLift 2189900
  have htrace : WordTrace (prefixWord ++ tailWord_2189900) baseStart_2189900 baseEnd_2189900 := by
    simpa [prefixWord, tailWord_2189900, baseEnd_2189900] using wordTrace_append hprefix tailTrace_2189900
  have hstable : (prefixWord ++ tailWord_2189900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189900).length < 2 ^ (prefixWord ++ tailWord_2189900).sum := by decide
  have hdescent : baseEnd_2189900 < baseStart_2189900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189901 : List Nat := [1, 6, 1, 1, 2, 3, 1, 3, 5]
def baseStart_2189901 : Nat := 118140960795 + 2189901 * 2 ^ 59
def prefixEnd_2189901 : Nat := 4983230072969 + 3 ^ 40 * 2189901 * 2
def baseEnd_2189901 : Nat := 124941310973526859551815

theorem tailTrace_2189901 : CollatzResearch.WordTrace tailWord_2189901 prefixEnd_2189901 124941310973526859551815 := by
  unfold tailWord_2189901
  simp only [CollatzResearch.WordTrace]
  refine ⟨79872251239370157159825557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53248167492913438106550371 79872251239370157159825557)
  ·
    refine ⟨3744011776845476116866823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 79872251239370157159825557 3744011776845476116866823)
    ·
      refine ⟨5616017665268214175300235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3744011776845476116866823 5616017665268214175300235)
      ·
        refine ⟨8424026497902321262950353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5616017665268214175300235 8424026497902321262950353)
        ·
          refine ⟨6318019873426740947212765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8424026497902321262950353 6318019873426740947212765)
          ·
            refine ⟨2369257452535027855204787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6318019873426740947212765 2369257452535027855204787)
            ·
              refine ⟨3553886178802541782807181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2369257452535027855204787 3553886178802541782807181)
              ·
                refine ⟨1332707317050953168552693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3553886178802541782807181 1332707317050953168552693)
                ·
                  refine ⟨124941310973526859551815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1332707317050953168552693 124941310973526859551815)
                  ·
                    rfl

theorem cell23_2189901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_2189901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189901 prefixEnd_2189901 := by exact prefixLift 2189901
  have htrace : WordTrace (prefixWord ++ tailWord_2189901) baseStart_2189901 baseEnd_2189901 := by
    simpa [prefixWord, tailWord_2189901, baseEnd_2189901] using wordTrace_append hprefix tailTrace_2189901
  have hstable : (prefixWord ++ tailWord_2189901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189901).length < 2 ^ (prefixWord ++ tailWord_2189901).sum := by decide
  have hdescent : baseEnd_2189901 < baseStart_2189901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189918 : List Nat := [4, 4, 1, 2, 1, 2, 1, 1, 7]
def baseStart_2189918 : Nat := 118140960795 + 2189918 * 2 ^ 59
def prefixEnd_2189918 : Nat := 4983230072969 + 3 ^ 40 * 2189918 * 2
def baseEnd_2189918 : Nat := 124942280881429796605973

theorem tailTrace_2189918 : CollatzResearch.WordTrace tailWord_2189918 prefixEnd_2189918 124942280881429796605973 := by
  unfold tailWord_2189918
  simp only [CollatzResearch.WordTrace]
  refine ⟨9984108910038571132899301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53248580853539046042129605 9984108910038571132899301)
  ·
    refine ⟨1872020420632232087418619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9984108910038571132899301 1872020420632232087418619)
    ·
      refine ⟨2808030630948348131127929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1872020420632232087418619 2808030630948348131127929)
      ·
        refine ⟨2106022973211261098345947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2808030630948348131127929 2106022973211261098345947)
        ·
          refine ⟨3159034459816891647518921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2106022973211261098345947 3159034459816891647518921)
          ·
            refine ⟨2369275844862668735639191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3159034459816891647518921 2369275844862668735639191)
            ·
              refine ⟨3553913767294003103458787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2369275844862668735639191 3553913767294003103458787)
              ·
                refine ⟨5330870650941004655188181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3553913767294003103458787 5330870650941004655188181)
                ·
                  refine ⟨124942280881429796605973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5330870650941004655188181 124942280881429796605973)
                  ·
                    rfl

theorem cell23_2189918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_2189918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189918 prefixEnd_2189918 := by exact prefixLift 2189918
  have htrace : WordTrace (prefixWord ++ tailWord_2189918) baseStart_2189918 baseEnd_2189918 := by
    simpa [prefixWord, tailWord_2189918, baseEnd_2189918] using wordTrace_append hprefix tailTrace_2189918
  have hstable : (prefixWord ++ tailWord_2189918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189918).length < 2 ^ (prefixWord ++ tailWord_2189918).sum := by decide
  have hdescent : baseEnd_2189918 < baseStart_2189918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189967 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 5, 1, 3]
def baseStart_2189967 : Nat := 118140960795 + 2189967 * 2 ^ 59
def prefixEnd_2189967 : Nat := 4983230072969 + 3 ^ 40 * 2189967 * 2
def baseEnd_2189967 : Nat := 1124505688484938477741031

theorem tailTrace_2189967 : CollatzResearch.WordTrace tailWord_2189967 prefixEnd_2189967 1124505688484938477741031 := by
  unfold tailWord_2189967
  simp only [CollatzResearch.WordTrace]
  refine ⟨79874658457131050431728155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53249772304754033621152103 79874658457131050431728155)
  ·
    refine ⟨119811987685696575647592233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79874658457131050431728155 119811987685696575647592233)
    ·
      refine ⟨89858990764272431735694175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119811987685696575647592233 89858990764272431735694175)
      ·
        refine ⟨134788486146408647603541263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89858990764272431735694175 134788486146408647603541263)
        ·
          refine ⟨202182729219612971405311895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134788486146408647603541263 202182729219612971405311895)
          ·
            refine ⟨303274093829419457107967843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202182729219612971405311895 303274093829419457107967843)
            ·
              refine ⟨454911140744129185661951765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303274093829419457107967843 454911140744129185661951765)
              ·
                refine ⟨21323959722381055577903989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 454911140744129185661951765 21323959722381055577903989)
                ·
                  refine ⟨1999121223973223960428499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21323959722381055577903989 1999121223973223960428499)
                  ·
                    refine ⟨2998681835959835940642749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1999121223973223960428499 2998681835959835940642749)
                    ·
                      refine ⟨1124505688484938477741031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2998681835959835940642749 1124505688484938477741031)
                      ·
                        rfl

theorem cell23_2189967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5, 1, 3].length) (baseStart_2189967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189967 prefixEnd_2189967 := by exact prefixLift 2189967
  have htrace : WordTrace (prefixWord ++ tailWord_2189967) baseStart_2189967 baseEnd_2189967 := by
    simpa [prefixWord, tailWord_2189967, baseEnd_2189967] using wordTrace_append hprefix tailTrace_2189967
  have hstable : (prefixWord ++ tailWord_2189967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189967).length < 2 ^ (prefixWord ++ tailWord_2189967).sum := by decide
  have hdescent : baseEnd_2189967 < baseStart_2189967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189978 : List Nat := [3, 1, 1, 6, 1, 1, 1, 4, 1, 4]
def baseStart_2189978 : Nat := 118140960795 + 2189978 * 2 ^ 59
def prefixEnd_2189978 : Nat := 4983230072969 + 3 ^ 40 * 2189978 * 2
def baseEnd_2189978 : Nat := 374837112257379311567827

theorem tailTrace_2189978 : CollatzResearch.WordTrace tailWord_2189978 prefixEnd_2189978 374837112257379311567827 := by
  unfold tailWord_2189978
  simp only [CollatzResearch.WordTrace]
  refine ⟨19968764915022799827594647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53250039773394132873585725 19968764915022799827594647)
  ·
    refine ⟨29953147372534199741391971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19968764915022799827594647 29953147372534199741391971)
    ·
      refine ⟨44929721058801299612087957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29953147372534199741391971 44929721058801299612087957)
      ·
        refine ⟨2106080674631310919316623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44929721058801299612087957 2106080674631310919316623)
        ·
          refine ⟨3159121011946966378974935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2106080674631310919316623 3159121011946966378974935)
          ·
            refine ⟨4738681517920449568462403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3159121011946966378974935 4738681517920449568462403)
            ·
              refine ⟨7108022276880674352693605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4738681517920449568462403 7108022276880674352693605)
              ·
                refine ⟨1332754176915126441130051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7108022276880674352693605 1332754176915126441130051)
                ·
                  refine ⟨1999131265372689661695077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1332754176915126441130051 1999131265372689661695077)
                  ·
                    refine ⟨374837112257379311567827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1999131265372689661695077 374837112257379311567827)
                    ·
                      rfl

theorem cell23_2189978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4, 1, 4].length) (baseStart_2189978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2189978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2189978 prefixEnd_2189978 := by exact prefixLift 2189978
  have htrace : WordTrace (prefixWord ++ tailWord_2189978) baseStart_2189978 baseEnd_2189978 := by
    simpa [prefixWord, tailWord_2189978, baseEnd_2189978] using wordTrace_append hprefix tailTrace_2189978
  have hstable : (prefixWord ++ tailWord_2189978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189978).length < 2 ^ (prefixWord ++ tailWord_2189978).sum := by decide
  have hdescent : baseEnd_2189978 < baseStart_2189978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190024 : List Nat := [2, 1, 3, 1, 2, 4, 1, 3, 1, 1, 4]
def baseStart_2190024 : Nat := 118140960795 + 2190024 * 2 ^ 59
def prefixEnd_2190024 : Nat := 4983230072969 + 3 ^ 40 * 2190024 * 2
def baseEnd_2190024 : Nat := 1124534956882244754728269

theorem tailTrace_2190024 : CollatzResearch.WordTrace tailWord_2190024 prefixEnd_2190024 1124534956882244754728269 := by
  unfold tailWord_2190024
  simp only [CollatzResearch.WordTrace]
  refine ⟨39938368708962274583276563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53251158278616366111035417 39938368708962274583276563)
  ·
    refine ⟨59907553063443411874914845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39938368708962274583276563 59907553063443411874914845)
    ·
      refine ⟨22465332398791279453093067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59907553063443411874914845 22465332398791279453093067)
      ·
        refine ⟨33697998598186919179639601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22465332398791279453093067 33697998598186919179639601)
        ·
          refine ⟨25273498948640189384729701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33697998598186919179639601 25273498948640189384729701)
          ·
            refine ⟨4738781052870035509636819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25273498948640189384729701 4738781052870035509636819)
            ·
              refine ⟨7108171579305053264455229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4738781052870035509636819 7108171579305053264455229)
              ·
                refine ⟨2665564342239394974170711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7108171579305053264455229 2665564342239394974170711)
                ·
                  refine ⟨3998346513359092461256067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2665564342239394974170711 3998346513359092461256067)
                  ·
                    refine ⟨5997519770038638691884101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3998346513359092461256067 5997519770038638691884101)
                    ·
                      refine ⟨1124534956882244754728269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5997519770038638691884101 1124534956882244754728269)
                      ·
                        rfl

theorem cell23_2190024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_2190024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190024 prefixEnd_2190024 := by exact prefixLift 2190024
  have htrace : WordTrace (prefixWord ++ tailWord_2190024) baseStart_2190024 baseEnd_2190024 := by
    simpa [prefixWord, tailWord_2190024, baseEnd_2190024] using wordTrace_append hprefix tailTrace_2190024
  have hstable : (prefixWord ++ tailWord_2190024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190024).length < 2 ^ (prefixWord ++ tailWord_2190024).sum := by decide
  have hdescent : baseEnd_2190024 < baseStart_2190024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190041 : List Nat := [1, 2, 1, 2, 3, 2, 4, 1, 3, 2, 2]
def baseStart_2190041 : Nat := 118140960795 + 2190041 * 2 ^ 59
def prefixEnd_2190041 : Nat := 4983230072969 + 3 ^ 40 * 2190041 * 2
def baseEnd_2190041 : Nat := 1124543686053371188215691

theorem tailTrace_2190041 : CollatzResearch.WordTrace tailWord_2190041 prefixEnd_2190041 1124543686053371188215691 := by
  unfold tailWord_2190041
  simp only [CollatzResearch.WordTrace]
  refine ⟨79877357458862961069921977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53251571639241974046614651 79877357458862961069921977)
  ·
    refine ⟨59908018094147220802441483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79877357458862961069921977 59908018094147220802441483)
    ·
      refine ⟨89862027141220831203662225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59908018094147220802441483 89862027141220831203662225)
      ·
        refine ⟨67396520355915623402746669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89862027141220831203662225 67396520355915623402746669)
        ·
          refine ⟨25273695133468358776030001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67396520355915623402746669 25273695133468358776030001)
          ·
            refine ⟨18955271350101269082022501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25273695133468358776030001 18955271350101269082022501)
            ·
              refine ⟨3554113378143987952879219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18955271350101269082022501 3554113378143987952879219)
              ·
                refine ⟨5331170067215981929318829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3554113378143987952879219 5331170067215981929318829)
                ·
                  refine ⟨1999188775205993223494561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5331170067215981929318829 1999188775205993223494561)
                  ·
                    refine ⟨1499391581404494917620921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1999188775205993223494561 1499391581404494917620921)
                    ·
                      refine ⟨1124543686053371188215691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1499391581404494917620921 1124543686053371188215691)
                      ·
                        rfl

theorem cell23_2190041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3, 2, 2].length) (baseStart_2190041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190041 prefixEnd_2190041 := by exact prefixLift 2190041
  have htrace : WordTrace (prefixWord ++ tailWord_2190041) baseStart_2190041 baseEnd_2190041 := by
    simpa [prefixWord, tailWord_2190041, baseEnd_2190041] using wordTrace_append hprefix tailTrace_2190041
  have hstable : (prefixWord ++ tailWord_2190041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190041).length < 2 ^ (prefixWord ++ tailWord_2190041).sum := by decide
  have hdescent : baseEnd_2190041 < baseStart_2190041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190044 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_2190044 : Nat := 118140960795 + 2190044 * 2 ^ 59
def prefixEnd_2190044 : Nat := 4983230072969 + 3 ^ 40 * 2190044 * 2
def baseEnd_2190044 : Nat := 1124545226495334676478177

theorem tailTrace_2190044 : CollatzResearch.WordTrace tailWord_2190044 prefixEnd_2190044 1124545226495334676478177 := by
  unfold tailWord_2190044
  simp only [CollatzResearch.WordTrace]
  refine ⟨39938733438926046291140593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53251644585234728388187457 39938733438926046291140593)
  ·
    refine ⟨29954050079194534718355445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39938733438926046291140593 29954050079194534718355445)
    ·
      refine ⟨2808192194924487629845823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29954050079194534718355445 2808192194924487629845823)
      ·
        refine ⟨4212288292386731444768735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2808192194924487629845823 4212288292386731444768735)
        ·
          refine ⟨6318432438580097167153103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4212288292386731444768735 6318432438580097167153103)
          ·
            refine ⟨9477648657870145750729655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6318432438580097167153103 9477648657870145750729655)
            ·
              refine ⟨14216472986805218626094483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9477648657870145750729655 14216472986805218626094483)
              ·
                refine ⟨21324709480207827939141725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14216472986805218626094483 21324709480207827939141725)
                ·
                  refine ⟨7996766055077935477178147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21324709480207827939141725 7996766055077935477178147)
                  ·
                    refine ⟨11995149082616903215767221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7996766055077935477178147 11995149082616903215767221)
                    ·
                      refine ⟨1124545226495334676478177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11995149082616903215767221 1124545226495334676478177)
                      ·
                        rfl

theorem cell23_2190044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_2190044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190044 prefixEnd_2190044 := by exact prefixLift 2190044
  have htrace : WordTrace (prefixWord ++ tailWord_2190044) baseStart_2190044 baseEnd_2190044 := by
    simpa [prefixWord, tailWord_2190044, baseEnd_2190044] using wordTrace_append hprefix tailTrace_2190044
  have hstable : (prefixWord ++ tailWord_2190044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190044).length < 2 ^ (prefixWord ++ tailWord_2190044).sum := by decide
  have hdescent : baseEnd_2190044 < baseStart_2190044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190061 : List Nat := [1, 5, 1, 2, 1, 1, 4, 2, 1, 2, 3]
def baseStart_2190061 : Nat := 118140960795 + 2190061 * 2 ^ 59
def prefixEnd_2190061 : Nat := 4983230072969 + 3 ^ 40 * 2190061 * 2
def baseEnd_2190061 : Nat := 1124553955666461109965599

theorem tailTrace_2190061 : CollatzResearch.WordTrace tailWord_2190061 prefixEnd_2190061 1124553955666461109965599 := by
  unfold tailWord_2190061
  simp only [CollatzResearch.WordTrace]
  refine ⟨79878086918790504485650037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53252057945860336323766691 79878086918790504485650037)
  ·
    refine ⟨7488570648636609795529691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79878086918790504485650037 7488570648636609795529691)
    ·
      refine ⟨11232855972954914693294537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7488570648636609795529691 11232855972954914693294537)
      ·
        refine ⟨8424641979716186019970903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11232855972954914693294537 8424641979716186019970903)
        ·
          refine ⟨12636962969574279029956355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8424641979716186019970903 12636962969574279029956355)
          ·
            refine ⟨18955444454361418544934533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12636962969574279029956355 18955444454361418544934533)
            ·
              refine ⟨3554145835192765977175225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18955444454361418544934533 3554145835192765977175225)
              ·
                refine ⟨2665609376394574482881419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3554145835192765977175225 2665609376394574482881419)
                ·
                  refine ⟨3998414064591861724322129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2665609376394574482881419 3998414064591861724322129)
                  ·
                    refine ⟨2998810548443896293241597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3998414064591861724322129 2998810548443896293241597)
                    ·
                      refine ⟨1124553955666461109965599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2998810548443896293241597 1124553955666461109965599)
                      ·
                        rfl

theorem cell23_2190061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_2190061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190061 prefixEnd_2190061 := by exact prefixLift 2190061
  have htrace : WordTrace (prefixWord ++ tailWord_2190061) baseStart_2190061 baseEnd_2190061 := by
    simpa [prefixWord, tailWord_2190061, baseEnd_2190061] using wordTrace_append hprefix tailTrace_2190061
  have hstable : (prefixWord ++ tailWord_2190061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190061).length < 2 ^ (prefixWord ++ tailWord_2190061).sum := by decide
  have hdescent : baseEnd_2190061 < baseStart_2190061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190069 : List Nat := [1, 3, 6, 1, 1, 2, 1, 3, 1, 1, 3]
def baseStart_2190069 : Nat := 118140960795 + 2190069 * 2 ^ 59
def prefixEnd_2190069 : Nat := 4983230072969 + 3 ^ 40 * 2190069 * 2
def baseEnd_2190069 : Nat := 1124558063511697078665563

theorem tailTrace_2190069 : CollatzResearch.WordTrace tailWord_2190069 prefixEnd_2190069 1124558063511697078665563 := by
  unfold tailWord_2190069
  simp only [CollatzResearch.WordTrace]
  refine ⟨79878378702761521851941261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53252252468507681234627507 79878378702761521851941261)
  ·
    refine ⟨29954392013535570694477973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79878378702761521851941261 29954392013535570694477973)
    ·
      refine ⟨1404112125634479876303655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29954392013535570694477973 1404112125634479876303655)
      ·
        refine ⟨2106168188451719814455483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1404112125634479876303655 2106168188451719814455483)
        ·
          refine ⟨3159252282677579721683225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2106168188451719814455483 3159252282677579721683225)
          ·
            refine ⟨2369439212008184791262419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3159252282677579721683225 2369439212008184791262419)
            ·
              refine ⟨3554158818012277186893629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2369439212008184791262419 3554158818012277186893629)
              ·
                refine ⟨1332809556754603945085111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3554158818012277186893629 1332809556754603945085111)
                ·
                  refine ⟨1999214335131905917627667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1332809556754603945085111 1999214335131905917627667)
                  ·
                    refine ⟨2998821502697858876441501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1999214335131905917627667 2998821502697858876441501)
                    ·
                      refine ⟨1124558063511697078665563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2998821502697858876441501 1124558063511697078665563)
                      ·
                        rfl

theorem cell23_2190069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_2190069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190069 prefixEnd_2190069 := by exact prefixLift 2190069
  have htrace : WordTrace (prefixWord ++ tailWord_2190069) baseStart_2190069 baseEnd_2190069 := by
    simpa [prefixWord, tailWord_2190069, baseEnd_2190069] using wordTrace_append hprefix tailTrace_2190069
  have hstable : (prefixWord ++ tailWord_2190069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190069).length < 2 ^ (prefixWord ++ tailWord_2190069).sum := by decide
  have hdescent : baseEnd_2190069 < baseStart_2190069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190074 : List Nat := [3, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3]
def baseStart_2190074 : Nat := 118140960795 + 2190074 * 2 ^ 59
def prefixEnd_2190074 : Nat := 4983230072969 + 3 ^ 40 * 2190074 * 2
def baseEnd_2190074 : Nat := 1124560630914969559103039

theorem tailTrace_2190074 : CollatzResearch.WordTrace tailWord_2190074 prefixEnd_2190074 1124560630914969559103039 := by
  unfold tailWord_2190074
  simp only [CollatzResearch.WordTrace]
  refine ⟨19969640266935851926468319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53252374045162271803915517 19969640266935851926468319)
  ·
    refine ⟨29954460400403777889702479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19969640266935851926468319 29954460400403777889702479)
    ·
      refine ⟨44931690600605666834553719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29954460400403777889702479 44931690600605666834553719)
      ·
        refine ⟨67397535900908500251830579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44931690600605666834553719 67397535900908500251830579)
        ·
          refine ⟨101096303851362750377745869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67397535900908500251830579 101096303851362750377745869)
          ·
            refine ⟨37911113944261031391654701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101096303851362750377745869 37911113944261031391654701)
            ·
              refine ⟨14216667729097886771870513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37911113944261031391654701 14216667729097886771870513)
              ·
                refine ⟨10662500796823415078902885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14216667729097886771870513 10662500796823415078902885)
                ·
                  refine ⟨1999218899404390327294291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10662500796823415078902885 1999218899404390327294291)
                  ·
                    refine ⟨2998828349106585490941437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1999218899404390327294291 2998828349106585490941437)
                    ·
                      refine ⟨1124560630914969559103039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2998828349106585490941437 1124560630914969559103039)
                      ·
                        rfl

theorem cell23_2190074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3].length) (baseStart_2190074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190074 prefixEnd_2190074 := by exact prefixLift 2190074
  have htrace : WordTrace (prefixWord ++ tailWord_2190074) baseStart_2190074 baseEnd_2190074 := by
    simpa [prefixWord, tailWord_2190074, baseEnd_2190074] using wordTrace_append hprefix tailTrace_2190074
  have hstable : (prefixWord ++ tailWord_2190074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190074).length < 2 ^ (prefixWord ++ tailWord_2190074).sum := by decide
  have hdescent : baseEnd_2190074 < baseStart_2190074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190108 : List Nat := [2, 2, 3, 1, 1, 3, 4, 1, 2, 1, 3]
def baseStart_2190108 : Nat := 118140960795 + 2190108 * 2 ^ 59
def prefixEnd_2190108 : Nat := 4983230072969 + 3 ^ 40 * 2190108 * 2
def baseEnd_2190108 : Nat := 1124578089257222426077883

theorem tailTrace_2190108 : CollatzResearch.WordTrace tailWord_2190108 prefixEnd_2190108 1124578089257222426077883 := by
  unfold tailWord_2190108
  simp only [CollatzResearch.WordTrace]
  refine ⟨39939900574810115756305489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53253200766413487675073985 39939900574810115756305489)
  ·
    refine ⟨29954925431107586817229117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39939900574810115756305489 29954925431107586817229117)
    ·
      refine ⟨11233097036665345056460919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29954925431107586817229117 11233097036665345056460919)
      ·
        refine ⟨16849645554998017584691379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11233097036665345056460919 16849645554998017584691379)
        ·
          refine ⟨25274468332497026377037069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16849645554998017584691379 25274468332497026377037069)
          ·
            refine ⟨9477925624686384891388901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25274468332497026377037069 9477925624686384891388901)
            ·
              refine ⟨1777111054628697167135419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9477925624686384891388901 1777111054628697167135419)
              ·
                refine ⟨2665666581943045750703129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1777111054628697167135419 2665666581943045750703129)
                ·
                  refine ⟨1999249936457284313027347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2665666581943045750703129 1999249936457284313027347)
                  ·
                    refine ⟨2998874904685926469541021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1999249936457284313027347 2998874904685926469541021)
                    ·
                      refine ⟨1124578089257222426077883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2998874904685926469541021 1124578089257222426077883)
                      ·
                        rfl

theorem cell23_2190108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_2190108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190108 prefixEnd_2190108 := by exact prefixLift 2190108
  have htrace : WordTrace (prefixWord ++ tailWord_2190108) baseStart_2190108 baseEnd_2190108 := by
    simpa [prefixWord, tailWord_2190108, baseEnd_2190108] using wordTrace_append hprefix tailTrace_2190108
  have hstable : (prefixWord ++ tailWord_2190108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190108).length < 2 ^ (prefixWord ++ tailWord_2190108).sum := by decide
  have hdescent : baseEnd_2190108 < baseStart_2190108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190117 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 4, 1, 5]
def baseStart_2190117 : Nat := 118140960795 + 2190117 * 2 ^ 59
def prefixEnd_2190117 : Nat := 4983230072969 + 3 ^ 40 * 2190117 * 2
def baseEnd_2190117 : Nat := 1124582710583112890865341

theorem tailTrace_2190117 : CollatzResearch.WordTrace tailWord_2190117 prefixEnd_2190117 1124582710583112890865341 := by
  unfold tailWord_2190117
  simp only [CollatzResearch.WordTrace]
  refine ⟨79880129406587626049688605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53253419604391750699792403 79880129406587626049688605)
  ·
    refine ⟨29955048527470359768633227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79880129406587626049688605 29955048527470359768633227)
    ·
      refine ⟨44932572791205539652949841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29955048527470359768633227 44932572791205539652949841)
      ·
        refine ⟨33699429593404154739712381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44932572791205539652949841 33699429593404154739712381)
        ·
          refine ⟨12637286097526558027392143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33699429593404154739712381 12637286097526558027392143)
          ·
            refine ⟨18955929146289837041088215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12637286097526558027392143 18955929146289837041088215)
            ·
              refine ⟨28433893719434755561632323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18955929146289837041088215 28433893719434755561632323)
              ·
                refine ⟨42650840579152133342448485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28433893719434755561632323 42650840579152133342448485)
                ·
                  refine ⟨7997032608591025001709091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42650840579152133342448485 7997032608591025001709091)
                  ·
                    refine ⟨11995548912886537502563637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7997032608591025001709091 11995548912886537502563637)
                    ·
                      refine ⟨1124582710583112890865341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11995548912886537502563637 1124582710583112890865341)
                      ·
                        rfl

theorem cell23_2190117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_2190117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190117 prefixEnd_2190117 := by exact prefixLift 2190117
  have htrace : WordTrace (prefixWord ++ tailWord_2190117) baseStart_2190117 baseEnd_2190117 := by
    simpa [prefixWord, tailWord_2190117, baseEnd_2190117] using wordTrace_append hprefix tailTrace_2190117
  have hstable : (prefixWord ++ tailWord_2190117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190117).length < 2 ^ (prefixWord ++ tailWord_2190117).sum := by decide
  have hdescent : baseEnd_2190117 < baseStart_2190117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190131 : List Nat := [1, 1, 1, 2, 6, 2, 1, 2, 1, 4, 2]
def baseStart_2190131 : Nat := 118140960795 + 2190131 * 2 ^ 59
def prefixEnd_2190131 : Nat := 4983230072969 + 3 ^ 40 * 2190131 * 2
def baseEnd_2190131 : Nat := 1124589899312275836090277

theorem tailTrace_2190131 : CollatzResearch.WordTrace tailWord_2190131 prefixEnd_2190131 1124589899312275836090277 := by
  unfold tailWord_2190131
  simp only [CollatzResearch.WordTrace]
  refine ⟨79880640028536906440698247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53253760019024604293798831 79880640028536906440698247)
  ·
    refine ⟨119820960042805359661047371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79880640028536906440698247 119820960042805359661047371)
    ·
      refine ⟨179731440064208039491571057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119820960042805359661047371 179731440064208039491571057)
      ·
        refine ⟨134798580048156029618678293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179731440064208039491571057 134798580048156029618678293)
        ·
          refine ⟨6318683439757313888375545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 134798580048156029618678293 6318683439757313888375545)
          ·
            refine ⟨4739012579817985416281659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6318683439757313888375545 4739012579817985416281659)
            ·
              refine ⟨7108518869726978124422489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4739012579817985416281659 7108518869726978124422489)
              ·
                refine ⟨5331389152295233593316867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7108518869726978124422489 5331389152295233593316867)
                ·
                  refine ⟨7997083728442850389975301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5331389152295233593316867 7997083728442850389975301)
                  ·
                    refine ⟨1499453199083034448120369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7997083728442850389975301 1499453199083034448120369)
                    ·
                      refine ⟨1124589899312275836090277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1499453199083034448120369 1124589899312275836090277)
                      ·
                        rfl

theorem cell23_2190131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 4, 2].length) (baseStart_2190131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190131 prefixEnd_2190131 := by exact prefixLift 2190131
  have htrace : WordTrace (prefixWord ++ tailWord_2190131) baseStart_2190131 baseEnd_2190131 := by
    simpa [prefixWord, tailWord_2190131, baseEnd_2190131] using wordTrace_append hprefix tailTrace_2190131
  have hstable : (prefixWord ++ tailWord_2190131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190131).length < 2 ^ (prefixWord ++ tailWord_2190131).sum := by decide
  have hdescent : baseEnd_2190131 < baseStart_2190131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190177 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 3, 2, 5]
def baseStart_2190177 : Nat := 118140960795 + 2190177 * 2 ^ 59
def prefixEnd_2190177 : Nat := 4983230072969 + 3 ^ 40 * 2190177 * 2
def baseEnd_2190177 : Nat := 1124613519422382656115065

theorem tailTrace_2190177 : CollatzResearch.WordTrace tailWord_2190177 prefixEnd_2190177 1124613519422382656115065 := by
  unfold tailWord_2190177
  simp only [CollatzResearch.WordTrace]
  refine ⟨79882317786370256296872785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53254878524246837531248523 79882317786370256296872785)
  ·
    refine ⟨59911738339777692222654589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79882317786370256296872785 59911738339777692222654589)
    ·
      refine ⟨22466901877416634583495471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59911738339777692222654589 22466901877416634583495471)
      ·
        refine ⟨33700352816124951875243207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22466901877416634583495471 33700352816124951875243207)
        ·
          refine ⟨50550529224187427812864811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33700352816124951875243207 50550529224187427812864811)
          ·
            refine ⟨75825793836281141719297217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50550529224187427812864811 75825793836281141719297217)
            ·
              refine ⟨56869345377210856289472913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75825793836281141719297217 56869345377210856289472913)
              ·
                refine ⟨42652009032908142217104685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56869345377210856289472913 42652009032908142217104685)
                ·
                  refine ⟨15994503387340553331414257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42652009032908142217104685 15994503387340553331414257)
                  ·
                    refine ⟨11995877540505414998560693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15994503387340553331414257 11995877540505414998560693)
                    ·
                      refine ⟨1124613519422382656115065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11995877540505414998560693 1124613519422382656115065)
                      ·
                        rfl

theorem cell23_2190177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_2190177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190177 prefixEnd_2190177 := by exact prefixLift 2190177
  have htrace : WordTrace (prefixWord ++ tailWord_2190177) baseStart_2190177 baseEnd_2190177 := by
    simpa [prefixWord, tailWord_2190177, baseEnd_2190177] using wordTrace_append hprefix tailTrace_2190177
  have hstable : (prefixWord ++ tailWord_2190177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190177).length < 2 ^ (prefixWord ++ tailWord_2190177).sum := by decide
  have hdescent : baseEnd_2190177 < baseStart_2190177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190184 : List Nat := [2, 1, 4, 2, 1, 3, 1, 1, 1, 7]
def baseStart_2190184 : Nat := 118140960795 + 2190184 * 2 ^ 59
def prefixEnd_2190184 : Nat := 4983230072969 + 3 ^ 40 * 2190184 * 2
def baseEnd_2190184 : Nat := 374872371262321376242511

theorem tailTrace_2190184 : CollatzResearch.WordTrace tailWord_2190184 prefixEnd_2190184 374872371262321376242511 := by
  unfold tailWord_2190184
  simp only [CollatzResearch.WordTrace]
  refine ⟨39941286548672448246188803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53255048731563264328251737 39941286548672448246188803)
  ·
    refine ⟨59911929823008672369283205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39941286548672448246188803 59911929823008672369283205)
    ·
      refine ⟨11233486841814126069240601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59911929823008672369283205 11233486841814126069240601)
      ·
        refine ⟨8425115131360594551930451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11233486841814126069240601 8425115131360594551930451)
        ·
          refine ⟨12637672697040891827895677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8425115131360594551930451 12637672697040891827895677)
          ·
            refine ⟨4739127261390334435460879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12637672697040891827895677 4739127261390334435460879)
            ·
              refine ⟨7108690892085501653191319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4739127261390334435460879 7108690892085501653191319)
              ·
                refine ⟨10663036338128252479786979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7108690892085501653191319 10663036338128252479786979)
                ·
                  refine ⟨15994554507192378719680469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10663036338128252479786979 15994554507192378719680469)
                  ·
                    refine ⟨374872371262321376242511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15994554507192378719680469 374872371262321376242511)
                    ·
                      rfl

theorem cell23_2190184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_2190184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190184 prefixEnd_2190184 := by exact prefixLift 2190184
  have htrace : WordTrace (prefixWord ++ tailWord_2190184) baseStart_2190184 baseEnd_2190184 := by
    simpa [prefixWord, tailWord_2190184, baseEnd_2190184] using wordTrace_append hprefix tailTrace_2190184
  have hstable : (prefixWord ++ tailWord_2190184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190184).length < 2 ^ (prefixWord ++ tailWord_2190184).sum := by decide
  have hdescent : baseEnd_2190184 < baseStart_2190184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190204 : List Nat := [2, 2, 2, 1, 1, 1, 1, 6, 2, 1, 4]
def baseStart_2190204 : Nat := 118140960795 + 2190204 * 2 ^ 59
def prefixEnd_2190204 : Nat := 4983230072969 + 3 ^ 40 * 2190204 * 2
def baseEnd_2190204 : Nat := 1124627383400054050477441

theorem tailTrace_2190204 : CollatzResearch.WordTrace tailWord_2190204 prefixEnd_2190204 1124627383400054050477441 := by
  unfold tailWord_2190204
  simp only [CollatzResearch.WordTrace]
  refine ⟨39941651278636219954052833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53255535038181626605403777 39941651278636219954052833)
  ·
    refine ⟨29956238458977164965539625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39941651278636219954052833 29956238458977164965539625)
    ·
      refine ⟨22467178844232873724154719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29956238458977164965539625 22467178844232873724154719)
      ·
        refine ⟨33700768266349310586232079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22467178844232873724154719 33700768266349310586232079)
        ·
          refine ⟨50551152399523965879348119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33700768266349310586232079 50551152399523965879348119)
          ·
            refine ⟨75826728599285948819022179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50551152399523965879348119 75826728599285948819022179)
            ·
              refine ⟨113740092898928923228533269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75826728599285948819022179 113740092898928923228533269)
              ·
                refine ⟨5331566854637293276337497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 113740092898928923228533269 5331566854637293276337497)
                ·
                  refine ⟨3998675140977969957253123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5331566854637293276337497 3998675140977969957253123)
                  ·
                    refine ⟨5998012711466954935879685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3998675140977969957253123 5998012711466954935879685)
                    ·
                      refine ⟨1124627383400054050477441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5998012711466954935879685 1124627383400054050477441)
                      ·
                        rfl

theorem cell23_2190204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_2190204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190204 prefixEnd_2190204 := by exact prefixLift 2190204
  have htrace : WordTrace (prefixWord ++ tailWord_2190204) baseStart_2190204 baseEnd_2190204 := by
    simpa [prefixWord, tailWord_2190204, baseEnd_2190204] using wordTrace_append hprefix tailTrace_2190204
  have hstable : (prefixWord ++ tailWord_2190204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190204).length < 2 ^ (prefixWord ++ tailWord_2190204).sum := by decide
  have hdescent : baseEnd_2190204 < baseStart_2190204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190207 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 5]
def baseStart_2190207 : Nat := 118140960795 + 2190207 * 2 ^ 59
def prefixEnd_2190207 : Nat := 4983230072969 + 3 ^ 40 * 2190207 * 2
def baseEnd_2190207 : Nat := 1124628923842017538739927

theorem tailTrace_2190207 : CollatzResearch.WordTrace tailWord_2190207 prefixEnd_2190207 1124628923842017538739927 := by
  unfold tailWord_2190207
  simp only [CollatzResearch.WordTrace]
  refine ⟨79883411976261571420464875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53255607984174380946976583 79883411976261571420464875)
  ·
    refine ⟨119825117964392357130697313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79883411976261571420464875 119825117964392357130697313)
    ·
      refine ⟨89868838473294267848022985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119825117964392357130697313 89868838473294267848022985)
      ·
        refine ⟨67401628854970700886017239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89868838473294267848022985 67401628854970700886017239)
        ·
          refine ⟨101102443282456051329025859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67401628854970700886017239 101102443282456051329025859)
          ·
            refine ⟨151653664923684076993538789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101102443282456051329025859 151653664923684076993538789)
            ·
              refine ⟨28435062173190764436288523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 151653664923684076993538789 28435062173190764436288523)
              ·
                refine ⟨42652593259786146654432785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28435062173190764436288523 42652593259786146654432785)
                ·
                  refine ⟨31989444944839609990824589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42652593259786146654432785 31989444944839609990824589)
                  ·
                    refine ⟨11996041854314853746559221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31989444944839609990824589 11996041854314853746559221)
                    ·
                      refine ⟨1124628923842017538739927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11996041854314853746559221 1124628923842017538739927)
                      ·
                        rfl

theorem cell23_2190207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_2190207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190207 prefixEnd_2190207 := by exact prefixLift 2190207
  have htrace : WordTrace (prefixWord ++ tailWord_2190207) baseStart_2190207 baseEnd_2190207 := by
    simpa [prefixWord, tailWord_2190207, baseEnd_2190207] using wordTrace_append hprefix tailTrace_2190207
  have hstable : (prefixWord ++ tailWord_2190207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190207).length < 2 ^ (prefixWord ++ tailWord_2190207).sum := by decide
  have hdescent : baseEnd_2190207 < baseStart_2190207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190241 : List Nat := [1, 2, 3, 4, 1, 1, 2, 1, 1, 4, 3]
def baseStart_2190241 : Nat := 118140960795 + 2190241 * 2 ^ 59
def prefixEnd_2190241 : Nat := 4983230072969 + 3 ^ 40 * 2190241 * 2
def baseEnd_2190241 : Nat := 1124646382184270405714771

theorem tailTrace_2190241 : CollatzResearch.WordTrace tailWord_2190241 prefixEnd_2190241 1124646382184270405714771 := by
  unfold tailWord_2190241
  simp only [CollatzResearch.WordTrace]
  refine ⟨79884652058138395227202577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53256434705425596818135051 79884652058138395227202577)
  ·
    refine ⟨59913489043603796420401933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79884652058138395227202577 59913489043603796420401933)
    ·
      refine ⟨22467558391351423657650725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59913489043603796420401933 22467558391351423657650725)
      ·
        refine ⟨4212667198378391935809511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22467558391351423657650725 4212667198378391935809511)
        ·
          refine ⟨6319000797567587903714267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4212667198378391935809511 6319000797567587903714267)
          ·
            refine ⟨9478501196351381855571401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6319000797567587903714267 9478501196351381855571401)
            ·
              refine ⟨7108875897263536391678551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9478501196351381855571401 7108875897263536391678551)
              ·
                refine ⟨10663313845895304587517827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7108875897263536391678551 10663313845895304587517827)
                ·
                  refine ⟨15994970768842956881276741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10663313845895304587517827 15994970768842956881276741)
                  ·
                    refine ⟨2999057019158054415239389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15994970768842956881276741 2999057019158054415239389)
                    ·
                      refine ⟨1124646382184270405714771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2999057019158054415239389 1124646382184270405714771)
                      ·
                        rfl

theorem cell23_2190241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_2190241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190241 prefixEnd_2190241 := by exact prefixLift 2190241
  have htrace : WordTrace (prefixWord ++ tailWord_2190241) baseStart_2190241 baseEnd_2190241 := by
    simpa [prefixWord, tailWord_2190241, baseEnd_2190241] using wordTrace_append hprefix tailTrace_2190241
  have hstable : (prefixWord ++ tailWord_2190241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190241).length < 2 ^ (prefixWord ++ tailWord_2190241).sum := by decide
  have hdescent : baseEnd_2190241 < baseStart_2190241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190265 : List Nat := [1, 2, 1, 4, 2, 3, 3, 2, 1, 4]
def baseStart_2190265 : Nat := 118140960795 + 2190265 * 2 ^ 59
def prefixEnd_2190265 : Nat := 4983230072969 + 3 ^ 40 * 2190265 * 2
def baseEnd_2190265 : Nat := 374886235239992770604887

theorem tailTrace_2190265 : CollatzResearch.WordTrace tailWord_2190265 prefixEnd_2190265 374886235239992770604887 := by
  unfold tailWord_2190265
  simp only [CollatzResearch.WordTrace]
  refine ⟨79885527410051447326076249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53257018273367631550717499 79885527410051447326076249)
  ·
    refine ⟨59914145557538585494557187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79885527410051447326076249 59914145557538585494557187)
    ·
      refine ⟨89871218336307878241835781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59914145557538585494557187 89871218336307878241835781)
      ·
        refine ⟨16850853438057727170344209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89871218336307878241835781 16850853438057727170344209)
        ·
          refine ⟨12638140078543295377758157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16850853438057727170344209 12638140078543295377758157)
          ·
            refine ⟨4739302529453735766659309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12638140078543295377758157 4739302529453735766659309)
            ·
              refine ⟨1777238448545150912497241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4739302529453735766659309 1777238448545150912497241)
              ·
                refine ⟨1332928836408863184372931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1777238448545150912497241 1332928836408863184372931)
                ·
                  refine ⟨1999393254613294776559397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1332928836408863184372931 1999393254613294776559397)
                  ·
                    refine ⟨374886235239992770604887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1999393254613294776559397 374886235239992770604887)
                    ·
                      rfl

theorem cell23_2190265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2, 1, 4].length) (baseStart_2190265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190265 prefixEnd_2190265 := by exact prefixLift 2190265
  have htrace : WordTrace (prefixWord ++ tailWord_2190265) baseStart_2190265 baseEnd_2190265 := by
    simpa [prefixWord, tailWord_2190265, baseEnd_2190265] using wordTrace_append hprefix tailTrace_2190265
  have hstable : (prefixWord ++ tailWord_2190265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190265).length < 2 ^ (prefixWord ++ tailWord_2190265).sum := by decide
  have hdescent : baseEnd_2190265 < baseStart_2190265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190271 : List Nat := [1, 1, 2, 2, 2, 1, 2, 5, 3, 1, 3]
def baseStart_2190271 : Nat := 118140960795 + 2190271 * 2 ^ 59
def prefixEnd_2190271 : Nat := 4983230072969 + 3 ^ 40 * 2190271 * 2
def baseEnd_2190271 : Nat := 1124661786603905288339633

theorem tailTrace_2190271 : CollatzResearch.WordTrace tailWord_2190271 prefixEnd_2190271 1124661786603905288339633 := by
  unfold tailWord_2190271
  simp only [CollatzResearch.WordTrace]
  refine ⟨79885746248029710350794667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53257164165353140233863111 79885746248029710350794667)
  ·
    refine ⟨119828619372044565526192001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79885746248029710350794667 119828619372044565526192001)
    ·
      refine ⟨89871464529033424144644001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119828619372044565526192001 89871464529033424144644001)
      ·
        refine ⟨67403598396775068108483001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89871464529033424144644001 67403598396775068108483001)
        ·
          refine ⟨50552698797581301081362251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67403598396775068108483001 50552698797581301081362251)
          ·
            refine ⟨75829048196371951622043377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50552698797581301081362251 75829048196371951622043377)
            ·
              refine ⟨56871786147278963716532533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75829048196371951622043377 56871786147278963716532533)
              ·
                refine ⟨5331729951307402848424925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56871786147278963716532533 5331729951307402848424925)
                ·
                  refine ⟨1999398731740276068159347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5331729951307402848424925 1999398731740276068159347)
                  ·
                    refine ⟨2999098097610414102239021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1999398731740276068159347 2999098097610414102239021)
                    ·
                      refine ⟨1124661786603905288339633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2999098097610414102239021 1124661786603905288339633)
                      ·
                        rfl

theorem cell23_2190271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3, 1, 3].length) (baseStart_2190271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190271 prefixEnd_2190271 := by exact prefixLift 2190271
  have htrace : WordTrace (prefixWord ++ tailWord_2190271) baseStart_2190271 baseEnd_2190271 := by
    simpa [prefixWord, tailWord_2190271, baseEnd_2190271] using wordTrace_append hprefix tailTrace_2190271
  have hstable : (prefixWord ++ tailWord_2190271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190271).length < 2 ^ (prefixWord ++ tailWord_2190271).sum := by decide
  have hdescent : baseEnd_2190271 < baseStart_2190271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190298 : List Nat := [3, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2]
def baseStart_2190298 : Nat := 118140960795 + 2190298 * 2 ^ 59
def prefixEnd_2190298 : Nat := 4983230072969 + 3 ^ 40 * 2190298 * 2
def baseEnd_2190298 : Nat := 1124675650581576682702009

theorem tailTrace_2190298 : CollatzResearch.WordTrace tailWord_2190298 prefixEnd_2190298 1124675650581576682702009 := by
  unfold tailWord_2190298
  simp only [CollatzResearch.WordTrace]
  refine ⟨19971682754732973490506887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53257820679287929308018365 19971682754732973490506887)
  ·
    refine ⟨29957524132099460235760331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19971682754732973490506887 29957524132099460235760331)
    ·
      refine ⟨44936286198149190353640497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29957524132099460235760331 44936286198149190353640497)
      ·
        refine ⟨33702214648611892765230373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44936286198149190353640497 33702214648611892765230373)
        ·
          refine ⟨6319165246614729893480695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33702214648611892765230373 6319165246614729893480695)
          ·
            refine ⟨9478747869922094840221043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6319165246614729893480695 9478747869922094840221043)
            ·
              refine ⟨14218121804883142260331565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9478747869922094840221043 14218121804883142260331565)
              ·
                refine ⟨5331795676831178347624337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14218121804883142260331565 5331795676831178347624337)
                ·
                  refine ⟨3998846757623383760718253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5331795676831178347624337 3998846757623383760718253)
                  ·
                    refine ⟨1499567534108768910269345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3998846757623383760718253 1499567534108768910269345)
                    ·
                      refine ⟨1124675650581576682702009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1499567534108768910269345 1124675650581576682702009)
                      ·
                        rfl

theorem cell23_2190298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2].length) (baseStart_2190298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190298 prefixEnd_2190298 := by exact prefixLift 2190298
  have htrace : WordTrace (prefixWord ++ tailWord_2190298) baseStart_2190298 baseEnd_2190298 := by
    simpa [prefixWord, tailWord_2190298, baseEnd_2190298] using wordTrace_append hprefix tailTrace_2190298
  have hstable : (prefixWord ++ tailWord_2190298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190298).length < 2 ^ (prefixWord ++ tailWord_2190298).sum := by decide
  have hdescent : baseEnd_2190298 < baseStart_2190298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190328 : List Nat := [2, 1, 2, 1, 1, 3, 1, 5, 3, 2, 2]
def baseStart_2190328 : Nat := 118140960795 + 2190328 * 2 ^ 59
def prefixEnd_2190328 : Nat := 4983230072969 + 3 ^ 40 * 2190328 * 2
def baseEnd_2190328 : Nat := 1124691055001211565326871

theorem tailTrace_2190328 : CollatzResearch.WordTrace tailWord_2190328 prefixEnd_2190328 1124691055001211565326871 := by
  unfold tailWord_2190328
  simp only [CollatzResearch.WordTrace]
  refine ⟨39943912604411604542809819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53258550139215472723746425 39943912604411604542809819)
  ·
    refine ⟨59915868906617406814214729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39943912604411604542809819 59915868906617406814214729)
    ·
      refine ⟨44936901679963055110661047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59915868906617406814214729 44936901679963055110661047)
      ·
        refine ⟨67405352519944582665991571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44936901679963055110661047 67405352519944582665991571)
        ·
          refine ⟨101108028779916873998987357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67405352519944582665991571 101108028779916873998987357)
          ·
            refine ⟨37915510792468827749620259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101108028779916873998987357 37915510792468827749620259)
            ·
              refine ⟨56873266188703241624430389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37915510792468827749620259 56873266188703241624430389)
              ·
                refine ⟨5331868705190928902290349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56873266188703241624430389 5331868705190928902290349)
                ·
                  refine ⟨1999450764446598338358881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5331868705190928902290349 1999450764446598338358881)
                  ·
                    refine ⟨1499588073334948753769161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1999450764446598338358881 1499588073334948753769161)
                    ·
                      refine ⟨1124691055001211565326871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1499588073334948753769161 1124691055001211565326871)
                      ·
                        rfl

theorem cell23_2190328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 3, 2, 2].length) (baseStart_2190328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190328 prefixEnd_2190328 := by exact prefixLift 2190328
  have htrace : WordTrace (prefixWord ++ tailWord_2190328) baseStart_2190328 baseEnd_2190328 := by
    simpa [prefixWord, tailWord_2190328, baseEnd_2190328] using wordTrace_append hprefix tailTrace_2190328
  have hstable : (prefixWord ++ tailWord_2190328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190328).length < 2 ^ (prefixWord ++ tailWord_2190328).sum := by decide
  have hdescent : baseEnd_2190328 < baseStart_2190328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190341 : List Nat := [1, 3, 1, 1, 2, 3, 4, 1, 1, 2, 4]
def baseStart_2190341 : Nat := 118140960795 + 2190341 * 2 ^ 59
def prefixEnd_2190341 : Nat := 4983230072969 + 3 ^ 40 * 2190341 * 2
def baseEnd_2190341 : Nat := 1124697730249720014464311

theorem tailTrace_2190341 : CollatzResearch.WordTrace tailWord_2190341 prefixEnd_2190341 1124697730249720014464311 := by
  unfold tailWord_2190341
  simp only [CollatzResearch.WordTrace]
  refine ⟨79888299357776112305842877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53258866238517408203895251 79888299357776112305842877)
  ·
    refine ⟨29958112259166042114691079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79888299357776112305842877 29958112259166042114691079)
    ·
      refine ⟨44937168388749063172036619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29958112259166042114691079 44937168388749063172036619)
      ·
        refine ⟨67405752583123594758054929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44937168388749063172036619 67405752583123594758054929)
        ·
          refine ⟨50554314437342696068541197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67405752583123594758054929 50554314437342696068541197)
          ·
            refine ⟨18957867914003511025702949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50554314437342696068541197 18957867914003511025702949)
            ·
              refine ⟨3554600233875658317319303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18957867914003511025702949 3554600233875658317319303)
              ·
                refine ⟨5331900350813487475978955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3554600233875658317319303 5331900350813487475978955)
                ·
                  refine ⟨7997850526220231213968433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5331900350813487475978955 7997850526220231213968433)
                  ·
                    refine ⟨5998387894665173410476325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7997850526220231213968433 5998387894665173410476325)
                    ·
                      refine ⟨1124697730249720014464311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5998387894665173410476325 1124697730249720014464311)
                      ·
                        rfl

theorem cell23_2190341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 2, 4].length) (baseStart_2190341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190341 prefixEnd_2190341 := by exact prefixLift 2190341
  have htrace : WordTrace (prefixWord ++ tailWord_2190341) baseStart_2190341 baseEnd_2190341 := by
    simpa [prefixWord, tailWord_2190341, baseEnd_2190341] using wordTrace_append hprefix tailTrace_2190341
  have hstable : (prefixWord ++ tailWord_2190341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190341).length < 2 ^ (prefixWord ++ tailWord_2190341).sum := by decide
  have hdescent : baseEnd_2190341 < baseStart_2190341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190361 : List Nat := [1, 2, 1, 2, 1, 1, 6, 2, 1, 3, 3]
def baseStart_2190361 : Nat := 118140960795 + 2190361 * 2 ^ 59
def prefixEnd_2190361 : Nat := 4983230072969 + 3 ^ 40 * 2190361 * 2
def baseEnd_2190361 : Nat := 1124707999862809936214219

theorem tailTrace_2190361 : CollatzResearch.WordTrace tailWord_2190361 prefixEnd_2190361 1124707999862809936214219 := by
  unfold tailWord_2190361
  simp only [CollatzResearch.WordTrace]
  refine ⟨79889028817703655721570937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53259352545135770481047291 79889028817703655721570937)
  ·
    refine ⟨59916771613277741791178203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79889028817703655721570937 59916771613277741791178203)
    ·
      refine ⟨89875157419916612686767305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59916771613277741791178203 89875157419916612686767305)
      ·
        refine ⟨67406368064937459515075479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89875157419916612686767305 67406368064937459515075479)
        ·
          refine ⟨101109552097406189272613219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67406368064937459515075479 101109552097406189272613219)
          ·
            refine ⟨151664328146109283908919829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101109552097406189272613219 151664328146109283908919829)
            ·
              refine ⟨7109265381848872683230617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 151664328146109283908919829 7109265381848872683230617)
              ·
                refine ⟨5331949036386654512422963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7109265381848872683230617 5331949036386654512422963)
                ·
                  refine ⟨7997923554579981768634445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5331949036386654512422963 7997923554579981768634445)
                  ·
                    refine ⟨2999221332967493163237917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7997923554579981768634445 2999221332967493163237917)
                    ·
                      refine ⟨1124707999862809936214219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2999221332967493163237917 1124707999862809936214219)
                      ·
                        rfl

theorem cell23_2190361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 3, 3].length) (baseStart_2190361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190361 prefixEnd_2190361 := by exact prefixLift 2190361
  have htrace : WordTrace (prefixWord ++ tailWord_2190361) baseStart_2190361 baseEnd_2190361 := by
    simpa [prefixWord, tailWord_2190361, baseEnd_2190361] using wordTrace_append hprefix tailTrace_2190361
  have hstable : (prefixWord ++ tailWord_2190361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190361).length < 2 ^ (prefixWord ++ tailWord_2190361).sum := by decide
  have hdescent : baseEnd_2190361 < baseStart_2190361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190362 : List Nat := [3, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2]
def baseStart_2190362 : Nat := 118140960795 + 2190362 * 2 ^ 59
def prefixEnd_2190362 : Nat := 4983230072969 + 3 ^ 40 * 2190362 * 2
def baseEnd_2190362 : Nat := 1124708513343464432301715

theorem tailTrace_2190362 : CollatzResearch.WordTrace tailWord_2190362 prefixEnd_2190362 1124708513343464432301715 := by
  unfold tailWord_2190362
  simp only [CollatzResearch.WordTrace]
  refine ⟨19972266322675008223089335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53259376860466688594904893 19972266322675008223089335)
  ·
    refine ⟨29958399484012512334634003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19972266322675008223089335 29958399484012512334634003)
    ·
      refine ⟨44937599226018768501951005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29958399484012512334634003 44937599226018768501951005)
      ·
        refine ⟨16851599709757038188231627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44937599226018768501951005 16851599709757038188231627)
        ·
          refine ⟨25277399564635557282347441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16851599709757038188231627 25277399564635557282347441)
          ·
            refine ⟨18958049673476667961760581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25277399564635557282347441 18958049673476667961760581)
            ·
              refine ⟨3554634313776875242830109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18958049673476667961760581 3554634313776875242830109)
              ·
                refine ⟨1332987867666328216061291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3554634313776875242830109 1332987867666328216061291)
                ·
                  refine ⟨1999481801499492324091937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1332987867666328216061291 1999481801499492324091937)
                  ·
                    refine ⟨1499611351124619243068953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1999481801499492324091937 1499611351124619243068953)
                    ·
                      refine ⟨1124708513343464432301715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1499611351124619243068953 1124708513343464432301715)
                      ·
                        rfl

theorem cell23_2190362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_2190362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190362 prefixEnd_2190362 := by exact prefixLift 2190362
  have htrace : WordTrace (prefixWord ++ tailWord_2190362) baseStart_2190362 baseEnd_2190362 := by
    simpa [prefixWord, tailWord_2190362, baseEnd_2190362] using wordTrace_append hprefix tailTrace_2190362
  have hstable : (prefixWord ++ tailWord_2190362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190362).length < 2 ^ (prefixWord ++ tailWord_2190362).sum := by decide
  have hdescent : baseEnd_2190362 < baseStart_2190362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190365 : List Nat := [1, 4, 2, 2, 3, 1, 1, 3, 1, 2, 3]
def baseStart_2190365 : Nat := 118140960795 + 2190365 * 2 ^ 59
def prefixEnd_2190365 : Nat := 4983230072969 + 3 ^ 40 * 2190365 * 2
def baseEnd_2190365 : Nat := 1124710053785427920564201

theorem tailTrace_2190365 : CollatzResearch.WordTrace tailWord_2190365 prefixEnd_2190365 1124710053785427920564201 := by
  unfold tailWord_2190365
  simp only [CollatzResearch.WordTrace]
  refine ⟨79889174709689164404716549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53259449806459442936477699 79889174709689164404716549)
  ·
    refine ⟨14979220258066718325884353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79889174709689164404716549 14979220258066718325884353)
    ·
      refine ⟨11234415193550038744413265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14979220258066718325884353 11234415193550038744413265)
      ·
        refine ⟨8425811395162529058309949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11234415193550038744413265 8425811395162529058309949)
        ·
          refine ⟨3159679273185948396866231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8425811395162529058309949 3159679273185948396866231)
          ·
            refine ⟨4739518909778922595299347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3159679273185948396866231 4739518909778922595299347)
            ·
              refine ⟨7109278364668383892949021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4739518909778922595299347 7109278364668383892949021)
              ·
                refine ⟨2665979386750643959855883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7109278364668383892949021 2665979386750643959855883)
                ·
                  refine ⟨3998969080125965939783825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2665979386750643959855883 3998969080125965939783825)
                  ·
                    refine ⟨2999226810094474454837869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3998969080125965939783825 2999226810094474454837869)
                    ·
                      refine ⟨1124710053785427920564201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2999226810094474454837869 1124710053785427920564201)
                      ·
                        rfl

theorem cell23_2190365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_2190365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190365 prefixEnd_2190365 := by exact prefixLift 2190365
  have htrace : WordTrace (prefixWord ++ tailWord_2190365) baseStart_2190365 baseEnd_2190365 := by
    simpa [prefixWord, tailWord_2190365, baseEnd_2190365] using wordTrace_append hprefix tailTrace_2190365
  have hstable : (prefixWord ++ tailWord_2190365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190365).length < 2 ^ (prefixWord ++ tailWord_2190365).sum := by decide
  have hdescent : baseEnd_2190365 < baseStart_2190365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190421 : List Nat := [1, 3, 2, 2, 1, 2, 3, 1, 2, 1, 5]
def baseStart_2190421 : Nat := 118140960795 + 2190421 * 2 ^ 59
def prefixEnd_2190421 : Nat := 4983230072969 + 3 ^ 40 * 2190421 * 2
def baseEnd_2190421 : Nat := 1124738808702079701463943

theorem tailTrace_2190421 : CollatzResearch.WordTrace tailWord_2190421 prefixEnd_2190421 1124738808702079701463943 := by
  unfold tailWord_2190421
  simp only [CollatzResearch.WordTrace]
  refine ⟨79891217197486285968755117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53260811464990857312503411 79891217197486285968755117)
  ·
    refine ⟨29959206449057357238283169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79891217197486285968755117 29959206449057357238283169)
    ·
      refine ⟨22469404836793017928712377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29959206449057357238283169 22469404836793017928712377)
      ·
        refine ⟨16852053627594763446534283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22469404836793017928712377 16852053627594763446534283)
        ·
          refine ⟨25278080441392145169801425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16852053627594763446534283 25278080441392145169801425)
          ·
            refine ⟨18958560331044108877351069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25278080441392145169801425 18958560331044108877351069)
            ·
              refine ⟨7109460124141540829006651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18958560331044108877351069 7109460124141540829006651)
              ·
                refine ⟨10664190186212311243509977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7109460124141540829006651 10664190186212311243509977)
                ·
                  refine ⟨7998142639659233432632483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10664190186212311243509977 7998142639659233432632483)
                  ·
                    refine ⟨11997213959488850148948725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7998142639659233432632483 11997213959488850148948725)
                    ·
                      refine ⟨1124738808702079701463943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11997213959488850148948725 1124738808702079701463943)
                      ·
                        rfl

theorem cell23_2190421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_2190421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190421 prefixEnd_2190421 := by exact prefixLift 2190421
  have htrace : WordTrace (prefixWord ++ tailWord_2190421) baseStart_2190421 baseEnd_2190421 := by
    simpa [prefixWord, tailWord_2190421, baseEnd_2190421] using wordTrace_append hprefix tailTrace_2190421
  have hstable : (prefixWord ++ tailWord_2190421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190421).length < 2 ^ (prefixWord ++ tailWord_2190421).sum := by decide
  have hdescent : baseEnd_2190421 < baseStart_2190421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190435 : List Nat := [1, 1, 1, 5, 1, 1, 1, 6, 2, 2, 2]
def baseStart_2190435 : Nat := 118140960795 + 2190435 * 2 ^ 59
def prefixEnd_2190435 : Nat := 4983230072969 + 3 ^ 40 * 2190435 * 2
def baseEnd_2190435 : Nat := 1124745997431242646688879

theorem tailTrace_2190435 : CollatzResearch.WordTrace tailWord_2190435 prefixEnd_2190435 1124745997431242646688879 := by
  unfold tailWord_2190435
  simp only [CollatzResearch.WordTrace]
  refine ⟨79891727819435566359764759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53261151879623710906509839 79891727819435566359764759)
  ·
    refine ⟨119837591729153349539647139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79891727819435566359764759 119837591729153349539647139)
    ·
      refine ⟨179756387593730024309470709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119837591729153349539647139 179756387593730024309470709)
      ·
        refine ⟨16852161336912189779012879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 179756387593730024309470709 16852161336912189779012879)
        ·
          refine ⟨25278242005368284668519319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16852161336912189779012879 25278242005368284668519319)
          ·
            refine ⟨37917363008052427002778979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25278242005368284668519319 37917363008052427002778979)
            ·
              refine ⟨56876044512078640504168469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37917363008052427002778979 56876044512078640504168469)
              ·
                refine ⟨2666064586503686273632897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56876044512078640504168469 2666064586503686273632897)
                ·
                  refine ⟨1999548439877764705224673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2666064586503686273632897 1999548439877764705224673)
                  ·
                    refine ⟨1499661329908323528918505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1999548439877764705224673 1499661329908323528918505)
                    ·
                      refine ⟨1124745997431242646688879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1499661329908323528918505 1124745997431242646688879)
                      ·
                        rfl

theorem cell23_2190435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_2190435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190435 prefixEnd_2190435 := by exact prefixLift 2190435
  have htrace : WordTrace (prefixWord ++ tailWord_2190435) baseStart_2190435 baseEnd_2190435 := by
    simpa [prefixWord, tailWord_2190435, baseEnd_2190435] using wordTrace_append hprefix tailTrace_2190435
  have hstable : (prefixWord ++ tailWord_2190435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190435).length < 2 ^ (prefixWord ++ tailWord_2190435).sum := by decide
  have hdescent : baseEnd_2190435 < baseStart_2190435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190441 : List Nat := [1, 2, 1, 1, 1, 6, 3, 1, 7]
def baseStart_2190441 : Nat := 118140960795 + 2190441 * 2 ^ 59
def prefixEnd_2190441 : Nat := 4983230072969 + 3 ^ 40 * 2190441 * 2
def baseEnd_2190441 : Nat := 124972119812796624801539

theorem tailTrace_2190441 : CollatzResearch.WordTrace tailWord_2190441 prefixEnd_2190441 124972119812796624801539 := by
  unfold tailWord_2190441
  simp only [CollatzResearch.WordTrace]
  refine ⟨79891946657413829384483177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53261297771609219589655451 79891946657413829384483177)
  ·
    refine ⟨59918959993060372038362383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79891946657413829384483177 59918959993060372038362383)
    ·
      refine ⟨89878439989590558057543575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59918959993060372038362383 89878439989590558057543575)
      ·
        refine ⟨134817659984385837086315363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89878439989590558057543575 134817659984385837086315363)
        ·
          refine ⟨202226489976578755629473045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134817659984385837086315363 202226489976578755629473045)
          ·
            refine ⟨9479366717652129170131549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 202226489976578755629473045 9479366717652129170131549)
            ·
              refine ⟨3554762519119548438799331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9479366717652129170131549 3554762519119548438799331)
              ·
                refine ⟨5332143778679322658198997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3554762519119548438799331 5332143778679322658198997)
                ·
                  refine ⟨124972119812796624801539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5332143778679322658198997 124972119812796624801539)
                  ·
                    rfl

theorem cell23_2190441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 7].length) (baseStart_2190441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190441 prefixEnd_2190441 := by exact prefixLift 2190441
  have htrace : WordTrace (prefixWord ++ tailWord_2190441) baseStart_2190441 baseEnd_2190441 := by
    simpa [prefixWord, tailWord_2190441, baseEnd_2190441] using wordTrace_append hprefix tailTrace_2190441
  have hstable : (prefixWord ++ tailWord_2190441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190441).length < 2 ^ (prefixWord ++ tailWord_2190441).sum := by decide
  have hdescent : baseEnd_2190441 < baseStart_2190441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190488 : List Nat := [2, 1, 2, 4, 2, 1, 2, 2, 2, 5]
def baseStart_2190488 : Nat := 118140960795 + 2190488 * 2 ^ 59
def prefixEnd_2190488 : Nat := 4983230072969 + 3 ^ 40 * 2190488 * 2
def baseEnd_2190488 : Nat := 374924403968643646442045

theorem tailTrace_2190488 : CollatzResearch.WordTrace tailWord_2190488 prefixEnd_2190488 374924403968643646442045 := by
  unfold tailWord_2190488
  simp only [CollatzResearch.WordTrace]
  refine ⟨39946830444121778205722059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53262440592162370940962745 39946830444121778205722059)
  ·
    refine ⟨59920245666182667308583089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39946830444121778205722059 59920245666182667308583089)
    ·
      refine ⟨44940184249637000481437317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59920245666182667308583089 44940184249637000481437317)
      ·
        refine ⟨8426284546806937590269497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44940184249637000481437317 8426284546806937590269497)
        ·
          refine ⟨6319713410105203192702123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8426284546806937590269497 6319713410105203192702123)
          ·
            refine ⟨9479570115157804789053185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6319713410105203192702123 9479570115157804789053185)
            ·
              refine ⟨7109677586368353591789889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9479570115157804789053185 7109677586368353591789889)
              ·
                refine ⟨5332258189776265193842417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7109677586368353591789889 5332258189776265193842417)
                ·
                  refine ⟨3999193642332198895381813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5332258189776265193842417 3999193642332198895381813)
                  ·
                    refine ⟨374924403968643646442045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3999193642332198895381813 374924403968643646442045)
                    ·
                      rfl

theorem cell23_2190488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 2, 5].length) (baseStart_2190488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190488 prefixEnd_2190488 := by exact prefixLift 2190488
  have htrace : WordTrace (prefixWord ++ tailWord_2190488) baseStart_2190488 baseEnd_2190488 := by
    simpa [prefixWord, tailWord_2190488, baseEnd_2190488] using wordTrace_append hprefix tailTrace_2190488
  have hstable : (prefixWord ++ tailWord_2190488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190488).length < 2 ^ (prefixWord ++ tailWord_2190488).sum := by decide
  have hdescent : baseEnd_2190488 < baseStart_2190488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190492 : List Nat := [2, 2, 3, 2, 1, 4, 2, 2, 5]
def baseStart_2190492 : Nat := 118140960795 + 2190492 * 2 ^ 59
def prefixEnd_2190492 : Nat := 4983230072969 + 3 ^ 40 * 2190492 * 2
def baseEnd_2190492 : Nat := 124975029536505435964013

theorem tailTrace_2190492 : CollatzResearch.WordTrace tailWord_2190492 prefixEnd_2190492 124975029536505435964013 := by
  unfold tailWord_2190492
  simp only [CollatzResearch.WordTrace]
  refine ⟨39946903390114532547294865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53262537853486043396393153 39946903390114532547294865)
  ·
    refine ⟨29960177542585899410471149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39946903390114532547294865 29960177542585899410471149)
    ·
      refine ⟨11235066578469712278926681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29960177542585899410471149 11235066578469712278926681)
      ·
        refine ⟨8426299933852284209195011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11235066578469712278926681 8426299933852284209195011)
        ·
          refine ⟨12639449900778426313792517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8426299933852284209195011 12639449900778426313792517)
          ·
            refine ⟨2369896856395954933836097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12639449900778426313792517 2369896856395954933836097)
            ·
              refine ⟨1777422642296966200377073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2369896856395954933836097 1777422642296966200377073)
              ·
                refine ⟨1333066981722724650282805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1777422642296966200377073 1333066981722724650282805)
                ·
                  refine ⟨124975029536505435964013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1333066981722724650282805 124975029536505435964013)
                  ·
                    rfl

theorem cell23_2190492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2, 5].length) (baseStart_2190492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190492 prefixEnd_2190492 := by exact prefixLift 2190492
  have htrace : WordTrace (prefixWord ++ tailWord_2190492) baseStart_2190492 baseEnd_2190492 := by
    simpa [prefixWord, tailWord_2190492, baseEnd_2190492] using wordTrace_append hprefix tailTrace_2190492
  have hstable : (prefixWord ++ tailWord_2190492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190492).length < 2 ^ (prefixWord ++ tailWord_2190492).sum := by decide
  have hdescent : baseEnd_2190492 < baseStart_2190492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190551 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 6]
def baseStart_2190551 : Nat := 118140960795 + 2190551 * 2 ^ 59
def prefixEnd_2190551 : Nat := 4983230072969 + 3 ^ 40 * 2190551 * 2
def baseEnd_2190551 : Nat := 1124805561187164192838345

theorem tailTrace_2190551 : CollatzResearch.WordTrace tailWord_2190551 prefixEnd_2190551 1124805561187164192838345 := by
  unfold tailWord_2190551
  simp only [CollatzResearch.WordTrace]
  refine ⟨79895958687015318170987507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53263972458010212113991671 79895958687015318170987507)
  ·
    refine ⟨119843938030522977256481261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79895958687015318170987507 119843938030522977256481261)
    ·
      refine ⟨44941476761446116471180473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119843938030522977256481261 44941476761446116471180473)
      ·
        refine ⟨33706107571084587353385355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44941476761446116471180473 33706107571084587353385355)
        ·
          refine ⟨50559161356626881030078033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33706107571084587353385355 50559161356626881030078033)
          ·
            refine ⟨37919371017470160772558525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50559161356626881030078033 37919371017470160772558525)
            ·
              refine ⟨14219764131551310289709447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37919371017470160772558525 14219764131551310289709447)
              ·
                refine ⟨21329646197326965434564171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14219764131551310289709447 21329646197326965434564171)
                ·
                  refine ⟨31994469295990448151846257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21329646197326965434564171 31994469295990448151846257)
                  ·
                    refine ⟨23995851971992836113884693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31994469295990448151846257 23995851971992836113884693)
                    ·
                      refine ⟨1124805561187164192838345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23995851971992836113884693 1124805561187164192838345)
                      ·
                        rfl

theorem cell23_2190551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_2190551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190551 prefixEnd_2190551 := by exact prefixLift 2190551
  have htrace : WordTrace (prefixWord ++ tailWord_2190551) baseStart_2190551 baseEnd_2190551 := by
    simpa [prefixWord, tailWord_2190551, baseEnd_2190551] using wordTrace_append hprefix tailTrace_2190551
  have hstable : (prefixWord ++ tailWord_2190551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190551).length < 2 ^ (prefixWord ++ tailWord_2190551).sum := by decide
  have hdescent : baseEnd_2190551 < baseStart_2190551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190585 : List Nat := [1, 2, 1, 3, 1, 1, 4, 3, 2, 3, 2]
def baseStart_2190585 : Nat := 118140960795 + 2190585 * 2 ^ 59
def prefixEnd_2190585 : Nat := 4983230072969 + 3 ^ 40 * 2190585 * 2
def baseEnd_2190585 : Nat := 1124823019529417059813189

theorem tailTrace_2190585 : CollatzResearch.WordTrace tailWord_2190585 prefixEnd_2190585 1124823019529417059813189 := by
  unfold tailWord_2190585
  simp only [CollatzResearch.WordTrace]
  refine ⟨79897198768892141977725209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53264799179261427985150139 79897198768892141977725209)
  ·
    refine ⟨59922899076669106483293907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79897198768892141977725209 59922899076669106483293907)
    ·
      refine ⟨89884348615003659724940861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59922899076669106483293907 89884348615003659724940861)
      ·
        refine ⟨33706630730626372396852823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89884348615003659724940861 33706630730626372396852823)
        ·
          refine ⟨50559946095939558595279235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33706630730626372396852823 50559946095939558595279235)
          ·
            refine ⟨75839919143909337892918853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50559946095939558595279235 75839919143909337892918853)
            ·
              refine ⟨14219984839483000854922285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75839919143909337892918853 14219984839483000854922285)
              ·
                refine ⟨5332494314806125320595857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14219984839483000854922285 5332494314806125320595857)
                ·
                  refine ⟨3999370736104593990446893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5332494314806125320595857 3999370736104593990446893)
                  ·
                    refine ⟨1499764026039222746417585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3999370736104593990446893 1499764026039222746417585)
                    ·
                      refine ⟨1124823019529417059813189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1499764026039222746417585 1124823019529417059813189)
                      ·
                        rfl

theorem cell23_2190585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 3, 2].length) (baseStart_2190585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190585 prefixEnd_2190585 := by exact prefixLift 2190585
  have htrace : WordTrace (prefixWord ++ tailWord_2190585) baseStart_2190585 baseEnd_2190585 := by
    simpa [prefixWord, tailWord_2190585, baseEnd_2190585] using wordTrace_append hprefix tailTrace_2190585
  have hstable : (prefixWord ++ tailWord_2190585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190585).length < 2 ^ (prefixWord ++ tailWord_2190585).sum := by decide
  have hdescent : baseEnd_2190585 < baseStart_2190585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190609 : List Nat := [1, 2, 2, 1, 1, 4, 5, 2, 1, 1, 3]
def baseStart_2190609 : Nat := 118140960795 + 2190609 * 2 ^ 59
def prefixEnd_2190609 : Nat := 4983230072969 + 3 ^ 40 * 2190609 * 2
def baseEnd_2190609 : Nat := 1124835343065124965913079

theorem tailTrace_2190609 : CollatzResearch.WordTrace tailWord_2190609 prefixEnd_2190609 1124835343065124965913079 := by
  unfold tailWord_2190609
  simp only [CollatzResearch.WordTrace]
  refine ⟨79898074120805194076598881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53265382747203462717732587 79898074120805194076598881)
  ·
    refine ⟨59923555590603895557449161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79898074120805194076598881 59923555590603895557449161)
    ·
      refine ⟨44942666692952921668086871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59923555590603895557449161 44942666692952921668086871)
      ·
        refine ⟨67414000039429382502130307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44942666692952921668086871 67414000039429382502130307)
        ·
          refine ⟨101121000059144073753195461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67414000039429382502130307 101121000059144073753195461)
          ·
            refine ⟨18960187511089513828724149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101121000059144073753195461 18960187511089513828724149)
            ·
              refine ⟨1777517579164641921442889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18960187511089513828724149 1777517579164641921442889)
              ·
                refine ⟨1333138184373481441082167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1777517579164641921442889 1333138184373481441082167)
                ·
                  refine ⟨1999707276560222161623251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1333138184373481441082167 1999707276560222161623251)
                  ·
                    refine ⟨2999560914840333242434877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1999707276560222161623251 2999560914840333242434877)
                    ·
                      refine ⟨1124835343065124965913079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2999560914840333242434877 1124835343065124965913079)
                      ·
                        rfl

theorem cell23_2190609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2, 1, 1, 3].length) (baseStart_2190609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190609 prefixEnd_2190609 := by exact prefixLift 2190609
  have htrace : WordTrace (prefixWord ++ tailWord_2190609) baseStart_2190609 baseEnd_2190609 := by
    simpa [prefixWord, tailWord_2190609, baseEnd_2190609] using wordTrace_append hprefix tailTrace_2190609
  have hstable : (prefixWord ++ tailWord_2190609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190609).length < 2 ^ (prefixWord ++ tailWord_2190609).sum := by decide
  have hdescent : baseEnd_2190609 < baseStart_2190609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190628 : List Nat := [2, 3, 1, 3, 1, 1, 1, 3, 1, 1, 6]
def baseStart_2190628 : Nat := 118140960795 + 2190628 * 2 ^ 59
def prefixEnd_2190628 : Nat := 4983230072969 + 3 ^ 40 * 2190628 * 2
def baseEnd_2190628 : Nat := 1124845099197560391575491

theorem tailTrace_2190628 : CollatzResearch.WordTrace tailWord_2190628 prefixEnd_2190628 1124845099197560391575491 := by
  unfold tailWord_2190628
  simp only [CollatzResearch.WordTrace]
  refine ⟨39949383553868180160770269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53265844738490906881027025 39949383553868180160770269)
  ·
    refine ⟨14981018832700567560288851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39949383553868180160770269 14981018832700567560288851)
    ·
      refine ⟨22471528249050851340433277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14981018832700567560288851 22471528249050851340433277)
      ·
        refine ⟨8426823093394069252662479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22471528249050851340433277 8426823093394069252662479)
        ·
          refine ⟨12640234640091103878993719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8426823093394069252662479 12640234640091103878993719)
          ·
            refine ⟨18960351960136655818490579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12640234640091103878993719 18960351960136655818490579)
            ·
              refine ⟨28440527940204983727735869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18960351960136655818490579 28440527940204983727735869)
              ·
                refine ⟨10665197977576868897900951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28440527940204983727735869 10665197977576868897900951)
                ·
                  refine ⟨15997796966365303346851427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10665197977576868897900951 15997796966365303346851427)
                  ·
                    refine ⟨23996695449547955020277141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15997796966365303346851427 23996695449547955020277141)
                    ·
                      refine ⟨1124845099197560391575491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23996695449547955020277141 1124845099197560391575491)
                      ·
                        rfl

theorem cell23_2190628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_2190628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190628 prefixEnd_2190628 := by exact prefixLift 2190628
  have htrace : WordTrace (prefixWord ++ tailWord_2190628) baseStart_2190628 baseEnd_2190628 := by
    simpa [prefixWord, tailWord_2190628, baseEnd_2190628] using wordTrace_append hprefix tailTrace_2190628
  have hstable : (prefixWord ++ tailWord_2190628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190628).length < 2 ^ (prefixWord ++ tailWord_2190628).sum := by decide
  have hdescent : baseEnd_2190628 < baseStart_2190628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190632 : List Nat := [2, 1, 5, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_2190632 : Nat := 118140960795 + 2190632 * 2 ^ 59
def prefixEnd_2190632 : Nat := 4983230072969 + 3 ^ 40 * 2190632 * 2
def baseEnd_2190632 : Nat := 1124847153120178375925473

theorem tailTrace_2190632 : CollatzResearch.WordTrace tailWord_2190632 prefixEnd_2190632 1124847153120178375925473 := by
  unfold tailWord_2190632
  simp only [CollatzResearch.WordTrace]
  refine ⟨39949456499860934502343075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53265941999814579336457433 39949456499860934502343075)
  ·
    refine ⟨59924184749791401753514613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39949456499860934502343075 59924184749791401753514613)
    ·
      refine ⟨5617892320292943914391995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59924184749791401753514613 5617892320292943914391995)
      ·
        refine ⟨8426838480439415871587993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5617892320292943914391995 8426838480439415871587993)
        ·
          refine ⟨6320128860329561903690995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8426838480439415871587993 6320128860329561903690995)
          ·
            refine ⟨9480193290494342855536493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6320128860329561903690995 9480193290494342855536493)
            ·
              refine ⟨3555072483935378570826185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9480193290494342855536493 3555072483935378570826185)
              ·
                refine ⟨2666304362951533928119639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3555072483935378570826185 2666304362951533928119639)
                ·
                  refine ⟨3999456544427300892179459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2666304362951533928119639 3999456544427300892179459)
                  ·
                    refine ⟨5999184816640951338269189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3999456544427300892179459 5999184816640951338269189)
                    ·
                      refine ⟨1124847153120178375925473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5999184816640951338269189 1124847153120178375925473)
                      ·
                        rfl

theorem cell23_2190632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_2190632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190632 prefixEnd_2190632 := by exact prefixLift 2190632
  have htrace : WordTrace (prefixWord ++ tailWord_2190632) baseStart_2190632 baseEnd_2190632 := by
    simpa [prefixWord, tailWord_2190632, baseEnd_2190632] using wordTrace_append hprefix tailTrace_2190632
  have hstable : (prefixWord ++ tailWord_2190632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190632).length < 2 ^ (prefixWord ++ tailWord_2190632).sum := by decide
  have hdescent : baseEnd_2190632 < baseStart_2190632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190645 : List Nat := [1, 3, 3, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_2190645 : Nat := 118140960795 + 2190645 * 2 ^ 59
def prefixEnd_2190645 : Nat := 4983230072969 + 3 ^ 40 * 2190645 * 2
def baseEnd_2190645 : Nat := 1124853828368686825062913

theorem tailTrace_2190645 : CollatzResearch.WordTrace tailWord_2190645 prefixEnd_2190645 1124853828368686825062913 := by
  unfold tailWord_2190645
  simp only [CollatzResearch.WordTrace]
  refine ⟨79899387148674772224909389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53266258099116514816606259 79899387148674772224909389)
  ·
    refine ⟨29962270180753039584341021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79899387148674772224909389 29962270180753039584341021)
    ·
      refine ⟨11235851317782389844127883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29962270180753039584341021 11235851317782389844127883)
      ·
        refine ⟨16853776976673584766191825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11235851317782389844127883 16853776976673584766191825)
        ·
          refine ⟨12640332732505188574643869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16853776976673584766191825 12640332732505188574643869)
          ·
            refine ⟨4740124774689445715491451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12640332732505188574643869 4740124774689445715491451)
            ·
              refine ⟨7110187162034168573237177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4740124774689445715491451 7110187162034168573237177)
              ·
                refine ⟨5332640371525626429927883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7110187162034168573237177 5332640371525626429927883)
                ·
                  refine ⟨7998960557288439644891825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5332640371525626429927883 7998960557288439644891825)
                  ·
                    refine ⟨5999220417966329733668869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7998960557288439644891825 5999220417966329733668869)
                    ·
                      refine ⟨1124853828368686825062913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5999220417966329733668869 1124853828368686825062913)
                      ·
                        rfl

theorem cell23_2190645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_2190645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190645 prefixEnd_2190645 := by exact prefixLift 2190645
  have htrace : WordTrace (prefixWord ++ tailWord_2190645) baseStart_2190645 baseEnd_2190645 := by
    simpa [prefixWord, tailWord_2190645, baseEnd_2190645] using wordTrace_append hprefix tailTrace_2190645
  have hstable : (prefixWord ++ tailWord_2190645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190645).length < 2 ^ (prefixWord ++ tailWord_2190645).sum := by decide
  have hdescent : baseEnd_2190645 < baseStart_2190645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190646 : List Nat := [5, 1, 2, 3, 1, 1, 3, 1, 1, 5]
def baseStart_2190646 : Nat := 118140960795 + 2190646 * 2 ^ 59
def prefixEnd_2190646 : Nat := 4983230072969 + 3 ^ 40 * 2190646 * 2
def baseEnd_2190646 : Nat := 374951447283113773716803

theorem tailTrace_2190646 : CollatzResearch.WordTrace tailWord_2190646 prefixEnd_2190646 374951447283113773716803 := by
  unfold tailWord_2190646
  simp only [CollatzResearch.WordTrace]
  refine ⟨4993713976354446837230987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53266282414447432930463861 4993713976354446837230987)
  ·
    refine ⟨7490570964531670255846481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4993713976354446837230987 7490570964531670255846481)
    ·
      refine ⟨5617928223398752691884861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7490570964531670255846481 5617928223398752691884861)
      ·
        refine ⟨2106723083774532259456823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5617928223398752691884861 2106723083774532259456823)
        ·
          refine ⟨3160084625661798389185235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2106723083774532259456823 3160084625661798389185235)
          ·
            refine ⟨4740126938492697583777853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3160084625661798389185235 4740126938492697583777853)
            ·
              refine ⟨1777547601934761593916695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4740126938492697583777853 1777547601934761593916695)
              ·
                refine ⟨2666321402902142390875043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1777547601934761593916695 2666321402902142390875043)
                ·
                  refine ⟨3999482104353213586312565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2666321402902142390875043 3999482104353213586312565)
                  ·
                    refine ⟨374951447283113773716803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3999482104353213586312565 374951447283113773716803)
                    ·
                      rfl

theorem cell23_2190646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_2190646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190646 prefixEnd_2190646 := by exact prefixLift 2190646
  have htrace : WordTrace (prefixWord ++ tailWord_2190646) baseStart_2190646 baseEnd_2190646 := by
    simpa [prefixWord, tailWord_2190646, baseEnd_2190646] using wordTrace_append hprefix tailTrace_2190646
  have hstable : (prefixWord ++ tailWord_2190646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190646).length < 2 ^ (prefixWord ++ tailWord_2190646).sum := by decide
  have hdescent : baseEnd_2190646 < baseStart_2190646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190649 : List Nat := [1, 2, 1, 6, 2, 1, 3, 1, 1, 1, 4]
def baseStart_2190649 : Nat := 118140960795 + 2190649 * 2 ^ 59
def prefixEnd_2190649 : Nat := 4983230072969 + 3 ^ 40 * 2190649 * 2
def baseEnd_2190649 : Nat := 1124855882291304809412895

theorem tailTrace_2190649 : CollatzResearch.WordTrace tailWord_2190649 prefixEnd_2190649 1124855882291304809412895 := by
  unfold tailWord_2190649
  simp only [CollatzResearch.WordTrace]
  refine ⟨79899533040660280908055001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53266355360440187272036667 79899533040660280908055001)
  ·
    refine ⟨59924649780495210681041251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79899533040660280908055001 59924649780495210681041251)
    ·
      refine ⟨89886974670742816021561877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59924649780495210681041251 89886974670742816021561877)
      ·
        refine ⟨4213451937691069501010713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 89886974670742816021561877 4213451937691069501010713)
        ·
          refine ⟨3160088953268302125758035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4213451937691069501010713 3160088953268302125758035)
          ·
            refine ⟨4740133429902453188637053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3160088953268302125758035 4740133429902453188637053)
            ·
              refine ⟨1777550036213419945738895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4740133429902453188637053 1777550036213419945738895)
              ·
                refine ⟨2666325054320129918608343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1777550036213419945738895 2666325054320129918608343)
                ·
                  refine ⟨3999487581480194877912515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2666325054320129918608343 3999487581480194877912515)
                  ·
                    refine ⟨5999231372220292316868773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3999487581480194877912515 5999231372220292316868773)
                    ·
                      refine ⟨1124855882291304809412895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5999231372220292316868773 1124855882291304809412895)
                      ·
                        rfl

theorem cell23_2190649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_2190649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190649 prefixEnd_2190649 := by exact prefixLift 2190649
  have htrace : WordTrace (prefixWord ++ tailWord_2190649) baseStart_2190649 baseEnd_2190649 := by
    simpa [prefixWord, tailWord_2190649, baseEnd_2190649] using wordTrace_append hprefix tailTrace_2190649
  have hstable : (prefixWord ++ tailWord_2190649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190649).length < 2 ^ (prefixWord ++ tailWord_2190649).sum := by decide
  have hdescent : baseEnd_2190649 < baseStart_2190649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190665 : List Nat := [1, 2, 1, 1, 2, 3, 2, 3, 4, 1, 3]
def baseStart_2190665 : Nat := 118140960795 + 2190665 * 2 ^ 59
def prefixEnd_2190665 : Nat := 4983230072969 + 3 ^ 40 * 2190665 * 2
def baseEnd_2190665 : Nat := 1124864097981776746812821

theorem tailTrace_2190665 : CollatzResearch.WordTrace tailWord_2190665 prefixEnd_2190665 1124864097981776746812821 := by
  unfold tailWord_2190665
  simp only [CollatzResearch.WordTrace]
  refine ⟨79900116608602315640637449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53266744405734877093758299 79900116608602315640637449)
  ·
    refine ⟨59925087456451736730478087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79900116608602315640637449 59925087456451736730478087)
    ·
      refine ⟨89887631184677605095717131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59925087456451736730478087 89887631184677605095717131)
      ·
        refine ⟨134831446777016407643575697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89887631184677605095717131 134831446777016407643575697)
        ·
          refine ⟨101123585082762305732681773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134831446777016407643575697 101123585082762305732681773)
          ·
            refine ⟨37921344406035864649755665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101123585082762305732681773 37921344406035864649755665)
            ·
              refine ⟨28441008304526898487316749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37921344406035864649755665 28441008304526898487316749)
              ·
                refine ⟨10665378114197586932743781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28441008304526898487316749 10665378114197586932743781)
                ·
                  refine ⟨1999758396412047549889459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10665378114197586932743781 1999758396412047549889459)
                  ·
                    refine ⟨2999637594618071324834189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1999758396412047549889459 2999637594618071324834189)
                    ·
                      refine ⟨1124864097981776746812821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2999637594618071324834189 1124864097981776746812821)
                      ·
                        rfl

theorem cell23_2190665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4, 1, 3].length) (baseStart_2190665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190665 prefixEnd_2190665 := by exact prefixLift 2190665
  have htrace : WordTrace (prefixWord ++ tailWord_2190665) baseStart_2190665 baseEnd_2190665 := by
    simpa [prefixWord, tailWord_2190665, baseEnd_2190665] using wordTrace_append hprefix tailTrace_2190665
  have hstable : (prefixWord ++ tailWord_2190665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190665).length < 2 ^ (prefixWord ++ tailWord_2190665).sum := by decide
  have hdescent : baseEnd_2190665 < baseStart_2190665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190668 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 2, 7]
def baseStart_2190668 : Nat := 118140960795 + 2190668 * 2 ^ 59
def prefixEnd_2190668 : Nat := 4983230072969 + 3 ^ 40 * 2190668 * 2
def baseEnd_2190668 : Nat := 374955212807913411691769

theorem tailTrace_2190668 : CollatzResearch.WordTrace tailWord_2190668 prefixEnd_2190668 374955212807913411691769 := by
  unfold tailWord_2190668
  simp only [CollatzResearch.WordTrace]
  refine ⟨39950113013795723576498329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53266817351727631435331105 39950113013795723576498329)
  ·
    refine ⟨29962584760346792682373747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39950113013795723576498329 29962584760346792682373747)
    ·
      refine ⟨44943877140520189023560621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29962584760346792682373747 44943877140520189023560621)
      ·
        refine ⟨16853953927695070883835233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44943877140520189023560621 16853953927695070883835233)
        ·
          refine ⟨12640465445771303162876425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16853953927695070883835233 12640465445771303162876425)
          ·
            refine ⟨9480349084328477372157319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12640465445771303162876425 9480349084328477372157319)
            ·
              refine ⟨14220523626492716058235979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9480349084328477372157319 14220523626492716058235979)
              ·
                refine ⟨21330785439739074087353969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14220523626492716058235979 21330785439739074087353969)
                ·
                  refine ⟨15998089079804305565515477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21330785439739074087353969 15998089079804305565515477)
                  ·
                    refine ⟨374955212807913411691769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15998089079804305565515477 374955212807913411691769)
                    ·
                      rfl

theorem cell23_2190668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 2, 7].length) (baseStart_2190668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190668 prefixEnd_2190668 := by exact prefixLift 2190668
  have htrace : WordTrace (prefixWord ++ tailWord_2190668) baseStart_2190668 baseEnd_2190668 := by
    simpa [prefixWord, tailWord_2190668, baseEnd_2190668] using wordTrace_append hprefix tailTrace_2190668
  have hstable : (prefixWord ++ tailWord_2190668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190668).length < 2 ^ (prefixWord ++ tailWord_2190668).sum := by decide
  have hdescent : baseEnd_2190668 < baseStart_2190668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190675 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 5, 3, 2]
def baseStart_2190675 : Nat := 118140960795 + 2190675 * 2 ^ 59
def prefixEnd_2190675 : Nat := 4983230072969 + 3 ^ 40 * 2190675 * 2
def baseEnd_2190675 : Nat := 1124869232788321707687775

theorem tailTrace_2190675 : CollatzResearch.WordTrace tailWord_2190675 prefixEnd_2190675 1124869232788321707687775 := by
  unfold tailWord_2190675
  simp only [CollatzResearch.WordTrace]
  refine ⟨79900481338566087348501479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53266987559044058232334319 79900481338566087348501479)
  ·
    refine ⟨119850722007849131022752219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79900481338566087348501479 119850722007849131022752219)
    ·
      refine ⟨179776083011773696534128329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119850722007849131022752219 179776083011773696534128329)
      ·
        refine ⟨134832062258830272400596247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179776083011773696534128329 134832062258830272400596247)
        ·
          refine ⟨202248093388245408600894371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134832062258830272400596247 202248093388245408600894371)
          ·
            refine ⟨303372140082368112901341557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202248093388245408600894371 303372140082368112901341557)
            ·
              refine ⟨28441138132722010584500771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 303372140082368112901341557 28441138132722010584500771)
              ·
                refine ⟨42661707199083015876751157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28441138132722010584500771 42661707199083015876751157)
                ·
                  refine ⟨3999535049914032738445421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42661707199083015876751157 3999535049914032738445421)
                  ·
                    refine ⟨1499825643717762276917033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3999535049914032738445421 1499825643717762276917033)
                    ·
                      refine ⟨1124869232788321707687775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1499825643717762276917033 1124869232788321707687775)
                      ·
                        rfl

theorem cell23_2190675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 3, 2].length) (baseStart_2190675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190675 prefixEnd_2190675 := by exact prefixLift 2190675
  have htrace : WordTrace (prefixWord ++ tailWord_2190675) baseStart_2190675 baseEnd_2190675 := by
    simpa [prefixWord, tailWord_2190675, baseEnd_2190675] using wordTrace_append hprefix tailTrace_2190675
  have hstable : (prefixWord ++ tailWord_2190675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190675).length < 2 ^ (prefixWord ++ tailWord_2190675).sum := by decide
  have hdescent : baseEnd_2190675 < baseStart_2190675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190682 : List Nat := [3, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3]
def baseStart_2190682 : Nat := 118140960795 + 2190682 * 2 ^ 59
def prefixEnd_2190682 : Nat := 4983230072969 + 3 ^ 40 * 2190682 * 2
def baseEnd_2190682 : Nat := 1124872827152903180300243

theorem tailTrace_2190682 : CollatzResearch.WordTrace tailWord_2190682 prefixEnd_2190682 1124872827152903180300243 := by
  unfold tailWord_2190682
  simp only [CollatzResearch.WordTrace]
  refine ⟨19975184162385181886001575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53267157766360485029337533 19975184162385181886001575)
  ·
    refine ⟨29962776243577772829002363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19975184162385181886001575 29962776243577772829002363)
    ·
      refine ⟨44944164365366659243503545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29962776243577772829002363 44944164365366659243503545)
      ·
        refine ⟨33708123274024994432627659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44944164365366659243503545 33708123274024994432627659)
        ·
          refine ⟨50562184911037491648941489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33708123274024994432627659 50562184911037491648941489)
          ·
            refine ⟨37921638683278118736706117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50562184911037491648941489 37921638683278118736706117)
            ·
              refine ⟨7110307253114647263132397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37921638683278118736706117 7110307253114647263132397)
              ·
                refine ⟨2666365219917992723674649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7110307253114647263132397 2666365219917992723674649)
                ·
                  refine ⟨1999773914938494542755987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2666365219917992723674649 1999773914938494542755987)
                  ·
                    refine ⟨2999660872407741814133981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1999773914938494542755987 2999660872407741814133981)
                    ·
                      refine ⟨1124872827152903180300243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2999660872407741814133981 1124872827152903180300243)
                      ·
                        rfl

theorem cell23_2190682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_2190682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190682 prefixEnd_2190682 := by exact prefixLift 2190682
  have htrace : WordTrace (prefixWord ++ tailWord_2190682) baseStart_2190682 baseEnd_2190682 := by
    simpa [prefixWord, tailWord_2190682, baseEnd_2190682] using wordTrace_append hprefix tailTrace_2190682
  have hstable : (prefixWord ++ tailWord_2190682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190682).length < 2 ^ (prefixWord ++ tailWord_2190682).sum := by decide
  have hdescent : baseEnd_2190682 < baseStart_2190682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190692 : List Nat := [2, 3, 1, 1, 3, 2, 2, 1, 3, 3, 2]
def baseStart_2190692 : Nat := 118140960795 + 2190692 * 2 ^ 59
def prefixEnd_2190692 : Nat := 4983230072969 + 3 ^ 40 * 2190692 * 2
def baseEnd_2190692 : Nat := 1124877961959448141175197

theorem tailTrace_2190692 : CollatzResearch.WordTrace tailWord_2190692 prefixEnd_2190692 1124877961959448141175197 := by
  unfold tailWord_2190692
  simp only [CollatzResearch.WordTrace]
  refine ⟨39950550689752249625935165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53267400919669666167913553 39950550689752249625935165)
  ·
    refine ⟨14981456508657093609725687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39950550689752249625935165 14981456508657093609725687)
    ·
      refine ⟨22472184762985640414588531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14981456508657093609725687 22472184762985640414588531)
      ·
        refine ⟨33708277144478460621882797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22472184762985640414588531 33708277144478460621882797)
        ·
          refine ⟨12640603929179422733206049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33708277144478460621882797 12640603929179422733206049)
          ·
            refine ⟨9480452946884567049904537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12640603929179422733206049 9480452946884567049904537)
            ·
              refine ⟨7110339710163425287428403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9480452946884567049904537 7110339710163425287428403)
              ·
                refine ⟨10665509565245137931142605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7110339710163425287428403 10665509565245137931142605)
                ·
                  refine ⟨3999566086966926724178477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10665509565245137931142605 3999566086966926724178477)
                  ·
                    refine ⟨1499837282612597521566929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3999566086966926724178477 1499837282612597521566929)
                    ·
                      refine ⟨1124877961959448141175197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1499837282612597521566929 1124877961959448141175197)
                      ·
                        rfl

theorem cell23_2190692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 3, 3, 2].length) (baseStart_2190692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190692 prefixEnd_2190692 := by exact prefixLift 2190692
  have htrace : WordTrace (prefixWord ++ tailWord_2190692) baseStart_2190692 baseEnd_2190692 := by
    simpa [prefixWord, tailWord_2190692, baseEnd_2190692] using wordTrace_append hprefix tailTrace_2190692
  have hstable : (prefixWord ++ tailWord_2190692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190692).length < 2 ^ (prefixWord ++ tailWord_2190692).sum := by decide
  have hdescent : baseEnd_2190692 < baseStart_2190692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190775 : List Nat := [1, 1, 3, 1, 3, 2, 3, 2, 2, 5]
def baseStart_2190775 : Nat := 118140960795 + 2190775 * 2 ^ 59
def prefixEnd_2190775 : Nat := 4983230072969 + 3 ^ 40 * 2190775 * 2
def baseEnd_2190775 : Nat := 374973526951257105479105

theorem tailTrace_2190775 : CollatzResearch.WordTrace tailWord_2190775 prefixEnd_2190775 374973526951257105479105 := by
  unfold tailWord_2190775
  simp only [CollatzResearch.WordTrace]
  refine ⟨79904128638203804427141779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53269419092135869618094519 79904128638203804427141779)
  ·
    refine ⟨119856192957305706640712669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79904128638203804427141779 119856192957305706640712669)
    ·
      refine ⟨44946072358989639990267251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119856192957305706640712669 44946072358989639990267251)
      ·
        refine ⟨67419108538484459985400877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44946072358989639990267251 67419108538484459985400877)
        ·
          refine ⟨25282165701931672494525329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67419108538484459985400877 25282165701931672494525329)
          ·
            refine ⟨18961624276448754370893997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25282165701931672494525329 18961624276448754370893997)
            ·
              refine ⟨7110609103668282889085249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18961624276448754370893997 7110609103668282889085249)
              ·
                refine ⟨5332956827751212166813937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7110609103668282889085249 5332956827751212166813937)
                ·
                  refine ⟨3999717620813409125110453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5332956827751212166813937 3999717620813409125110453)
                  ·
                    refine ⟨374973526951257105479105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3999717620813409125110453 374973526951257105479105)
                    ·
                      rfl

theorem cell23_2190775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 5].length) (baseStart_2190775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190775 prefixEnd_2190775 := by exact prefixLift 2190775
  have htrace : WordTrace (prefixWord ++ tailWord_2190775) baseStart_2190775 baseEnd_2190775 := by
    simpa [prefixWord, tailWord_2190775, baseEnd_2190775] using wordTrace_append hprefix tailTrace_2190775
  have hstable : (prefixWord ++ tailWord_2190775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190775).length < 2 ^ (prefixWord ++ tailWord_2190775).sum := by decide
  have hdescent : baseEnd_2190775 < baseStart_2190775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190778 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8]
def baseStart_2190778 : Nat := 118140960795 + 2190778 * 2 ^ 59
def prefixEnd_2190778 : Nat := 4983230072969 + 3 ^ 40 * 2190778 * 2
def baseEnd_2190778 : Nat := 1124922121295734804699801

theorem tailTrace_2190778 : CollatzResearch.WordTrace tailWord_2190778 prefixEnd_2190778 1124922121295734804699801 := by
  unfold tailWord_2190778
  simp only [CollatzResearch.WordTrace]
  refine ⟨19976059514298233984875247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53269492038128623959667325 19976059514298233984875247)
  ·
    refine ⟨29964089271447350977312871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19976059514298233984875247 29964089271447350977312871)
    ·
      refine ⟨44946133907171026465969307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29964089271447350977312871 44946133907171026465969307)
      ·
        refine ⟨67419200860756539698953961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44946133907171026465969307 67419200860756539698953961)
        ·
          refine ⟨50564400645567404774215471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67419200860756539698953961 50564400645567404774215471)
          ·
            refine ⟨75846600968351107161323207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50564400645567404774215471 75846600968351107161323207)
            ·
              refine ⟨113769901452526660741984811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75846600968351107161323207 113769901452526660741984811)
              ·
                refine ⟨170654852178789991112977217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113769901452526660741984811 170654852178789991112977217)
                ·
                  refine ⟨127991139134092493334732913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170654852178789991112977217 127991139134092493334732913)
                  ·
                    refine ⟨95993354350569370001049685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 127991139134092493334732913 95993354350569370001049685)
                    ·
                      refine ⟨1124922121295734804699801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 95993354350569370001049685 1124922121295734804699801)
                      ·
                        rfl

theorem cell23_2190778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_2190778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190778 prefixEnd_2190778 := by exact prefixLift 2190778
  have htrace : WordTrace (prefixWord ++ tailWord_2190778) baseStart_2190778 baseEnd_2190778 := by
    simpa [prefixWord, tailWord_2190778, baseEnd_2190778] using wordTrace_append hprefix tailTrace_2190778
  have hstable : (prefixWord ++ tailWord_2190778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190778).length < 2 ^ (prefixWord ++ tailWord_2190778).sum := by decide
  have hdescent : baseEnd_2190778 < baseStart_2190778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190782 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2]
def baseStart_2190782 : Nat := 118140960795 + 2190782 * 2 ^ 59
def prefixEnd_2190782 : Nat := 4983230072969 + 3 ^ 40 * 2190782 * 2
def baseEnd_2190782 : Nat := 1124924175218352789049783

theorem tailTrace_2190782 : CollatzResearch.WordTrace tailWord_2190782 prefixEnd_2190782 1124924175218352789049783 := by
  unfold tailWord_2190782
  simp only [CollatzResearch.WordTrace]
  refine ⟨9988047993647305577830825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53269589299452296415097733 9988047993647305577830825)
  ·
    refine ⟨7491035995235479183373119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9988047993647305577830825 7491035995235479183373119)
    ·
      refine ⟨11236553992853218775059679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7491035995235479183373119 11236553992853218775059679)
      ·
        refine ⟨16854830989279828162589519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11236553992853218775059679 16854830989279828162589519)
        ·
          refine ⟨25282246483919742243884279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16854830989279828162589519 25282246483919742243884279)
          ·
            refine ⟨37923369725879613365826419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25282246483919742243884279 37923369725879613365826419)
            ·
              refine ⟨56885054588819420048739629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37923369725879613365826419 56885054588819420048739629)
              ·
                refine ⟨21331895470807282518277361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56885054588819420048739629 21331895470807282518277361)
                ·
                  refine ⟨15998921603105461888708021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21331895470807282518277361 15998921603105461888708021)
                  ·
                    refine ⟨1499898900291137052066377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15998921603105461888708021 1499898900291137052066377)
                    ·
                      refine ⟨1124924175218352789049783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1499898900291137052066377 1124924175218352789049783)
                      ·
                        rfl

theorem cell23_2190782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_2190782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190782 prefixEnd_2190782 := by exact prefixLift 2190782
  have htrace : WordTrace (prefixWord ++ tailWord_2190782) baseStart_2190782 baseEnd_2190782 := by
    simpa [prefixWord, tailWord_2190782, baseEnd_2190782] using wordTrace_append hprefix tailTrace_2190782
  have hstable : (prefixWord ++ tailWord_2190782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190782).length < 2 ^ (prefixWord ++ tailWord_2190782).sum := by decide
  have hdescent : baseEnd_2190782 < baseStart_2190782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190832 : List Nat := [2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 3]
def baseStart_2190832 : Nat := 118140960795 + 2190832 * 2 ^ 59
def prefixEnd_2190832 : Nat := 4983230072969 + 3 ^ 40 * 2190832 * 2
def baseEnd_2190832 : Nat := 1124949849251077593424553

theorem tailTrace_2190832 : CollatzResearch.WordTrace tailWord_2190832 prefixEnd_2190832 1124949849251077593424553 := by
  unfold tailWord_2190832
  simp only [CollatzResearch.WordTrace]
  refine ⟨39953103799498651580983375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53270805065998202107977833 39953103799498651580983375)
  ·
    refine ⟨59929655699247977371475063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39953103799498651580983375 59929655699247977371475063)
    ·
      refine ⟨89894483548871966057212595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59929655699247977371475063 89894483548871966057212595)
      ·
        refine ⟨134841725323307949085818893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89894483548871966057212595 134841725323307949085818893)
        ·
          refine ⟨50565646996240480907182085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134841725323307949085818893 50565646996240480907182085)
          ·
            refine ⟨9481058811795090170096641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50565646996240480907182085 9481058811795090170096641)
            ·
              refine ⟨7110794108846317627572481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9481058811795090170096641 7110794108846317627572481)
              ·
                refine ⟨5333095581634738220679361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7110794108846317627572481 5333095581634738220679361)
                ·
                  refine ⟨3999821686226053665509521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5333095581634738220679361 3999821686226053665509521)
                  ·
                    refine ⟨2999866264669540249132141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3999821686226053665509521 2999866264669540249132141)
                    ·
                      refine ⟨1124949849251077593424553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2999866264669540249132141 1124949849251077593424553)
                      ·
                        rfl

theorem cell23_2190832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 3].length) (baseStart_2190832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190832 prefixEnd_2190832 := by exact prefixLift 2190832
  have htrace : WordTrace (prefixWord ++ tailWord_2190832) baseStart_2190832 baseEnd_2190832 := by
    simpa [prefixWord, tailWord_2190832, baseEnd_2190832] using wordTrace_append hprefix tailTrace_2190832
  have hstable : (prefixWord ++ tailWord_2190832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190832).length < 2 ^ (prefixWord ++ tailWord_2190832).sum := by decide
  have hdescent : baseEnd_2190832 < baseStart_2190832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190865 : List Nat := [1, 2, 2, 1, 1, 2, 3, 3, 3, 5]
def baseStart_2190865 : Nat := 118140960795 + 2190865 * 2 ^ 59
def prefixEnd_2190865 : Nat := 4983230072969 + 3 ^ 40 * 2190865 * 2
def baseEnd_2190865 : Nat := 374988931370891988103967

theorem tailTrace_2190865 : CollatzResearch.WordTrace tailWord_2190865 prefixEnd_2190865 374988931370891988103967 := by
  unfold tailWord_2190865
  simp only [CollatzResearch.WordTrace]
  refine ⟨79907411207877749797918049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53271607471918499865278699 79907411207877749797918049)
  ·
    refine ⟨59930558405908312348438537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79907411207877749797918049 59930558405908312348438537)
    ·
      refine ⟨44947918804431234261328903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59930558405908312348438537 44947918804431234261328903)
      ·
        refine ⟨67421878206646851391993355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44947918804431234261328903 67421878206646851391993355)
        ·
          refine ⟨101132817309970277087990033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67421878206646851391993355 101132817309970277087990033)
          ·
            refine ⟨75849612982477707815992525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101132817309970277087990033 75849612982477707815992525)
            ·
              refine ⟨28443604868429140430997197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75849612982477707815992525 28443604868429140430997197)
              ·
                refine ⟨10666351825660927661623949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28443604868429140430997197 10666351825660927661623949)
                ·
                  refine ⟨3999881934622847873108981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10666351825660927661623949 3999881934622847873108981)
                  ·
                    refine ⟨374988931370891988103967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3999881934622847873108981 374988931370891988103967)
                    ·
                      rfl

theorem cell23_2190865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 5].length) (baseStart_2190865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190865 prefixEnd_2190865 := by exact prefixLift 2190865
  have htrace : WordTrace (prefixWord ++ tailWord_2190865) baseStart_2190865 baseEnd_2190865 := by
    simpa [prefixWord, tailWord_2190865, baseEnd_2190865] using wordTrace_append hprefix tailTrace_2190865
  have hstable : (prefixWord ++ tailWord_2190865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190865).length < 2 ^ (prefixWord ++ tailWord_2190865).sum := by decide
  have hdescent : baseEnd_2190865 < baseStart_2190865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2190932 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_2190932 : Nat := 118140960795 + 2190932 * 2 ^ 59
def prefixEnd_2190932 : Nat := 4983230072969 + 3 ^ 40 * 2190932 * 2
def baseEnd_2190932 : Nat := 1125001197316527202174093

theorem tailTrace_2190932 : CollatzResearch.WordTrace tailWord_2190932 prefixEnd_2190932 1125001197316527202174093 := by
  unfold tailWord_2190932
  simp only [CollatzResearch.WordTrace]
  refine ⟨39954927449317510120303525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53273236599090013493738033 39954927449317510120303525)
  ·
    refine ⟨7491548896747033147556911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39954927449317510120303525 7491548896747033147556911)
    ·
      refine ⟨11237323345120549721335367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7491548896747033147556911 11237323345120549721335367)
      ·
        refine ⟨16855985017680824582003051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11237323345120549721335367 16855985017680824582003051)
        ·
          refine ⟨25283977526521236873004577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16855985017680824582003051 25283977526521236873004577)
          ·
            refine ⟨18962983144890927654753433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25283977526521236873004577 18962983144890927654753433)
            ·
              refine ⟨14222237358668195741065075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18962983144890927654753433 14222237358668195741065075)
              ·
                refine ⟨21333356038002293611597613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14222237358668195741065075 21333356038002293611597613)
                ·
                  refine ⟨8000008514250860104349105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21333356038002293611597613 8000008514250860104349105)
                  ·
                    refine ⟨6000006385688145078261829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8000008514250860104349105 6000006385688145078261829)
                    ·
                      refine ⟨1125001197316527202174093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6000006385688145078261829 1125001197316527202174093)
                      ·
                        rfl

theorem cell23_2190932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_2190932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2190932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2190932 prefixEnd_2190932 := by exact prefixLift 2190932
  have htrace : WordTrace (prefixWord ++ tailWord_2190932) baseStart_2190932 baseEnd_2190932 := by
    simpa [prefixWord, tailWord_2190932, baseEnd_2190932] using wordTrace_append hprefix tailTrace_2190932
  have hstable : (prefixWord ++ tailWord_2190932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2190932).length < 2 ^ (prefixWord ++ tailWord_2190932).sum := by decide
  have hdescent : baseEnd_2190932 < baseStart_2190932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2190932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191004 : List Nat := [2, 2, 3, 2, 4, 1, 2, 2, 1, 2, 2]
def baseStart_2191004 : Nat := 118140960795 + 2191004 * 2 ^ 59
def prefixEnd_2191004 : Nat := 4983230072969 + 3 ^ 40 * 2191004 * 2
def baseEnd_2191004 : Nat := 1125038167923650920473763

theorem tailTrace_2191004 : CollatzResearch.WordTrace tailWord_2191004 prefixEnd_2191004 1125038167923650920473763 := by
  unfold tailWord_2191004
  simp only [CollatzResearch.WordTrace]
  refine ⟨39956240477187088268614033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53274987302916117691485377 39956240477187088268614033)
  ·
    refine ⟨29967180357890316201460525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39956240477187088268614033 29967180357890316201460525)
    ·
      refine ⟨11237692634208868575547697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29967180357890316201460525 11237692634208868575547697)
      ·
        refine ⟨8428269475656651431660773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11237692634208868575547697 8428269475656651431660773)
        ·
          refine ⟨1580300526685622143436395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8428269475656651431660773 1580300526685622143436395)
          ·
            refine ⟨2370450790028433215154593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1580300526685622143436395 2370450790028433215154593)
            ·
              refine ⟨1777838092521324911365945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2370450790028433215154593 1777838092521324911365945)
              ·
                refine ⟨1333378569390993683524459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1777838092521324911365945 1333378569390993683524459)
                ·
                  refine ⟨2000067854086490525286689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1333378569390993683524459 2000067854086490525286689)
                  ·
                    refine ⟨1500050890564867893965017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2000067854086490525286689 1500050890564867893965017)
                    ·
                      refine ⟨1125038167923650920473763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1500050890564867893965017 1125038167923650920473763)
                      ·
                        rfl

theorem cell23_2191004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_2191004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191004 prefixEnd_2191004 := by exact prefixLift 2191004
  have htrace : WordTrace (prefixWord ++ tailWord_2191004) baseStart_2191004 baseEnd_2191004 := by
    simpa [prefixWord, tailWord_2191004, baseEnd_2191004] using wordTrace_append hprefix tailTrace_2191004
  have hstable : (prefixWord ++ tailWord_2191004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191004).length < 2 ^ (prefixWord ++ tailWord_2191004).sum := by decide
  have hdescent : baseEnd_2191004 < baseStart_2191004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191060 : List Nat := [2, 4, 1, 3, 1, 1, 3, 2, 2, 2, 2]
def baseStart_2191060 : Nat := 118140960795 + 2191060 * 2 ^ 59
def prefixEnd_2191060 : Nat := 4983230072969 + 3 ^ 40 * 2191060 * 2
def baseEnd_2191060 : Nat := 1125066922840302701373505

theorem tailTrace_2191060 : CollatzResearch.WordTrace tailWord_2191060 prefixEnd_2191060 1125066922840302701373505 := by
  unfold tailWord_2191060
  simp only [CollatzResearch.WordTrace]
  refine ⟨39957261721085649050633317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53276348961447532067511089 39957261721085649050633317)
  ·
    refine ⟨7491986572703559196993747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39957261721085649050633317 7491986572703559196993747)
    ·
      refine ⟨11237979859055338795490621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7491986572703559196993747 11237979859055338795490621)
      ·
        refine ⟨4214242447145752048308983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11237979859055338795490621 4214242447145752048308983)
        ·
          refine ⟨6321363670718628072463475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4214242447145752048308983 6321363670718628072463475)
          ·
            refine ⟨9482045506077942108695213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6321363670718628072463475 9482045506077942108695213)
            ·
              refine ⟨3555767064779228290760705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9482045506077942108695213 3555767064779228290760705)
              ·
                refine ⟨2666825298584421218070529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3555767064779228290760705 2666825298584421218070529)
                ·
                  refine ⟨2000118973938315913552897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2666825298584421218070529 2000118973938315913552897)
                  ·
                    refine ⟨1500089230453736935164673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2000118973938315913552897 1500089230453736935164673)
                    ·
                      refine ⟨1125066922840302701373505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1500089230453736935164673 1125066922840302701373505)
                      ·
                        rfl

theorem cell23_2191060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_2191060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191060 prefixEnd_2191060 := by exact prefixLift 2191060
  have htrace : WordTrace (prefixWord ++ tailWord_2191060) baseStart_2191060 baseEnd_2191060 := by
    simpa [prefixWord, tailWord_2191060, baseEnd_2191060] using wordTrace_append hprefix tailTrace_2191060
  have hstable : (prefixWord ++ tailWord_2191060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191060).length < 2 ^ (prefixWord ++ tailWord_2191060).sum := by decide
  have hdescent : baseEnd_2191060 < baseStart_2191060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191072 : List Nat := [2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 5]
def baseStart_2191072 : Nat := 118140960795 + 2191072 * 2 ^ 59
def prefixEnd_2191072 : Nat := 4983230072969 + 3 ^ 40 * 2191072 * 2
def baseEnd_2191072 : Nat := 1125073084608156654423449

theorem tailTrace_2191072 : CollatzResearch.WordTrace tailWord_2191072 prefixEnd_2191072 1125073084608156654423449 := by
  unfold tailWord_2191072
  simp only [CollatzResearch.WordTrace]
  refine ⟨39957480559063912075351735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53276640745418549433802313 39957480559063912075351735)
  ·
    refine ⟨59936220838595868113027603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39957480559063912075351735 59936220838595868113027603)
    ·
      refine ⟨89904331257893802169541405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59936220838595868113027603 89904331257893802169541405)
      ·
        refine ⟨33714124221710175813578027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89904331257893802169541405 33714124221710175813578027)
        ·
          refine ⟨50571186332565263720367041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33714124221710175813578027 50571186332565263720367041)
          ·
            refine ⟨37928389749423947790275281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50571186332565263720367041 37928389749423947790275281)
            ·
              refine ⟨28446292312067960842706461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37928389749423947790275281 28446292312067960842706461)
              ·
                refine ⟨10667359617025485316014923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28446292312067960842706461 10667359617025485316014923)
                ·
                  refine ⟨16001039425538227974022385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10667359617025485316014923 16001039425538227974022385)
                  ·
                    refine ⟨12000779569153670980516789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16001039425538227974022385 12000779569153670980516789)
                    ·
                      refine ⟨1125073084608156654423449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12000779569153670980516789 1125073084608156654423449)
                      ·
                        rfl

theorem cell23_2191072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_2191072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191072 prefixEnd_2191072 := by exact prefixLift 2191072
  have htrace : WordTrace (prefixWord ++ tailWord_2191072) baseStart_2191072 baseEnd_2191072 := by
    simpa [prefixWord, tailWord_2191072, baseEnd_2191072] using wordTrace_append hprefix tailTrace_2191072
  have hstable : (prefixWord ++ tailWord_2191072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191072).length < 2 ^ (prefixWord ++ tailWord_2191072).sum := by decide
  have hdescent : baseEnd_2191072 < baseStart_2191072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191099 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 4, 4, 2]
def baseStart_2191099 : Nat := 118140960795 + 2191099 * 2 ^ 59
def prefixEnd_2191099 : Nat := 4983230072969 + 3 ^ 40 * 2191099 * 2
def baseEnd_2191099 : Nat := 1125086948585828048785825

theorem tailTrace_2191099 : CollatzResearch.WordTrace tailWord_2191099 prefixEnd_2191099 1125086948585828048785825 := by
  unfold tailWord_2191099
  simp only [CollatzResearch.WordTrace]
  refine ⟨79915945889030007761936351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53277297259353338507957567 79915945889030007761936351)
  ·
    refine ⟨119873918833545011642904527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79915945889030007761936351 119873918833545011642904527)
    ·
      refine ⟨179810878250317517464356791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119873918833545011642904527 179810878250317517464356791)
      ·
        refine ⟨269716317375476276196535187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179810878250317517464356791 269716317375476276196535187)
        ·
          refine ⟨404574476063214414294802781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269716317375476276196535187 404574476063214414294802781)
          ·
            refine ⟨151715428523705405360551043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 404574476063214414294802781 151715428523705405360551043)
            ·
              refine ⟨227573142785558108040826565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151715428523705405360551043 227573142785558108040826565)
              ·
                refine ⟨42669964272292145257654981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 227573142785558108040826565 42669964272292145257654981)
                ·
                  refine ⟨8000618301054777235810309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42669964272292145257654981 8000618301054777235810309)
                  ·
                    refine ⟨1500115931447770731714433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8000618301054777235810309 1500115931447770731714433)
                    ·
                      refine ⟨1125086948585828048785825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1500115931447770731714433 1125086948585828048785825)
                      ·
                        rfl

theorem cell23_2191099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 4, 2].length) (baseStart_2191099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191099 prefixEnd_2191099 := by exact prefixLift 2191099
  have htrace : WordTrace (prefixWord ++ tailWord_2191099) baseStart_2191099 baseEnd_2191099 := by
    simpa [prefixWord, tailWord_2191099, baseEnd_2191099] using wordTrace_append hprefix tailTrace_2191099
  have hstable : (prefixWord ++ tailWord_2191099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191099).length < 2 ^ (prefixWord ++ tailWord_2191099).sum := by decide
  have hdescent : baseEnd_2191099 < baseStart_2191099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191117 : List Nat := [1, 7, 2, 1, 1, 2, 1, 1, 7]
def baseStart_2191117 : Nat := 118140960795 + 2191117 * 2 ^ 59
def prefixEnd_2191117 : Nat := 4983230072969 + 3 ^ 40 * 2191117 * 2
def baseEnd_2191117 : Nat := 125010687915289886484527

theorem tailTrace_2191117 : CollatzResearch.WordTrace tailWord_2191117 prefixEnd_2191117 125010687915289886484527 := by
  unfold tailWord_2191117
  simp only [CollatzResearch.WordTrace]
  refine ⟨79916602402964796836091605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53277734935309864557394403 79916602402964796836091605)
  ·
    refine ⟨1873045368819487425845897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 79916602402964796836091605 1873045368819487425845897)
    ·
      refine ⟨1404784026614615569384423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1873045368819487425845897 1404784026614615569384423)
      ·
        refine ⟨2107176039921923354076635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1404784026614615569384423 2107176039921923354076635)
        ·
          refine ⟨3160764059882885031114953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2107176039921923354076635 3160764059882885031114953)
          ·
            refine ⟨2370573044912163773336215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3160764059882885031114953 2370573044912163773336215)
            ·
              refine ⟨3555859567368245660004323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2370573044912163773336215 3555859567368245660004323)
              ·
                refine ⟨5333789351052368490006485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3555859567368245660004323 5333789351052368490006485)
                ·
                  refine ⟨125010687915289886484527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5333789351052368490006485 125010687915289886484527)
                  ·
                    rfl

theorem cell23_2191117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_2191117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191117 prefixEnd_2191117 := by exact prefixLift 2191117
  have htrace : WordTrace (prefixWord ++ tailWord_2191117) baseStart_2191117 baseEnd_2191117 := by
    simpa [prefixWord, tailWord_2191117, baseEnd_2191117] using wordTrace_append hprefix tailTrace_2191117
  have hstable : (prefixWord ++ tailWord_2191117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191117).length < 2 ^ (prefixWord ++ tailWord_2191117).sum := by decide
  have hdescent : baseEnd_2191117 < baseStart_2191117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191199 : List Nat := [1, 1, 2, 3, 1, 4, 1, 3, 1, 6]
def baseStart_2191199 : Nat := 118140960795 + 2191199 * 2 ^ 59
def prefixEnd_2191199 : Nat := 4983230072969 + 3 ^ 40 * 2191199 * 2
def baseEnd_2191199 : Nat := 375046098883759219178455

theorem tailTrace_2191199 : CollatzResearch.WordTrace tailWord_2191199 prefixEnd_2191199 375046098883759219178455 := by
  unfold tailWord_2191199
  simp only [CollatzResearch.WordTrace]
  refine ⟨79919593188667724840576651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53279728792445149893717767 79919593188667724840576651)
  ·
    refine ⟨119879389783001587260864977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79919593188667724840576651 119879389783001587260864977)
    ·
      refine ⟨89909542337251190445648733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119879389783001587260864977 89909542337251190445648733)
      ·
        refine ⟨33716078376469196417118275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89909542337251190445648733 33716078376469196417118275)
        ·
          refine ⟨50574117564703794625677413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33716078376469196417118275 50574117564703794625677413)
          ·
            refine ⟨9482647043381961492314515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50574117564703794625677413 9482647043381961492314515)
            ·
              refine ⟨14223970565072942238471773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9482647043381961492314515 14223970565072942238471773)
              ·
                refine ⟨5333988961902353339426915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14223970565072942238471773 5333988961902353339426915)
                ·
                  refine ⟨8000983442853530009140373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5333988961902353339426915 8000983442853530009140373)
                  ·
                    refine ⟨375046098883759219178455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8000983442853530009140373 375046098883759219178455)
                    ·
                      rfl

theorem cell23_2191199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 6].length) (baseStart_2191199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191199 prefixEnd_2191199 := by exact prefixLift 2191199
  have htrace : WordTrace (prefixWord ++ tailWord_2191199) baseStart_2191199 baseEnd_2191199 := by
    simpa [prefixWord, tailWord_2191199, baseEnd_2191199] using wordTrace_append hprefix tailTrace_2191199
  have hstable : (prefixWord ++ tailWord_2191199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191199).length < 2 ^ (prefixWord ++ tailWord_2191199).sum := by decide
  have hdescent : baseEnd_2191199 < baseStart_2191199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191210 : List Nat := [3, 1, 3, 4, 1, 1, 1, 1, 1, 5, 2]
def baseStart_2191210 : Nat := 118140960795 + 2191210 * 2 ^ 59
def prefixEnd_2191210 : Nat := 4983230072969 + 3 ^ 40 * 2191210 * 2
def baseEnd_2191210 : Nat := 1125143944938477114497815

theorem tailTrace_2191210 : CollatzResearch.WordTrace tailWord_2191210 prefixEnd_2191210 1125143944938477114497815 := by
  unfold tailWord_2191210
  simp only [CollatzResearch.WordTrace]
  refine ⟨19979998597906968429806771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53279996261085249146151389 19979998597906968429806771)
  ·
    refine ⟨29969997896860452644710157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19979998597906968429806771 29969997896860452644710157)
    ·
      refine ⟨11238749211322669741766309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29969997896860452644710157 11238749211322669741766309)
      ·
        refine ⟨2107265477123000576581183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11238749211322669741766309 2107265477123000576581183)
        ·
          refine ⟨3160898215684500864871775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2107265477123000576581183 3160898215684500864871775)
          ·
            refine ⟨4741347323526751297307663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3160898215684500864871775 4741347323526751297307663)
            ·
              refine ⟨7112020985290126945961495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4741347323526751297307663 7112020985290126945961495)
              ·
                refine ⟨10668031477935190418942243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7112020985290126945961495 10668031477935190418942243)
                ·
                  refine ⟨16002047216902785628413365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10668031477935190418942243 16002047216902785628413365)
                  ·
                    refine ⟨1500191926584636152663753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16002047216902785628413365 1500191926584636152663753)
                    ·
                      refine ⟨1125143944938477114497815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1500191926584636152663753 1125143944938477114497815)
                      ·
                        rfl

theorem cell23_2191210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_2191210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191210 prefixEnd_2191210 := by exact prefixLift 2191210
  have htrace : WordTrace (prefixWord ++ tailWord_2191210) baseStart_2191210 baseEnd_2191210 := by
    simpa [prefixWord, tailWord_2191210, baseEnd_2191210] using wordTrace_append hprefix tailTrace_2191210
  have hstable : (prefixWord ++ tailWord_2191210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191210).length < 2 ^ (prefixWord ++ tailWord_2191210).sum := by decide
  have hdescent : baseEnd_2191210 < baseStart_2191210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191260 : List Nat := [2, 2, 3, 3, 1, 2, 2, 2, 1, 2, 3]
def baseStart_2191260 : Nat := 118140960795 + 2191260 * 2 ^ 59
def prefixEnd_2191260 : Nat := 4983230072969 + 3 ^ 40 * 2191260 * 2
def baseEnd_2191260 : Nat := 1125169618971201918872585

theorem tailTrace_2191260 : CollatzResearch.WordTrace tailWord_2191260 prefixEnd_2191260 1125169618971201918872585 := by
  unfold tailWord_2191260
  simp only [CollatzResearch.WordTrace]
  refine ⟨39960909020723366129273617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53281212027631154839031489 39960909020723366129273617)
  ·
    refine ⟨29970681765542524596955213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39960909020723366129273617 29970681765542524596955213)
    ·
      refine ⟨11239005662078446723858205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29970681765542524596955213 11239005662078446723858205)
      ·
        refine ⟨4214627123279417521446827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11239005662078446723858205 4214627123279417521446827)
        ·
          refine ⟨6321940684919126282170241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4214627123279417521446827 6321940684919126282170241)
          ·
            refine ⟨4741455513689344711627681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6321940684919126282170241 4741455513689344711627681)
            ·
              refine ⟨3556091635267008533720761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4741455513689344711627681 3556091635267008533720761)
              ·
                refine ⟨2667068726450256400290571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3556091635267008533720761 2667068726450256400290571)
                ·
                  refine ⟨4000603089675384600435857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2667068726450256400290571 4000603089675384600435857)
                  ·
                    refine ⟨3000452317256538450326893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4000603089675384600435857 3000452317256538450326893)
                    ·
                      refine ⟨1125169618971201918872585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3000452317256538450326893 1125169618971201918872585)
                      ·
                        rfl

theorem cell23_2191260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_2191260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191260 prefixEnd_2191260 := by exact prefixLift 2191260
  have htrace : WordTrace (prefixWord ++ tailWord_2191260) baseStart_2191260 baseEnd_2191260 := by
    simpa [prefixWord, tailWord_2191260, baseEnd_2191260] using wordTrace_append hprefix tailTrace_2191260
  have hstable : (prefixWord ++ tailWord_2191260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191260).length < 2 ^ (prefixWord ++ tailWord_2191260).sum := by decide
  have hdescent : baseEnd_2191260 < baseStart_2191260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191263 : List Nat := [1, 1, 2, 5, 3, 2, 2, 7]
def baseStart_2191263 : Nat := 118140960795 + 2191263 * 2 ^ 59
def prefixEnd_2191263 : Nat := 4983230072969 + 3 ^ 40 * 2191263 * 2
def baseEnd_2191263 : Nat := 41673005904191311375373

theorem tailTrace_2191263 : CollatzResearch.WordTrace tailWord_2191263 prefixEnd_2191263 41673005904191311375373 := by
  unfold tailWord_2191263
  simp only [CollatzResearch.WordTrace]
  refine ⟨79921927460435863770906443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53281284973623909180604295 79921927460435863770906443)
  ·
    refine ⟨119882891190653795656359665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79921927460435863770906443 119882891190653795656359665)
    ·
      refine ⟨89912168392990346742269749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119882891190653795656359665 89912168392990346742269749)
      ·
        refine ⟨8429265786842845007087789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89912168392990346742269749 8429265786842845007087789)
        ·
          refine ⟨3160974670066066877657921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8429265786842845007087789 3160974670066066877657921)
          ·
            refine ⟨2370731002549550158243441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3160974670066066877657921 2370731002549550158243441)
            ·
              refine ⟨1778048251912162618682581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2370731002549550158243441 1778048251912162618682581)
              ·
                refine ⟨41673005904191311375373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1778048251912162618682581 41673005904191311375373)
                ·
                  rfl

theorem cell23_2191263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 7].length) (baseStart_2191263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191263 prefixEnd_2191263 := by exact prefixLift 2191263
  have htrace : WordTrace (prefixWord ++ tailWord_2191263) baseStart_2191263 baseEnd_2191263 := by
    simpa [prefixWord, tailWord_2191263, baseEnd_2191263] using wordTrace_append hprefix tailTrace_2191263
  have hstable : (prefixWord ++ tailWord_2191263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191263).length < 2 ^ (prefixWord ++ tailWord_2191263).sum := by decide
  have hdescent : baseEnd_2191263 < baseStart_2191263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191283 : List Nat := [1, 1, 1, 2, 3, 1, 3, 5, 1, 3, 2]
def baseStart_2191283 : Nat := 118140960795 + 2191283 * 2 ^ 59
def prefixEnd_2191283 : Nat := 4983230072969 + 3 ^ 40 * 2191283 * 2
def baseEnd_2191283 : Nat := 1125181429026255328884979

theorem tailTrace_2191283 : CollatzResearch.WordTrace tailWord_2191283 prefixEnd_2191283 1125181429026255328884979 := by
  unfold tailWord_2191283
  simp only [CollatzResearch.WordTrace]
  refine ⟨79922656920363407186634503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53281771280242271457756335 79922656920363407186634503)
  ·
    refine ⟨119883985380545110779951755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79922656920363407186634503 119883985380545110779951755)
    ·
      refine ⟨179825978070817666169927633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119883985380545110779951755 179825978070817666169927633)
      ·
        refine ⟨134869483553113249627445725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179825978070817666169927633 134869483553113249627445725)
        ·
          refine ⟨50576056332417468610292147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134869483553113249627445725 50576056332417468610292147)
          ·
            refine ⟨75864084498626202915438221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50576056332417468610292147 75864084498626202915438221)
            ·
              refine ⟨28449031686984826093289333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75864084498626202915438221 28449031686984826093289333)
              ·
                refine ⟨2667096720654827446245875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28449031686984826093289333 2667096720654827446245875)
                ·
                  refine ⟨4000645080982241169368813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2667096720654827446245875 4000645080982241169368813)
                  ·
                    refine ⟨1500241905368340438513305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4000645080982241169368813 1500241905368340438513305)
                    ·
                      refine ⟨1125181429026255328884979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1500241905368340438513305 1125181429026255328884979)
                      ·
                        rfl

theorem cell23_2191283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 3, 2].length) (baseStart_2191283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191283 prefixEnd_2191283 := by exact prefixLift 2191283
  have htrace : WordTrace (prefixWord ++ tailWord_2191283) baseStart_2191283 baseEnd_2191283 := by
    simpa [prefixWord, tailWord_2191283, baseEnd_2191283] using wordTrace_append hprefix tailTrace_2191283
  have hstable : (prefixWord ++ tailWord_2191283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191283).length < 2 ^ (prefixWord ++ tailWord_2191283).sum := by decide
  have hdescent : baseEnd_2191283 < baseStart_2191283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191299 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 5]
def baseStart_2191299 : Nat := 118140960795 + 2191299 * 2 ^ 59
def prefixEnd_2191299 : Nat := 4983230072969 + 3 ^ 40 * 2191299 * 2
def baseEnd_2191299 : Nat := 1125189644716727266284905

theorem tailTrace_2191299 : CollatzResearch.WordTrace tailWord_2191299 prefixEnd_2191299 1125189644716727266284905 := by
  unfold tailWord_2191299
  simp only [CollatzResearch.WordTrace]
  refine ⟨79923240488305441919216951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53282160325536961279477967 79923240488305441919216951)
  ·
    refine ⟨119884860732458162878825427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79923240488305441919216951 119884860732458162878825427)
    ·
      refine ⟨179827291098687244318238141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119884860732458162878825427 179827291098687244318238141)
      ·
        refine ⟨67435234162007716619339303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179827291098687244318238141 67435234162007716619339303)
        ·
          refine ⟨101152851243011574929008955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67435234162007716619339303 101152851243011574929008955)
          ·
            refine ⟨151729276864517362393513433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101152851243011574929008955 151729276864517362393513433)
            ·
              refine ⟨113796957648388021795135075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151729276864517362393513433 113796957648388021795135075)
              ·
                refine ⟨170695436472582032692702613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113796957648388021795135075 170695436472582032692702613)
                ·
                  refine ⟨8001348584652282782470435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 170695436472582032692702613 8001348584652282782470435)
                  ·
                    refine ⟨12002022876978424173705653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8001348584652282782470435 12002022876978424173705653)
                    ·
                      refine ⟨1125189644716727266284905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12002022876978424173705653 1125189644716727266284905)
                      ·
                        rfl

theorem cell23_2191299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_2191299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191299 prefixEnd_2191299 := by exact prefixLift 2191299
  have htrace : WordTrace (prefixWord ++ tailWord_2191299) baseStart_2191299 baseEnd_2191299 := by
    simpa [prefixWord, tailWord_2191299, baseEnd_2191299] using wordTrace_append hprefix tailTrace_2191299
  have hstable : (prefixWord ++ tailWord_2191299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191299).length < 2 ^ (prefixWord ++ tailWord_2191299).sum := by decide
  have hdescent : baseEnd_2191299 < baseStart_2191299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191313 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 6, 2, 2]
def baseStart_2191313 : Nat := 118140960795 + 2191313 * 2 ^ 59
def prefixEnd_2191313 : Nat := 4983230072969 + 3 ^ 40 * 2191313 * 2
def baseEnd_2191313 : Nat := 1125196833445890211509841

theorem tailTrace_2191313 : CollatzResearch.WordTrace tailWord_2191313 prefixEnd_2191313 1125196833445890211509841 := by
  unfold tailWord_2191313
  simp only [CollatzResearch.WordTrace]
  refine ⟨79923751110254722310226593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53282500740169814873484395 79923751110254722310226593)
  ·
    refine ⟨59942813332691041732669945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79923751110254722310226593 59942813332691041732669945)
    ·
      refine ⟨44957109999518281299502459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59942813332691041732669945 44957109999518281299502459)
      ·
        refine ⟨67435664999277421949253689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44957109999518281299502459 67435664999277421949253689)
        ·
          refine ⟨50576748749458066461940267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67435664999277421949253689 50576748749458066461940267)
          ·
            refine ⟨75865123124187099692910401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50576748749458066461940267 75865123124187099692910401)
            ·
              refine ⟨56898842343140324769682801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75865123124187099692910401 56898842343140324769682801)
              ·
                refine ⟨42674131757355243577262101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56898842343140324769682801 42674131757355243577262101)
                ·
                  refine ⟨2000349926126027042684161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42674131757355243577262101 2000349926126027042684161)
                  ·
                    refine ⟨1500262444594520282013121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2000349926126027042684161 1500262444594520282013121)
                    ·
                      refine ⟨1125196833445890211509841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1500262444594520282013121 1125196833445890211509841)
                      ·
                        rfl

theorem cell23_2191313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6, 2, 2].length) (baseStart_2191313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191313 prefixEnd_2191313 := by exact prefixLift 2191313
  have htrace : WordTrace (prefixWord ++ tailWord_2191313) baseStart_2191313 baseEnd_2191313 := by
    simpa [prefixWord, tailWord_2191313, baseEnd_2191313] using wordTrace_append hprefix tailTrace_2191313
  have hstable : (prefixWord ++ tailWord_2191313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191313).length < 2 ^ (prefixWord ++ tailWord_2191313).sum := by decide
  have hdescent : baseEnd_2191313 < baseStart_2191313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191316 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_2191316 : Nat := 118140960795 + 2191316 * 2 ^ 59
def prefixEnd_2191316 : Nat := 4983230072969 + 3 ^ 40 * 2191316 * 2
def baseEnd_2191316 : Nat := 1125198373887853699772327

theorem tailTrace_2191316 : CollatzResearch.WordTrace tailWord_2191316 prefixEnd_2191316 1125198373887853699772327 := by
  unfold tailWord_2191316
  simp only [CollatzResearch.WordTrace]
  refine ⟨39961930264621926911292901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53282573686162569215057201 39961930264621926911292901)
  ·
    refine ⟨7492861924616611295867419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39961930264621926911292901 7492861924616611295867419)
    ·
      refine ⟨11239292886924916943801129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7492861924616611295867419 11239292886924916943801129)
      ·
        refine ⟨8429469665193687707850847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11239292886924916943801129 8429469665193687707850847)
        ·
          refine ⟨12644204497790531561776271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8429469665193687707850847 12644204497790531561776271)
          ·
            refine ⟨18966306746685797342664407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12644204497790531561776271 18966306746685797342664407)
            ·
              refine ⟨28449460120028696013996611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18966306746685797342664407 28449460120028696013996611)
              ·
                refine ⟨42674190180043044020994917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28449460120028696013996611 42674190180043044020994917)
                ·
                  refine ⟨8001410658758070753936547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42674190180043044020994917 8001410658758070753936547)
                  ·
                    refine ⟨12002115988137106130904821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8001410658758070753936547 12002115988137106130904821)
                    ·
                      refine ⟨1125198373887853699772327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12002115988137106130904821 1125198373887853699772327)
                      ·
                        rfl

theorem cell23_2191316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_2191316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191316 prefixEnd_2191316 := by exact prefixLift 2191316
  have htrace : WordTrace (prefixWord ++ tailWord_2191316) baseStart_2191316 baseEnd_2191316 := by
    simpa [prefixWord, tailWord_2191316, baseEnd_2191316] using wordTrace_append hprefix tailTrace_2191316
  have hstable : (prefixWord ++ tailWord_2191316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191316).length < 2 ^ (prefixWord ++ tailWord_2191316).sum := by decide
  have hdescent : baseEnd_2191316 < baseStart_2191316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191317 : List Nat := [1, 3, 2, 3, 2, 3, 1, 2, 1, 3, 2]
def baseStart_2191317 : Nat := 118140960795 + 2191317 * 2 ^ 59
def prefixEnd_2191317 : Nat := 4983230072969 + 3 ^ 40 * 2191317 * 2
def baseEnd_2191317 : Nat := 1125198887368508195859823

theorem tailTrace_2191317 : CollatzResearch.WordTrace tailWord_2191317 prefixEnd_2191317 1125198887368508195859823 := by
  unfold tailWord_2191317
  simp only [CollatzResearch.WordTrace]
  refine ⟨79923897002240230993372205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53282598001493487328914803 79923897002240230993372205)
  ·
    refine ⟨29971461375840086622514577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79923897002240230993372205 29971461375840086622514577)
    ·
      refine ⟨22478596031880064966885933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29971461375840086622514577 22478596031880064966885933)
      ·
        refine ⟨8429473511955024362582225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22478596031880064966885933 8429473511955024362582225)
        ·
          refine ⟨6322105133966268271936669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8429473511955024362582225 6322105133966268271936669)
          ·
            refine ⟨2370789425237350601976251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6322105133966268271936669 2370789425237350601976251)
            ·
              refine ⟨3556184137856025902964377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2370789425237350601976251 3556184137856025902964377)
              ·
                refine ⟨2667138103392019427223283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3556184137856025902964377 2667138103392019427223283)
                ·
                  refine ⟨4000707155088029140834925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2667138103392019427223283 4000707155088029140834925)
                  ·
                    refine ⟨1500265183158010927813097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4000707155088029140834925 1500265183158010927813097)
                    ·
                      refine ⟨1125198887368508195859823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1500265183158010927813097 1125198887368508195859823)
                      ·
                        rfl

theorem cell23_2191317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_2191317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191317 prefixEnd_2191317 := by exact prefixLift 2191317
  have htrace : WordTrace (prefixWord ++ tailWord_2191317) baseStart_2191317 baseEnd_2191317 := by
    simpa [prefixWord, tailWord_2191317, baseEnd_2191317] using wordTrace_append hprefix tailTrace_2191317
  have hstable : (prefixWord ++ tailWord_2191317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191317).length < 2 ^ (prefixWord ++ tailWord_2191317).sum := by decide
  have hdescent : baseEnd_2191317 < baseStart_2191317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191319 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 9]
def baseStart_2191319 : Nat := 118140960795 + 2191319 * 2 ^ 59
def prefixEnd_2191319 : Nat := 4983230072969 + 3 ^ 40 * 2191319 * 2
def baseEnd_2191319 : Nat := 125022212703313020892757

theorem tailTrace_2191319 : CollatzResearch.WordTrace tailWord_2191319 prefixEnd_2191319 125022212703313020892757 := by
  unfold tailWord_2191319
  simp only [CollatzResearch.WordTrace]
  refine ⟨79923969948232985334945011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53282646632155323556630007 79923969948232985334945011)
  ·
    refine ⟨119885954922349478002417517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79923969948232985334945011 119885954922349478002417517)
    ·
      refine ⟨44957233095881054250906569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119885954922349478002417517 44957233095881054250906569)
      ·
        refine ⟨33717924821910790688179927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44957233095881054250906569 33717924821910790688179927)
        ·
          refine ⟨50576887232866186032269891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33717924821910790688179927 50576887232866186032269891)
          ·
            refine ⟨75865330849299279048404837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50576887232866186032269891 75865330849299279048404837)
            ·
              refine ⟨14224749534243614821575907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75865330849299279048404837 14224749534243614821575907)
              ·
                refine ⟨21337124301365422232363861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14224749534243614821575907 21337124301365422232363861)
                ·
                  refine ⟨125022212703313020892757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21337124301365422232363861 125022212703313020892757)
                  ·
                    rfl

theorem cell23_2191319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 9].length) (baseStart_2191319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191319 prefixEnd_2191319 := by exact prefixLift 2191319
  have htrace : WordTrace (prefixWord ++ tailWord_2191319) baseStart_2191319 baseEnd_2191319 := by
    simpa [prefixWord, tailWord_2191319, baseEnd_2191319] using wordTrace_append hprefix tailTrace_2191319
  have hstable : (prefixWord ++ tailWord_2191319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191319).length < 2 ^ (prefixWord ++ tailWord_2191319).sum := by decide
  have hdescent : baseEnd_2191319 < baseStart_2191319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191353 : List Nat := [1, 2, 1, 3, 1, 5, 1, 4, 5]
def baseStart_2191353 : Nat := 118140960795 + 2191353 * 2 ^ 59
def prefixEnd_2191353 : Nat := 4983230072969 + 3 ^ 40 * 2191353 * 2
def baseEnd_2191353 : Nat := 125024152519118895001073

theorem tailTrace_2191353 : CollatzResearch.WordTrace tailWord_2191353 prefixEnd_2191353 125024152519118895001073 := by
  unfold tailWord_2191353
  simp only [CollatzResearch.WordTrace]
  refine ⟨79925210030109809141682713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53283473353406539427788475 79925210030109809141682713)
  ·
    refine ⟨59943907522582356856262035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79925210030109809141682713 59943907522582356856262035)
    ·
      refine ⟨89915861283873535284393053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59943907522582356856262035 89915861283873535284393053)
      ·
        refine ⟨33718447981452575731647395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89915861283873535284393053 33718447981452575731647395)
        ·
          refine ⟨50577671972178863597471093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33718447981452575731647395 50577671972178863597471093)
          ·
            refine ⟨4741656747391768462262915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50577671972178863597471093 4741656747391768462262915)
            ·
              refine ⟨7112485121087652693394373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4741656747391768462262915 7112485121087652693394373)
              ·
                refine ⟨1333590960203934880011445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7112485121087652693394373 1333590960203934880011445)
                ·
                  refine ⟨125024152519118895001073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1333590960203934880011445 125024152519118895001073)
                  ·
                    rfl

theorem cell23_2191353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4, 5].length) (baseStart_2191353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191353 prefixEnd_2191353 := by exact prefixLift 2191353
  have htrace : WordTrace (prefixWord ++ tailWord_2191353) baseStart_2191353 baseEnd_2191353 := by
    simpa [prefixWord, tailWord_2191353, baseEnd_2191353] using wordTrace_append hprefix tailTrace_2191353
  have hstable : (prefixWord ++ tailWord_2191353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191353).length < 2 ^ (prefixWord ++ tailWord_2191353).sum := by decide
  have hdescent : baseEnd_2191353 < baseStart_2191353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191383 : List Nat := [1, 1, 3, 5, 2, 1, 1, 1, 1, 7]
def baseStart_2191383 : Nat := 118140960795 + 2191383 * 2 ^ 59
def prefixEnd_2191383 : Nat := 4983230072969 + 3 ^ 40 * 2191383 * 2
def baseEnd_2191383 : Nat := 375077592363901645878173

theorem tailTrace_2191383 : CollatzResearch.WordTrace tailWord_2191383 prefixEnd_2191383 375077592363901645878173 := by
  unfold tailWord_2191383
  simp only [CollatzResearch.WordTrace]
  refine ⟨79926304220001124265274803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53284202813334082843516535 79926304220001124265274803)
  ·
    refine ⟨119889456330001686397912205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79926304220001124265274803 119889456330001686397912205)
    ·
      refine ⟨44958546123750632399217077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119889456330001686397912205 44958546123750632399217077)
      ·
        refine ⟨4214863699101621787426601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44958546123750632399217077 4214863699101621787426601)
        ·
          refine ⟨3161147774326216340569951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4214863699101621787426601 3161147774326216340569951)
          ·
            refine ⟨4741721661489324510854927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3161147774326216340569951 4741721661489324510854927)
            ·
              refine ⟨7112582492233986766282391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4741721661489324510854927 7112582492233986766282391)
              ·
                refine ⟨10668873738350980149423587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7112582492233986766282391 10668873738350980149423587)
                ·
                  refine ⟨16003310607526470224135381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10668873738350980149423587 16003310607526470224135381)
                  ·
                    refine ⟨375077592363901645878173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16003310607526470224135381 375077592363901645878173)
                    ·
                      rfl

theorem cell23_2191383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 7].length) (baseStart_2191383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191383 prefixEnd_2191383 := by exact prefixLift 2191383
  have htrace : WordTrace (prefixWord ++ tailWord_2191383) baseStart_2191383 baseEnd_2191383 := by
    simpa [prefixWord, tailWord_2191383, baseEnd_2191383] using wordTrace_append hprefix tailTrace_2191383
  have hstable : (prefixWord ++ tailWord_2191383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191383).length < 2 ^ (prefixWord ++ tailWord_2191383).sum := by decide
  have hdescent : baseEnd_2191383 < baseStart_2191383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191413 : List Nat := [1, 3, 3, 1, 1, 1, 3, 3, 3, 4]
def baseStart_2191413 : Nat := 118140960795 + 2191413 * 2 ^ 59
def prefixEnd_2191413 : Nat := 4983230072969 + 3 ^ 40 * 2191413 * 2
def baseEnd_2191413 : Nat := 375082727170446606753127

theorem tailTrace_2191413 : CollatzResearch.WordTrace tailWord_2191413 prefixEnd_2191413 375082727170446606753127 := by
  unfold tailWord_2191413
  simp only [CollatzResearch.WordTrace]
  refine ⟨79927398409892439388866893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53284932273261626259244595 79927398409892439388866893)
  ·
    refine ⟨29972774403709664770825085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79927398409892439388866893 29972774403709664770825085)
    ·
      refine ⟨11239790401391124289059407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29972774403709664770825085 11239790401391124289059407)
      ·
        refine ⟨16859685602086686433589111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11239790401391124289059407 16859685602086686433589111)
        ·
          refine ⟨25289528403130029650383667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16859685602086686433589111 25289528403130029650383667)
          ·
            refine ⟨37934292604695044475575501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25289528403130029650383667 37934292604695044475575501)
            ·
              refine ⟨14225359726760641678340813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37934292604695044475575501 14225359726760641678340813)
              ·
                refine ⟨5334509897535240629377805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14225359726760641678340813 5334509897535240629377805)
                ·
                  refine ⟨2000441211575715236016677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5334509897535240629377805 2000441211575715236016677)
                  ·
                    refine ⟨375082727170446606753127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2000441211575715236016677 375082727170446606753127)
                    ·
                      rfl

theorem cell23_2191413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_2191413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191413 prefixEnd_2191413 := by exact prefixLift 2191413
  have htrace : WordTrace (prefixWord ++ tailWord_2191413) baseStart_2191413 baseEnd_2191413 := by
    simpa [prefixWord, tailWord_2191413, baseEnd_2191413] using wordTrace_append hprefix tailTrace_2191413
  have hstable : (prefixWord ++ tailWord_2191413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191413).length < 2 ^ (prefixWord ++ tailWord_2191413).sum := by decide
  have hdescent : baseEnd_2191413 < baseStart_2191413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191454 : List Nat := [4, 4, 1, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_2191454 : Nat := 118140960795 + 2191454 * 2 ^ 59
def prefixEnd_2191454 : Nat := 4983230072969 + 3 ^ 40 * 2191454 * 2
def baseEnd_2191454 : Nat := 1125269234218174159846693

theorem tailTrace_2191454 : CollatzResearch.WordTrace tailWord_2191454 prefixEnd_2191454 1125269234218174159846693 := by
  unfold tailWord_2191454
  simp only [CollatzResearch.WordTrace]
  refine ⟨9991111725342987923888677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53285929201829268927406277 9991111725342987923888677)
  ·
    refine ⟨1873333448501810235729127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9991111725342987923888677 1873333448501810235729127)
    ·
      refine ⟨2810000172752715353593691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1873333448501810235729127 2810000172752715353593691)
      ·
        refine ⟨4215000259129073030390537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2810000172752715353593691 4215000259129073030390537)
        ·
          refine ⟨3161250194346804772792903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4215000259129073030390537 3161250194346804772792903)
          ·
            refine ⟨4741875291520207159189355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3161250194346804772792903 4741875291520207159189355)
            ·
              refine ⟨7112812937280310738784033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4741875291520207159189355 7112812937280310738784033)
              ·
                refine ⟨5334609702960233054088025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7112812937280310738784033 5334609702960233054088025)
                ·
                  refine ⟨4000957277220174790566019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5334609702960233054088025 4000957277220174790566019)
                  ·
                    refine ⟨6001435915830262185849029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4000957277220174790566019 6001435915830262185849029)
                    ·
                      refine ⟨1125269234218174159846693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6001435915830262185849029 1125269234218174159846693)
                      ·
                        rfl

theorem cell23_2191454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_2191454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191454 prefixEnd_2191454 := by exact prefixLift 2191454
  have htrace : WordTrace (prefixWord ++ tailWord_2191454) baseStart_2191454 baseEnd_2191454 := by
    simpa [prefixWord, tailWord_2191454, baseEnd_2191454] using wordTrace_append hprefix tailTrace_2191454
  have hstable : (prefixWord ++ tailWord_2191454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191454).length < 2 ^ (prefixWord ++ tailWord_2191454).sum := by decide
  have hdescent : baseEnd_2191454 < baseStart_2191454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191520 : List Nat := [2, 1, 1, 4, 2, 2, 1, 4, 2, 4]
def baseStart_2191520 : Nat := 118140960795 + 2191520 * 2 ^ 59
def prefixEnd_2191520 : Nat := 4983230072969 + 3 ^ 40 * 2191520 * 2
def baseEnd_2191520 : Nat := 375101041313790300540463

theorem tailTrace_2191520 : CollatzResearch.WordTrace tailWord_2191520 prefixEnd_2191520 375101041313790300540463 := by
  unfold tailWord_2191520
  simp only [CollatzResearch.WordTrace]
  refine ⟨39965650510252398331506007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53287534013669864442008009 39965650510252398331506007)
  ·
    refine ⟨59948475765378597497259011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39965650510252398331506007 59948475765378597497259011)
    ·
      refine ⟨89922713648067896245888517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59948475765378597497259011 89922713648067896245888517)
      ·
        refine ⟨16860508809012730546104097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89922713648067896245888517 16860508809012730546104097)
        ·
          refine ⟨12645381606759547909578073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16860508809012730546104097 12645381606759547909578073)
          ·
            refine ⟨9484036205069660932183555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12645381606759547909578073 9484036205069660932183555)
            ·
              refine ⟨14226054307604491398275333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9484036205069660932183555 14226054307604491398275333)
              ·
                refine ⟨2667385182675842137176625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14226054307604491398275333 2667385182675842137176625)
                ·
                  refine ⟨2000538887006881602882469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2667385182675842137176625 2000538887006881602882469)
                  ·
                    refine ⟨375101041313790300540463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2000538887006881602882469 375101041313790300540463)
                    ·
                      rfl

theorem cell23_2191520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 2, 4].length) (baseStart_2191520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191520 prefixEnd_2191520 := by exact prefixLift 2191520
  have htrace : WordTrace (prefixWord ++ tailWord_2191520) baseStart_2191520 baseEnd_2191520 := by
    simpa [prefixWord, tailWord_2191520, baseEnd_2191520] using wordTrace_append hprefix tailTrace_2191520
  have hstable : (prefixWord ++ tailWord_2191520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191520).length < 2 ^ (prefixWord ++ tailWord_2191520).sum := by decide
  have hdescent : baseEnd_2191520 < baseStart_2191520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191521 : List Nat := [1, 2, 3, 3, 1, 4, 2, 2, 1, 1, 3]
def baseStart_2191521 : Nat := 118140960795 + 2191521 * 2 ^ 59
def prefixEnd_2191521 : Nat := 4983230072969 + 3 ^ 40 * 2191521 * 2
def baseEnd_2191521 : Nat := 1125303637422025397708885

theorem tailTrace_2191521 : CollatzResearch.WordTrace tailWord_2191521 prefixEnd_2191521 1125303637422025397708885 := by
  unfold tailWord_2191521
  simp only [CollatzResearch.WordTrace]
  refine ⟨79931337493501173833798417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53287558329000782555865611 79931337493501173833798417)
  ·
    refine ⟨59948503120125880375348813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79931337493501173833798417 59948503120125880375348813)
    ·
      refine ⟨22480688670047205140755805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59948503120125880375348813 22480688670047205140755805)
      ·
        refine ⟨8430258251267701927783427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22480688670047205140755805 8430258251267701927783427)
        ·
          refine ⟨12645387376901552891675141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8430258251267701927783427 12645387376901552891675141)
          ·
            refine ⟨2371010133169041167189089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12645387376901552891675141 2371010133169041167189089)
            ·
              refine ⟨1778257599876780875391817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2371010133169041167189089 1778257599876780875391817)
              ·
                refine ⟨1333693199907585656543863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1778257599876780875391817 1333693199907585656543863)
                ·
                  refine ⟨2000539799861378484815795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1333693199907585656543863 2000539799861378484815795)
                  ·
                    refine ⟨3000809699792067727223693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2000539799861378484815795 3000809699792067727223693)
                    ·
                      refine ⟨1125303637422025397708885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3000809699792067727223693 1125303637422025397708885)
                      ·
                        rfl

theorem cell23_2191521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_2191521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191521 prefixEnd_2191521 := by exact prefixLift 2191521
  have htrace : WordTrace (prefixWord ++ tailWord_2191521) baseStart_2191521 baseEnd_2191521 := by
    simpa [prefixWord, tailWord_2191521, baseEnd_2191521] using wordTrace_append hprefix tailTrace_2191521
  have hstable : (prefixWord ++ tailWord_2191521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191521).length < 2 ^ (prefixWord ++ tailWord_2191521).sum := by decide
  have hdescent : baseEnd_2191521 < baseStart_2191521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191560 : List Nat := [2, 1, 3, 1, 2, 1, 1, 4, 4, 1, 3]
def baseStart_2191560 : Nat := 118140960795 + 2191560 * 2 ^ 59
def prefixEnd_2191560 : Nat := 4983230072969 + 3 ^ 40 * 2191560 * 2
def baseEnd_2191560 : Nat := 1125323663167550745121205

theorem tailTrace_2191560 : CollatzResearch.WordTrace tailWord_2191560 prefixEnd_2191560 1125323663167550745121205 := by
  unfold tailWord_2191560
  simp only [CollatzResearch.WordTrace]
  refine ⟨39966379970179941747234067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53288506626906588996312089 39966379970179941747234067)
  ·
    refine ⟨59949569955269912620851101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39966379970179941747234067 59949569955269912620851101)
    ·
      refine ⟨22481088733226217232819163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59949569955269912620851101 22481088733226217232819163)
      ·
        refine ⟨33721633099839325849228745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22481088733226217232819163 33721633099839325849228745)
        ·
          refine ⟨25291224824879494386921559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33721633099839325849228745 25291224824879494386921559)
          ·
            refine ⟨37936837237319241580382339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25291224824879494386921559 37936837237319241580382339)
            ·
              refine ⟨56905255855978862370573509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37936837237319241580382339 56905255855978862370573509)
              ·
                refine ⟨10669735472996036694482533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56905255855978862370573509 10669735472996036694482533)
                ·
                  refine ⟨2000575401186756880215475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10669735472996036694482533 2000575401186756880215475)
                  ·
                    refine ⟨3000863101780135320323213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2000575401186756880215475 3000863101780135320323213)
                    ·
                      refine ⟨1125323663167550745121205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3000863101780135320323213 1125323663167550745121205)
                      ·
                        rfl

theorem cell23_2191560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_2191560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191560 prefixEnd_2191560 := by exact prefixLift 2191560
  have htrace : WordTrace (prefixWord ++ tailWord_2191560) baseStart_2191560 baseEnd_2191560 := by
    simpa [prefixWord, tailWord_2191560, baseEnd_2191560] using wordTrace_append hprefix tailTrace_2191560
  have hstable : (prefixWord ++ tailWord_2191560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191560).length < 2 ^ (prefixWord ++ tailWord_2191560).sum := by decide
  have hdescent : baseEnd_2191560 < baseStart_2191560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191564 : List Nat := [2, 2, 1, 6, 1, 1, 1, 3, 1, 2, 3]
def baseStart_2191564 : Nat := 118140960795 + 2191564 * 2 ^ 59
def prefixEnd_2191564 : Nat := 4983230072969 + 3 ^ 40 * 2191564 * 2
def baseEnd_2191564 : Nat := 1125325717090168729471187

theorem tailTrace_2191564 : CollatzResearch.WordTrace tailWord_2191564 prefixEnd_2191564 1125325717090168729471187 := by
  unfold tailWord_2191564
  simp only [CollatzResearch.WordTrace]
  refine ⟨39966452916172696088806873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53288603888230261451742497 39966452916172696088806873)
  ·
    refine ⟨29974839687129522066605155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39966452916172696088806873 29974839687129522066605155)
    ·
      refine ⟨44962259530694283099907733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29974839687129522066605155 44962259530694283099907733)
      ·
        refine ⟨2107605915501294520308175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44962259530694283099907733 2107605915501294520308175)
        ·
          refine ⟨3161408873251941780462263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2107605915501294520308175 3161408873251941780462263)
          ·
            refine ⟨4742113309877912670693395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3161408873251941780462263 4742113309877912670693395)
            ·
              refine ⟨7113169964816869006040093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4742113309877912670693395 7113169964816869006040093)
              ·
                refine ⟨2667438736806325877265035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7113169964816869006040093 2667438736806325877265035)
                ·
                  refine ⟨4001158105209488815897553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2667438736806325877265035 4001158105209488815897553)
                  ·
                    refine ⟨3000868578907116611923165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4001158105209488815897553 3000868578907116611923165)
                    ·
                      refine ⟨1125325717090168729471187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3000868578907116611923165 1125325717090168729471187)
                      ·
                        rfl

theorem cell23_2191564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_2191564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191564 prefixEnd_2191564 := by exact prefixLift 2191564
  have htrace : WordTrace (prefixWord ++ tailWord_2191564) baseStart_2191564 baseEnd_2191564 := by
    simpa [prefixWord, tailWord_2191564, baseEnd_2191564] using wordTrace_append hprefix tailTrace_2191564
  have hstable : (prefixWord ++ tailWord_2191564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191564).length < 2 ^ (prefixWord ++ tailWord_2191564).sum := by decide
  have hdescent : baseEnd_2191564 < baseStart_2191564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191577 : List Nat := [1, 2, 1, 2, 3, 1, 5, 2, 2, 1, 3]
def baseStart_2191577 : Nat := 118140960795 + 2191577 * 2 ^ 59
def prefixEnd_2191577 : Nat := 4983230072969 + 3 ^ 40 * 2191577 * 2
def baseEnd_2191577 : Nat := 1125332392338677178608627

theorem tailTrace_2191577 : CollatzResearch.WordTrace tailWord_2191577 prefixEnd_2191577 1125332392338677178608627 := by
  unfold tailWord_2191577
  simp only [CollatzResearch.WordTrace]
  refine ⟨79933379981298295397836985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53288919987532196931891323 79933379981298295397836985)
  ·
    refine ⟨59950034985973721548377739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79933379981298295397836985 59950034985973721548377739)
    ·
      refine ⟨89925052478960582322566609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59950034985973721548377739 89925052478960582322566609)
      ·
        refine ⟨67443789359220436741924957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89925052478960582322566609 67443789359220436741924957)
        ·
          refine ⟨25291421009707663778221859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67443789359220436741924957 25291421009707663778221859)
          ·
            refine ⟨37937131514561495667332789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25291421009707663778221859 37937131514561495667332789)
            ·
              refine ⟨3556606079490140218812449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37937131514561495667332789 3556606079490140218812449)
              ·
                refine ⟨2667454559617605164109337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3556606079490140218812449 2667454559617605164109337)
                ·
                  refine ⟨2000590919713203873082003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2667454559617605164109337 2000590919713203873082003)
                  ·
                    refine ⟨3000886379569805809623005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2000590919713203873082003 3000886379569805809623005)
                    ·
                      refine ⟨1125332392338677178608627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3000886379569805809623005 1125332392338677178608627)
                      ·
                        rfl

theorem cell23_2191577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2, 1, 3].length) (baseStart_2191577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191577 prefixEnd_2191577 := by exact prefixLift 2191577
  have htrace : WordTrace (prefixWord ++ tailWord_2191577) baseStart_2191577 baseEnd_2191577 := by
    simpa [prefixWord, tailWord_2191577, baseEnd_2191577] using wordTrace_append hprefix tailTrace_2191577
  have hstable : (prefixWord ++ tailWord_2191577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191577).length < 2 ^ (prefixWord ++ tailWord_2191577).sum := by decide
  have hdescent : baseEnd_2191577 < baseStart_2191577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191594 : List Nat := [3, 1, 3, 1, 1, 2, 5, 1, 2, 1, 3]
def baseStart_2191594 : Nat := 118140960795 + 2191594 * 2 ^ 59
def prefixEnd_2191594 : Nat := 4983230072969 + 3 ^ 40 * 2191594 * 2
def baseEnd_2191594 : Nat := 1125341121509803612096049

theorem tailTrace_2191594 : CollatzResearch.WordTrace tailWord_2191594 prefixEnd_2191594 1125341121509803612096049 := by
  unfold tailWord_2191594
  simp only [CollatzResearch.WordTrace]
  refine ⟨19983500005559176825301459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53289333348157804867470557 19983500005559176825301459)
  ·
    refine ⟨29975250008338765237952189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19983500005559176825301459 29975250008338765237952189)
    ·
      refine ⟨11240718753127036964232071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29975250008338765237952189 11240718753127036964232071)
      ·
        refine ⟨16861078129690555446348107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11240718753127036964232071 16861078129690555446348107)
        ·
          refine ⟨25291617194535833169522161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16861078129690555446348107 25291617194535833169522161)
          ·
            refine ⟨18968712895901874877141621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25291617194535833169522161 18968712895901874877141621)
            ·
              refine ⟨1778316833990800769732027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18968712895901874877141621 1778316833990800769732027)
              ·
                refine ⟨2667475250986201154598041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1778316833990800769732027 2667475250986201154598041)
                ·
                  refine ⟨2000606438239650865948531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2667475250986201154598041 2000606438239650865948531)
                  ·
                    refine ⟨3000909657359476298922797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2000606438239650865948531 3000909657359476298922797)
                    ·
                      refine ⟨1125341121509803612096049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3000909657359476298922797 1125341121509803612096049)
                      ·
                        rfl

theorem cell23_2191594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_2191594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191594 prefixEnd_2191594 := by exact prefixLift 2191594
  have htrace : WordTrace (prefixWord ++ tailWord_2191594) baseStart_2191594 baseEnd_2191594 := by
    simpa [prefixWord, tailWord_2191594, baseEnd_2191594] using wordTrace_append hprefix tailTrace_2191594
  have hstable : (prefixWord ++ tailWord_2191594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191594).length < 2 ^ (prefixWord ++ tailWord_2191594).sum := by decide
  have hdescent : baseEnd_2191594 < baseStart_2191594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191603 : List Nat := [1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 5]
def baseStart_2191603 : Nat := 118140960795 + 2191603 * 2 ^ 59
def prefixEnd_2191603 : Nat := 4983230072969 + 3 ^ 40 * 2191603 * 2
def baseEnd_2191603 : Nat := 1125345742835694076883507

theorem tailTrace_2191603 : CollatzResearch.WordTrace tailWord_2191603 prefixEnd_2191603 1125345742835694076883507 := by
  unfold tailWord_2191603
  simp only [CollatzResearch.WordTrace]
  refine ⟨79934328279204101838283463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53289552186136067892188975 79934328279204101838283463)
  ·
    refine ⟨119901492418806152757425195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79934328279204101838283463 119901492418806152757425195)
    ·
      refine ⟨179852238628209229136137793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119901492418806152757425195 179852238628209229136137793)
      ·
        refine ⟨134889178971156921852103345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179852238628209229136137793 134889178971156921852103345)
        ·
          refine ⟨101166884228367691389077509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134889178971156921852103345 101166884228367691389077509)
          ·
            refine ⟨18968790792818942135452033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101166884228367691389077509 18968790792818942135452033)
            ·
              refine ⟨14226593094614206601589025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18968790792818942135452033 14226593094614206601589025)
              ·
                refine ⟨10669944820960654951191769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14226593094614206601589025 10669944820960654951191769)
                ·
                  refine ⟨8002458615720491213393827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10669944820960654951191769 8002458615720491213393827)
                  ·
                    refine ⟨12003687923580736820090741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8002458615720491213393827 12003687923580736820090741)
                    ·
                      refine ⟨1125345742835694076883507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12003687923580736820090741 1125345742835694076883507)
                      ·
                        rfl

theorem cell23_2191603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 5].length) (baseStart_2191603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191603 prefixEnd_2191603 := by exact prefixLift 2191603
  have htrace : WordTrace (prefixWord ++ tailWord_2191603) baseStart_2191603 baseEnd_2191603 := by
    simpa [prefixWord, tailWord_2191603, baseEnd_2191603] using wordTrace_append hprefix tailTrace_2191603
  have hstable : (prefixWord ++ tailWord_2191603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191603).length < 2 ^ (prefixWord ++ tailWord_2191603).sum := by decide
  have hdescent : baseEnd_2191603 < baseStart_2191603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191613 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 1, 4, 4]
def baseStart_2191613 : Nat := 118140960795 + 2191613 * 2 ^ 59
def prefixEnd_2191613 : Nat := 4983230072969 + 3 ^ 40 * 2191613 * 2
def baseEnd_2191613 : Nat := 1125350877642239037758461

theorem tailTrace_2191613 : CollatzResearch.WordTrace tailWord_2191613 prefixEnd_2191613 1125350877642239037758461 := by
  unfold tailWord_2191613
  simp only [CollatzResearch.WordTrace]
  refine ⟨79934693009167873546147493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53289795339445249030764995 79934693009167873546147493)
  ·
    refine ⟨14987754939218976289902655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79934693009167873546147493 14987754939218976289902655)
    ·
      refine ⟨22481632408828464434853983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14987754939218976289902655 22481632408828464434853983)
      ·
        refine ⟨33722448613242696652280975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22481632408828464434853983 33722448613242696652280975)
        ·
          refine ⟨50583672919864044978421463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33722448613242696652280975 50583672919864044978421463)
          ·
            refine ⟨75875509379796067467632195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50583672919864044978421463 75875509379796067467632195)
            ·
              refine ⟨113813264069694101201448293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75875509379796067467632195 113813264069694101201448293)
              ·
                refine ⟨21339987013067643975271555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113813264069694101201448293 21339987013067643975271555)
                ·
                  refine ⟨32009980519601465962907333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21339987013067643975271555 32009980519601465962907333)
                  ·
                    refine ⟨6001871347425274868045125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32009980519601465962907333 6001871347425274868045125)
                    ·
                      refine ⟨1125350877642239037758461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6001871347425274868045125 1125350877642239037758461)
                      ·
                        rfl

theorem cell23_2191613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_2191613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191613 prefixEnd_2191613 := by exact prefixLift 2191613
  have htrace : WordTrace (prefixWord ++ tailWord_2191613) baseStart_2191613 baseEnd_2191613 := by
    simpa [prefixWord, tailWord_2191613, baseEnd_2191613] using wordTrace_append hprefix tailTrace_2191613
  have hstable : (prefixWord ++ tailWord_2191613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191613).length < 2 ^ (prefixWord ++ tailWord_2191613).sum := by decide
  have hdescent : baseEnd_2191613 < baseStart_2191613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191617 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 6, 2, 2]
def baseStart_2191617 : Nat := 118140960795 + 2191617 * 2 ^ 59
def prefixEnd_2191617 : Nat := 4983230072969 + 3 ^ 40 * 2191617 * 2
def baseEnd_2191617 : Nat := 1125352931564857022108443

theorem tailTrace_2191617 : CollatzResearch.WordTrace tailWord_2191617 prefixEnd_2191617 1125352931564857022108443 := by
  unfold tailWord_2191617
  simp only [CollatzResearch.WordTrace]
  refine ⟨79934838901153382229293105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53289892600768921486195403 79934838901153382229293105)
  ·
    refine ⟨59951129175865036671969829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79934838901153382229293105 59951129175865036671969829)
    ·
      refine ⟨11240836720474694375994343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59951129175865036671969829 11240836720474694375994343)
      ·
        refine ⟨16861255080712041563991515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11240836720474694375994343 16861255080712041563991515)
        ·
          refine ⟨25291882621068062345987273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16861255080712041563991515 25291882621068062345987273)
          ·
            refine ⟨18968911965801046759490455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25291882621068062345987273 18968911965801046759490455)
            ·
              refine ⟨28453367948701570139235683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18968911965801046759490455 28453367948701570139235683)
              ·
                refine ⟨42680051923052355208853525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28453367948701570139235683 42680051923052355208853525)
                ·
                  refine ⟨2000627433893079150415009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42680051923052355208853525 2000627433893079150415009)
                  ·
                    refine ⟨1500470575419809362811257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2000627433893079150415009 1500470575419809362811257)
                    ·
                      refine ⟨1125352931564857022108443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1500470575419809362811257 1125352931564857022108443)
                      ·
                        rfl

theorem cell23_2191617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_2191617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191617 prefixEnd_2191617 := by exact prefixLift 2191617
  have htrace : WordTrace (prefixWord ++ tailWord_2191617) baseStart_2191617 baseEnd_2191617 := by
    simpa [prefixWord, tailWord_2191617, baseEnd_2191617] using wordTrace_append hprefix tailTrace_2191617
  have hstable : (prefixWord ++ tailWord_2191617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191617).length < 2 ^ (prefixWord ++ tailWord_2191617).sum := by decide
  have hdescent : baseEnd_2191617 < baseStart_2191617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191655 : List Nat := [1, 1, 8, 1, 1, 2, 1, 2, 1, 3, 2]
def baseStart_2191655 : Nat := 118140960795 + 2191655 * 2 ^ 59
def prefixEnd_2191655 : Nat := 4983230072969 + 3 ^ 40 * 2191655 * 2
def baseEnd_2191655 : Nat := 1125372443829727873433269

theorem tailTrace_2191655 : CollatzResearch.WordTrace tailWord_2191655 prefixEnd_2191655 1125372443829727873433269 := by
  unfold tailWord_2191655
  simp only [CollatzResearch.WordTrace]
  refine ⟨79936224875015714719176419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53290816583343809812784279 79936224875015714719176419)
  ·
    refine ⟨119904337312523572078764629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79936224875015714719176419 119904337312523572078764629)
    ·
      refine ⟨1405128952881135610298023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 119904337312523572078764629 1405128952881135610298023)
      ·
        refine ⟨2107693429321703415447035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1405128952881135610298023 2107693429321703415447035)
        ·
          refine ⟨3161540143982555123170553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2107693429321703415447035 3161540143982555123170553)
          ·
            refine ⟨2371155107986916342377915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3161540143982555123170553 2371155107986916342377915)
            ·
              refine ⟨3556732661980374513566873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2371155107986916342377915 3556732661980374513566873)
              ·
                refine ⟨2667549496485280885175155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3556732661980374513566873 2667549496485280885175155)
                ·
                  refine ⟨4001324244727921327762733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2667549496485280885175155 4001324244727921327762733)
                  ·
                    refine ⟨1500496591772970497911025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4001324244727921327762733 1500496591772970497911025)
                    ·
                      refine ⟨1125372443829727873433269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1500496591772970497911025 1125372443829727873433269)
                      ·
                        rfl

theorem cell23_2191655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_2191655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191655 prefixEnd_2191655 := by exact prefixLift 2191655
  have htrace : WordTrace (prefixWord ++ tailWord_2191655) baseStart_2191655 baseEnd_2191655 := by
    simpa [prefixWord, tailWord_2191655, baseEnd_2191655] using wordTrace_append hprefix tailTrace_2191655
  have hstable : (prefixWord ++ tailWord_2191655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191655).length < 2 ^ (prefixWord ++ tailWord_2191655).sum := by decide
  have hdescent : baseEnd_2191655 < baseStart_2191655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191713 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 12]
def baseStart_2191713 : Nat := 118140960795 + 2191713 * 2 ^ 59
def prefixEnd_2191713 : Nat := 4983230072969 + 3 ^ 40 * 2191713 * 2
def baseEnd_2191713 : Nat := 125044691745298738500889

theorem tailTrace_2191713 : CollatzResearch.WordTrace tailWord_2191713 prefixEnd_2191713 125044691745298738500889 := by
  unfold tailWord_2191713
  simp only [CollatzResearch.WordTrace]
  refine ⟨79938340308805590624787793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53292226872537060416525195 79938340308805590624787793)
  ·
    refine ⟨59953755231604192968590845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79938340308805590624787793 59953755231604192968590845)
    ·
      refine ⟨22482658211851572363221567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59953755231604192968590845 22482658211851572363221567)
      ·
        refine ⟨33723987317777358544832351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22482658211851572363221567 33723987317777358544832351)
        ·
          refine ⟨50585980976666037817248527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33723987317777358544832351 50585980976666037817248527)
          ·
            refine ⟨75878971464999056725872791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50585980976666037817248527 75878971464999056725872791)
            ·
              refine ⟨113818457197498585088809187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75878971464999056725872791 113818457197498585088809187)
              ·
                refine ⟨170727685796247877633213781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113818457197498585088809187 170727685796247877633213781)
                ·
                  refine ⟨125044691745298738500889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 170727685796247877633213781 125044691745298738500889)
                  ·
                    rfl

theorem cell23_2191713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 12].length) (baseStart_2191713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191713 prefixEnd_2191713 := by exact prefixLift 2191713
  have htrace : WordTrace (prefixWord ++ tailWord_2191713) baseStart_2191713 baseEnd_2191713 := by
    simpa [prefixWord, tailWord_2191713, baseEnd_2191713] using wordTrace_append hprefix tailTrace_2191713
  have hstable : (prefixWord ++ tailWord_2191713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191713).length < 2 ^ (prefixWord ++ tailWord_2191713).sum := by decide
  have hdescent : baseEnd_2191713 < baseStart_2191713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191717 : List Nat := [1, 3, 1, 3, 1, 4, 1, 2, 3, 4]
def baseStart_2191717 : Nat := 118140960795 + 2191717 * 2 ^ 59
def prefixEnd_2191717 : Nat := 4983230072969 + 3 ^ 40 * 2191717 * 2
def baseEnd_2191717 : Nat := 375134759876768876952661

theorem tailTrace_2191717 : CollatzResearch.WordTrace tailWord_2191717 prefixEnd_2191717 375134759876768876952661 := by
  unfold tailWord_2191717
  simp only [CollatzResearch.WordTrace]
  refine ⟨79938486200791099307933405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53292324133860732871955603 79938486200791099307933405)
  ·
    refine ⟨29976932325296662240475027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79938486200791099307933405 29976932325296662240475027)
    ·
      refine ⟨44965398487944993360712541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29976932325296662240475027 44965398487944993360712541)
      ·
        refine ⟨16862024432979372510267203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44965398487944993360712541 16862024432979372510267203)
        ·
          refine ⟨25293036649469058765400805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16862024432979372510267203 25293036649469058765400805)
          ·
            refine ⟨4742444371775448518512651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25293036649469058765400805 4742444371775448518512651)
            ·
              refine ⟨7113666557663172777768977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4742444371775448518512651 7113666557663172777768977)
              ·
                refine ⟨5335249918247379583326733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7113666557663172777768977 5335249918247379583326733)
                ·
                  refine ⟨2000718719342767343747525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5335249918247379583326733 2000718719342767343747525)
                  ·
                    refine ⟨375134759876768876952661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2000718719342767343747525 375134759876768876952661)
                    ·
                      rfl

theorem cell23_2191717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3, 4].length) (baseStart_2191717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191717 prefixEnd_2191717 := by exact prefixLift 2191717
  have htrace : WordTrace (prefixWord ++ tailWord_2191717) baseStart_2191717 baseEnd_2191717 := by
    simpa [prefixWord, tailWord_2191717, baseEnd_2191717] using wordTrace_append hprefix tailTrace_2191717
  have hstable : (prefixWord ++ tailWord_2191717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191717).length < 2 ^ (prefixWord ++ tailWord_2191717).sum := by decide
  have hdescent : baseEnd_2191717 < baseStart_2191717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191724 : List Nat := [2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 4]
def baseStart_2191724 : Nat := 118140960795 + 2191724 * 2 ^ 59
def prefixEnd_2191724 : Nat := 4983230072969 + 3 ^ 40 * 2191724 * 2
def baseEnd_2191724 : Nat := 1125407873994888103470451

theorem tailTrace_2191724 : CollatzResearch.WordTrace tailWord_2191724 prefixEnd_2191724 1125407873994888103470451 := by
  unfold tailWord_2191724
  simp only [CollatzResearch.WordTrace]
  refine ⟨39969370755882869751719113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53292494341177159668958817 39969370755882869751719113)
  ·
    refine ⟨29977028066912152313789335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39969370755882869751719113 29977028066912152313789335)
    ·
      refine ⟨44965542100368228470684003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29977028066912152313789335 44965542100368228470684003)
      ·
        refine ⟨67448313150552342706026005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44965542100368228470684003 67448313150552342706026005)
        ·
          refine ⟨3161639678932141064344969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 67448313150552342706026005 3161639678932141064344969)
          ·
            refine ⟨2371229759199105798258727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3161639678932141064344969 2371229759199105798258727)
            ·
              refine ⟨3556844638798658697388091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2371229759199105798258727 3556844638798658697388091)
              ·
                refine ⟨5335266958197988046082137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3556844638798658697388091 5335266958197988046082137)
                ·
                  refine ⟨4001450218648491034561603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5335266958197988046082137 4001450218648491034561603)
                  ·
                    refine ⟨6002175327972736551842405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4001450218648491034561603 6002175327972736551842405)
                    ·
                      refine ⟨1125407873994888103470451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6002175327972736551842405 1125407873994888103470451)
                      ·
                        rfl

theorem cell23_2191724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 4].length) (baseStart_2191724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191724 prefixEnd_2191724 := by exact prefixLift 2191724
  have htrace : WordTrace (prefixWord ++ tailWord_2191724) baseStart_2191724 baseEnd_2191724 := by
    simpa [prefixWord, tailWord_2191724, baseEnd_2191724] using wordTrace_append hprefix tailTrace_2191724
  have hstable : (prefixWord ++ tailWord_2191724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191724).length < 2 ^ (prefixWord ++ tailWord_2191724).sum := by decide
  have hdescent : baseEnd_2191724 < baseStart_2191724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191767 : List Nat := [1, 1, 3, 3, 1, 1, 3, 2, 1, 5, 2]
def baseStart_2191767 : Nat := 118140960795 + 2191767 * 2 ^ 59
def prefixEnd_2191767 : Nat := 4983230072969 + 3 ^ 40 * 2191767 * 2
def baseEnd_2191767 : Nat := 1125429953663031435232753

theorem tailTrace_2191767 : CollatzResearch.WordTrace tailWord_2191767 prefixEnd_2191767 1125429953663031435232753 := by
  unfold tailWord_2191767
  simp only [CollatzResearch.WordTrace]
  refine ⟨79940309850609957847253555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53293539900406638564835703 79940309850609957847253555)
  ·
    refine ⟨119910464775914936770880333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79940309850609957847253555 119910464775914936770880333)
    ·
      refine ⟨44966424290968101289080125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119910464775914936770880333 44966424290968101289080125)
      ·
        refine ⟨16862409109113037983405047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44966424290968101289080125 16862409109113037983405047)
        ·
          refine ⟨25293613663669556975107571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16862409109113037983405047 25293613663669556975107571)
          ·
            refine ⟨37940420495504335462661357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25293613663669556975107571 37940420495504335462661357)
            ·
              refine ⟨14227657685814125798498009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37940420495504335462661357 14227657685814125798498009)
              ·
                refine ⟨10670743264360594348873507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14227657685814125798498009 10670743264360594348873507)
                ·
                  refine ⟨16006114896540891523310261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10670743264360594348873507 16006114896540891523310261)
                  ·
                    refine ⟨1500573271550708580310337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16006114896540891523310261 1500573271550708580310337)
                    ·
                      refine ⟨1125429953663031435232753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1500573271550708580310337 1125429953663031435232753)
                      ·
                        rfl

theorem cell23_2191767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_2191767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191767 prefixEnd_2191767 := by exact prefixLift 2191767
  have htrace : WordTrace (prefixWord ++ tailWord_2191767) baseStart_2191767 baseEnd_2191767 := by
    simpa [prefixWord, tailWord_2191767, baseEnd_2191767] using wordTrace_append hprefix tailTrace_2191767
  have hstable : (prefixWord ++ tailWord_2191767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191767).length < 2 ^ (prefixWord ++ tailWord_2191767).sum := by decide
  have hdescent : baseEnd_2191767 < baseStart_2191767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191878 : List Nat := [6, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_2191878 : Nat := 118140960795 + 2191878 * 2 ^ 59
def prefixEnd_2191878 : Nat := 4983230072969 + 3 ^ 40 * 2191878 * 2
def baseEnd_2191878 : Nat := 1125486950015680500944743

theorem tailTrace_2191878 : CollatzResearch.WordTrace tailWord_2191878 prefixEnd_2191878 1125486950015680500944743 := by
  unfold tailWord_2191878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2498261198537744493892009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53296238902138549203029525 2498261198537744493892009)
  ·
    refine ⟨1873695898903308370419007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2498261198537744493892009 1873695898903308370419007)
    ·
      refine ⟨2810543848354962555628511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1873695898903308370419007 2810543848354962555628511)
      ·
        refine ⟨4215815772532443833442767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2810543848354962555628511 4215815772532443833442767)
        ·
          refine ⟨6323723658798665750164151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4215815772532443833442767 6323723658798665750164151)
          ·
            refine ⟨9485585488197998625246227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6323723658798665750164151 9485585488197998625246227)
            ·
              refine ⟨14228378232296997937869341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9485585488197998625246227 14228378232296997937869341)
              ·
                refine ⟨5335641837111374226701003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14228378232296997937869341 5335641837111374226701003)
                ·
                  refine ⟨8003462755667061340051505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5335641837111374226701003 8003462755667061340051505)
                  ·
                    refine ⟨6002597066750296005038629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8003462755667061340051505 6002597066750296005038629)
                    ·
                      refine ⟨1125486950015680500944743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6002597066750296005038629 1125486950015680500944743)
                      ·
                        rfl

theorem cell23_2191878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_2191878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191878 prefixEnd_2191878 := by exact prefixLift 2191878
  have htrace : WordTrace (prefixWord ++ tailWord_2191878) baseStart_2191878 baseEnd_2191878 := by
    simpa [prefixWord, tailWord_2191878, baseEnd_2191878] using wordTrace_append hprefix tailTrace_2191878
  have hstable : (prefixWord ++ tailWord_2191878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191878).length < 2 ^ (prefixWord ++ tailWord_2191878).sum := by decide
  have hdescent : baseEnd_2191878 < baseStart_2191878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191927 : List Nat := [1, 1, 3, 1, 2, 3, 4, 1, 7]
def baseStart_2191927 : Nat := 118140960795 + 2191927 * 2 ^ 59
def prefixEnd_2191927 : Nat := 4983230072969 + 3 ^ 40 * 2191927 * 2
def baseEnd_2191927 : Nat := 125056901174194534359113

theorem tailTrace_2191927 : CollatzResearch.WordTrace tailWord_2191927 prefixEnd_2191927 125056901174194534359113 := by
  unfold tailWord_2191927
  simp only [CollatzResearch.WordTrace]
  refine ⟨79946145530030305173078035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53297430353353536782052023 79946145530030305173078035)
  ·
    refine ⟨119919218295045457759617053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79946145530030305173078035 119919218295045457759617053)
    ·
      refine ⟨44969706860642046659856395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119919218295045457759617053 44969706860642046659856395)
      ·
        refine ⟨67454560290963069989784593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44969706860642046659856395 67454560290963069989784593)
        ·
          refine ⟨50590920218222302492338445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67454560290963069989784593 50590920218222302492338445)
          ·
            refine ⟨18971595081833363434626917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50590920218222302492338445 18971595081833363434626917)
            ·
              refine ⟨3557174077843755643992547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18971595081833363434626917 3557174077843755643992547)
              ·
                refine ⟨5335761116765633465988821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3557174077843755643992547 5335761116765633465988821)
                ·
                  refine ⟨125056901174194534359113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5335761116765633465988821 125056901174194534359113)
                  ·
                    rfl

theorem cell23_2191927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 7].length) (baseStart_2191927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191927 prefixEnd_2191927 := by exact prefixLift 2191927
  have htrace : WordTrace (prefixWord ++ tailWord_2191927) baseStart_2191927 baseEnd_2191927 := by
    simpa [prefixWord, tailWord_2191927, baseEnd_2191927] using wordTrace_append hprefix tailTrace_2191927
  have hstable : (prefixWord ++ tailWord_2191927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191927).length < 2 ^ (prefixWord ++ tailWord_2191927).sum := by decide
  have hdescent : baseEnd_2191927 < baseStart_2191927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191957 : List Nat := [1, 3, 2, 2, 1, 1, 4, 1, 1, 7]
def baseStart_2191957 : Nat := 118140960795 + 2191957 * 2 ^ 59
def prefixEnd_2191957 : Nat := 4983230072969 + 3 ^ 40 * 2191957 * 2
def baseEnd_2191957 : Nat := 375175838329128563952293

theorem tailTrace_2191957 : CollatzResearch.WordTrace tailWord_2191957 prefixEnd_2191957 375175838329128563952293 := by
  unfold tailWord_2191957
  simp only [CollatzResearch.WordTrace]
  refine ⟨79947239719921620296670125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53298159813281080197780083 79947239719921620296670125)
  ·
    refine ⟨29980214894970607611251297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79947239719921620296670125 29980214894970607611251297)
    ·
      refine ⟨22485161171227955708438473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29980214894970607611251297 22485161171227955708438473)
      ·
        refine ⟨16863870878420966781328855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22485161171227955708438473 16863870878420966781328855)
        ·
          refine ⟨25295806317631450171993283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16863870878420966781328855 25295806317631450171993283)
          ·
            refine ⟨37943709476447175257989925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25295806317631450171993283 37943709476447175257989925)
            ·
              refine ⟨7114445526833845360873111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37943709476447175257989925 7114445526833845360873111)
              ·
                refine ⟨10671668290250768041309667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7114445526833845360873111 10671668290250768041309667)
                ·
                  refine ⟨16007502435376152061964501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10671668290250768041309667 16007502435376152061964501)
                  ·
                    refine ⟨375175838329128563952293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16007502435376152061964501 375175838329128563952293)
                    ·
                      rfl

theorem cell23_2191957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_2191957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191957 prefixEnd_2191957 := by exact prefixLift 2191957
  have htrace : WordTrace (prefixWord ++ tailWord_2191957) baseStart_2191957 baseEnd_2191957 := by
    simpa [prefixWord, tailWord_2191957, baseEnd_2191957] using wordTrace_append hprefix tailTrace_2191957
  have hstable : (prefixWord ++ tailWord_2191957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191957).length < 2 ^ (prefixWord ++ tailWord_2191957).sum := by decide
  have hdescent : baseEnd_2191957 < baseStart_2191957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191984 : List Nat := [2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 5]
def baseStart_2191984 : Nat := 118140960795 + 2191984 * 2 ^ 59
def prefixEnd_2191984 : Nat := 4983230072969 + 3 ^ 40 * 2191984 * 2
def baseEnd_2191984 : Nat := 1125541378965057086219255

theorem tailTrace_2191984 : CollatzResearch.WordTrace tailWord_2191984 prefixEnd_2191984 1125541378965057086219255 := by
  unfold tailWord_2191984
  simp only [CollatzResearch.WordTrace]
  refine ⟨39974112245411901953951503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53298816327215869271935337 39974112245411901953951503)
  ·
    refine ⟨59961168368117852930927255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39974112245411901953951503 59961168368117852930927255)
    ·
      refine ⟨89941752552176779396390883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59961168368117852930927255 89941752552176779396390883)
      ·
        refine ⟨134912628828265169094586325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89941752552176779396390883 134912628828265169094586325)
        ·
          refine ⟨3162014738162464900654367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 134912628828265169094586325 3162014738162464900654367)
          ·
            refine ⟨4743022107243697350981551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3162014738162464900654367 4743022107243697350981551)
            ·
              refine ⟨7114533160865546026472327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4743022107243697350981551 7114533160865546026472327)
              ·
                refine ⟨10671799741298319039708491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7114533160865546026472327 10671799741298319039708491)
                ·
                  refine ⟨16007699611947478559562737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10671799741298319039708491 16007699611947478559562737)
                  ·
                    refine ⟨12005774708960608919672053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16007699611947478559562737 12005774708960608919672053)
                    ·
                      refine ⟨1125541378965057086219255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12005774708960608919672053 1125541378965057086219255)
                      ·
                        rfl

theorem cell23_2191984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 5].length) (baseStart_2191984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191984 prefixEnd_2191984 := by exact prefixLift 2191984
  have htrace : WordTrace (prefixWord ++ tailWord_2191984) baseStart_2191984 baseEnd_2191984 := by
    simpa [prefixWord, tailWord_2191984, baseEnd_2191984] using wordTrace_append hprefix tailTrace_2191984
  have hstable : (prefixWord ++ tailWord_2191984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191984).length < 2 ^ (prefixWord ++ tailWord_2191984).sum := by decide
  have hdescent : baseEnd_2191984 < baseStart_2191984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191989 : List Nat := [1, 3, 4, 2, 3, 1, 2, 1, 2, 2, 2]
def baseStart_2191989 : Nat := 118140960795 + 2191989 * 2 ^ 59
def prefixEnd_2191989 : Nat := 4983230072969 + 3 ^ 40 * 2191989 * 2
def baseEnd_2191989 : Nat := 1125543946368329566656733

theorem tailTrace_2191989 : CollatzResearch.WordTrace tailWord_2191989 prefixEnd_2191989 1125543946368329566656733 := by
  unfold tailWord_2191989
  simp only [CollatzResearch.WordTrace]
  refine ⟨79948406855805689761835021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53298937903870459841223347 79948406855805689761835021)
  ·
    refine ⟨29980652570927133660688133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79948406855805689761835021 29980652570927133660688133)
    ·
      refine ⟨5621372357048837561379025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29980652570927133660688133 5621372357048837561379025)
      ·
        refine ⟨4216029267786628171034269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5621372357048837561379025 4216029267786628171034269)
        ·
          refine ⟨1581010975419985564137851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4216029267786628171034269 1581010975419985564137851)
          ·
            refine ⟨2371516463129978346206777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1581010975419985564137851 2371516463129978346206777)
            ·
              refine ⟨1778637347347483759655083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2371516463129978346206777 1778637347347483759655083)
              ·
                refine ⟨2667956021021225639482625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1778637347347483759655083 2667956021021225639482625)
                ·
                  refine ⟨2000967015765919229611969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2667956021021225639482625 2000967015765919229611969)
                  ·
                    refine ⟨1500725261824439422208977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2000967015765919229611969 1500725261824439422208977)
                    ·
                      refine ⟨1125543946368329566656733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1500725261824439422208977 1125543946368329566656733)
                      ·
                        rfl

theorem cell23_2191989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_2191989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191989 prefixEnd_2191989 := by exact prefixLift 2191989
  have htrace : WordTrace (prefixWord ++ tailWord_2191989) baseStart_2191989 baseEnd_2191989 := by
    simpa [prefixWord, tailWord_2191989, baseEnd_2191989] using wordTrace_append hprefix tailTrace_2191989
  have hstable : (prefixWord ++ tailWord_2191989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191989).length < 2 ^ (prefixWord ++ tailWord_2191989).sum := by decide
  have hdescent : baseEnd_2191989 < baseStart_2191989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2191994 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2]
def baseStart_2191994 : Nat := 118140960795 + 2191994 * 2 ^ 59
def prefixEnd_2191994 : Nat := 4983230072969 + 3 ^ 40 * 2191994 * 2
def baseEnd_2191994 : Nat := 1125546513771602047094209

theorem tailTrace_2191994 : CollatzResearch.WordTrace tailWord_2191994 prefixEnd_2191994 1125546513771602047094209 := by
  unfold tailWord_2191994
  simp only [CollatzResearch.WordTrace]
  refine ⟨19987147305196893903941759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53299059480525050410511357 19987147305196893903941759)
  ·
    refine ⟨29980720957795340855912639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19987147305196893903941759 29980720957795340855912639)
    ·
      refine ⟨44971081436693011283868959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29980720957795340855912639 44971081436693011283868959)
      ·
        refine ⟨67456622155039516925803439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44971081436693011283868959 67456622155039516925803439)
        ·
          refine ⟨101184933232559275388705159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67456622155039516925803439 101184933232559275388705159)
          ·
            refine ⟨151777399848838913083057739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101184933232559275388705159 151777399848838913083057739)
            ·
              refine ⟨227666099773258369624586609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151777399848838913083057739 227666099773258369624586609)
              ·
                refine ⟨170749574829943777218439957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227666099773258369624586609 170749574829943777218439957)
                ·
                  refine ⟨8003886320153614557114373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 170749574829943777218439957 8003886320153614557114373)
                  ·
                    refine ⟨1500728685028802729458945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8003886320153614557114373 1500728685028802729458945)
                    ·
                      refine ⟨1125546513771602047094209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1500728685028802729458945 1125546513771602047094209)
                      ·
                        rfl

theorem cell23_2191994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2].length) (baseStart_2191994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2191994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2191994 prefixEnd_2191994 := by exact prefixLift 2191994
  have htrace : WordTrace (prefixWord ++ tailWord_2191994) baseStart_2191994 baseEnd_2191994 := by
    simpa [prefixWord, tailWord_2191994, baseEnd_2191994] using wordTrace_append hprefix tailTrace_2191994
  have hstable : (prefixWord ++ tailWord_2191994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2191994).length < 2 ^ (prefixWord ++ tailWord_2191994).sum := by decide
  have hdescent : baseEnd_2191994 < baseStart_2191994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2191994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192037 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 1, 2, 6]
def baseStart_2192037 : Nat := 118140960795 + 2192037 * 2 ^ 59
def prefixEnd_2192037 : Nat := 4983230072969 + 3 ^ 40 * 2192037 * 2
def baseEnd_2192037 : Nat := 1125568593439745378856511

theorem tailTrace_2192037 : CollatzResearch.WordTrace tailWord_2192037 prefixEnd_2192037 1125568593439745378856511 := by
  unfold tailWord_2192037
  simp only [CollatzResearch.WordTrace]
  refine ⟨79950157559631793959582365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53300105039754529306388243 79950157559631793959582365)
  ·
    refine ⟨29981309084861922734843387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79950157559631793959582365 29981309084861922734843387)
    ·
      refine ⟨44971963627292884102265081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29981309084861922734843387 44971963627292884102265081)
      ·
        refine ⟨33728972720469663076698811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44971963627292884102265081 33728972720469663076698811)
        ·
          refine ⟨50593459080704494615048217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33728972720469663076698811 50593459080704494615048217)
          ·
            refine ⟨37945094310528370961286163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50593459080704494615048217 37945094310528370961286163)
            ·
              refine ⟨56917641465792556441929245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37945094310528370961286163 56917641465792556441929245)
              ·
                refine ⟨21344115549672208665723467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56917641465792556441929245 21344115549672208665723467)
                ·
                  refine ⟨32016173324508312998585201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21344115549672208665723467 32016173324508312998585201)
                  ·
                    refine ⟨24012129993381234748938901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32016173324508312998585201 24012129993381234748938901)
                    ·
                      refine ⟨1125568593439745378856511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24012129993381234748938901 1125568593439745378856511)
                      ·
                        rfl

theorem cell23_2192037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_2192037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192037 prefixEnd_2192037 := by exact prefixLift 2192037
  have htrace : WordTrace (prefixWord ++ tailWord_2192037) baseStart_2192037 baseEnd_2192037 := by
    simpa [prefixWord, tailWord_2192037, baseEnd_2192037] using wordTrace_append hprefix tailTrace_2192037
  have hstable : (prefixWord ++ tailWord_2192037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192037).length < 2 ^ (prefixWord ++ tailWord_2192037).sum := by decide
  have hdescent : baseEnd_2192037 < baseStart_2192037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192057 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 1, 3, 7]
def baseStart_2192057 : Nat := 118140960795 + 2192057 * 2 ^ 59
def prefixEnd_2192057 : Nat := 4983230072969 + 3 ^ 40 * 2192057 * 2
def baseEnd_2192057 : Nat := 1125578863052835300606419

theorem tailTrace_2192057 : CollatzResearch.WordTrace tailWord_2192057 prefixEnd_2192057 1125578863052835300606419 := by
  unfold tailWord_2192057
  simp only [CollatzResearch.WordTrace]
  refine ⟨79950887019559337375310425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53300591346372891583540283 79950887019559337375310425)
  ·
    refine ⟨59963165264669503031482819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79950887019559337375310425 59963165264669503031482819)
    ·
      refine ⟨89944747897004254547224229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59963165264669503031482819 89944747897004254547224229)
      ·
        refine ⟨16864640230688297727604543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89944747897004254547224229 16864640230688297727604543)
        ·
          refine ⟨25296960346032446591406815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16864640230688297727604543 25296960346032446591406815)
          ·
            refine ⟨37945440519048669887110223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25296960346032446591406815 37945440519048669887110223)
            ·
              refine ⟨56918160778573004830665335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37945440519048669887110223 56918160778573004830665335)
              ·
                refine ⟨85377241167859507245998003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56918160778573004830665335 85377241167859507245998003)
                ·
                  refine ⟨128065861751789260868997005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85377241167859507245998003 128065861751789260868997005)
                  ·
                    refine ⟨48024698156920972825873877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 128065861751789260868997005 48024698156920972825873877)
                    ·
                      refine ⟨1125578863052835300606419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48024698156920972825873877 1125578863052835300606419)
                      ·
                        rfl

theorem cell23_2192057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_2192057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192057 prefixEnd_2192057 := by exact prefixLift 2192057
  have htrace : WordTrace (prefixWord ++ tailWord_2192057) baseStart_2192057 baseEnd_2192057 := by
    simpa [prefixWord, tailWord_2192057, baseEnd_2192057] using wordTrace_append hprefix tailTrace_2192057
  have hstable : (prefixWord ++ tailWord_2192057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192057).length < 2 ^ (prefixWord ++ tailWord_2192057).sum := by decide
  have hdescent : baseEnd_2192057 < baseStart_2192057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192061 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 5, 1, 3]
def baseStart_2192061 : Nat := 118140960795 + 2192061 * 2 ^ 59
def prefixEnd_2192061 : Nat := 4983230072969 + 3 ^ 40 * 2192061 * 2
def baseEnd_2192061 : Nat := 1125580916975453284956401

theorem tailTrace_2192061 : CollatzResearch.WordTrace tailWord_2192061 prefixEnd_2192061 1125580916975453284956401 := by
  unfold tailWord_2192061
  simp only [CollatzResearch.WordTrace]
  refine ⟨79951032911544846058456037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53300688607696564038970691 79951032911544846058456037)
  ·
    refine ⟨14990818670914658635960507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79951032911544846058456037 14990818670914658635960507)
    ·
      refine ⟨22486228006371987953940761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14990818670914658635960507 22486228006371987953940761)
      ·
        refine ⟨16864671004778990965455571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22486228006371987953940761 16864671004778990965455571)
        ·
          refine ⟨25297006507168486448183357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16864671004778990965455571 25297006507168486448183357)
          ·
            refine ⟨9486377440188182418068759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25297006507168486448183357 9486377440188182418068759)
            ·
              refine ⟨14229566160282273627103139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9486377440188182418068759 14229566160282273627103139)
              ·
                refine ⟨21344349240423410440654709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14229566160282273627103139 21344349240423410440654709)
                ·
                  refine ⟨2001032741289694728811379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21344349240423410440654709 2001032741289694728811379)
                  ·
                    refine ⟨3001549111934542093217069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2001032741289694728811379 3001549111934542093217069)
                    ·
                      refine ⟨1125580916975453284956401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3001549111934542093217069 1125580916975453284956401)
                      ·
                        rfl

theorem cell23_2192061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_2192061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192061 prefixEnd_2192061 := by exact prefixLift 2192061
  have htrace : WordTrace (prefixWord ++ tailWord_2192061) baseStart_2192061 baseEnd_2192061 := by
    simpa [prefixWord, tailWord_2192061, baseEnd_2192061] using wordTrace_append hprefix tailTrace_2192061
  have hstable : (prefixWord ++ tailWord_2192061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192061).length < 2 ^ (prefixWord ++ tailWord_2192061).sum := by decide
  have hdescent : baseEnd_2192061 < baseStart_2192061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192064 : List Nat := [2, 1, 1, 2, 4, 2, 2, 1, 3, 5]
def baseStart_2192064 : Nat := 118140960795 + 2192064 * 2 ^ 59
def prefixEnd_2192064 : Nat := 4983230072969 + 3 ^ 40 * 2192064 * 2
def baseEnd_2192064 : Nat := 375194152472472257739629

theorem tailTrace_2192064 : CollatzResearch.WordTrace tailWord_2192064 prefixEnd_2192064 375194152472472257739629 := by
  unfold tailWord_2192064
  simp only [CollatzResearch.WordTrace]
  refine ⟨39975571165266988785407623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53300761553689318380543497 39975571165266988785407623)
  ·
    refine ⟨59963356747900483178111435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39975571165266988785407623 59963356747900483178111435)
    ·
      refine ⟨89945035121850724767167153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59963356747900483178111435 89945035121850724767167153)
      ·
        refine ⟨67458776341388043575375365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89945035121850724767167153 67458776341388043575375365)
        ·
          refine ⟨12648520564010258170382881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67458776341388043575375365 12648520564010258170382881)
          ·
            refine ⟨9486390423007693627787161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12648520564010258170382881 9486390423007693627787161)
            ·
              refine ⟨7114792817255770220840371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9486390423007693627787161 7114792817255770220840371)
              ·
                refine ⟨10672189225883655331260557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7114792817255770220840371 10672189225883655331260557)
                ·
                  refine ⟨4002070959706370749222709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10672189225883655331260557 4002070959706370749222709)
                  ·
                    refine ⟨375194152472472257739629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4002070959706370749222709 375194152472472257739629)
                    ·
                      rfl

theorem cell23_2192064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 3, 5].length) (baseStart_2192064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192064 prefixEnd_2192064 := by exact prefixLift 2192064
  have htrace : WordTrace (prefixWord ++ tailWord_2192064) baseStart_2192064 baseEnd_2192064 := by
    simpa [prefixWord, tailWord_2192064, baseEnd_2192064] using wordTrace_append hprefix tailTrace_2192064
  have hstable : (prefixWord ++ tailWord_2192064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192064).length < 2 ^ (prefixWord ++ tailWord_2192064).sum := by decide
  have hdescent : baseEnd_2192064 < baseStart_2192064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192071 : List Nat := [1, 1, 4, 1, 1, 1, 2, 5, 2, 3, 2]
def baseStart_2192071 : Nat := 118140960795 + 2192071 * 2 ^ 59
def prefixEnd_2192071 : Nat := 4983230072969 + 3 ^ 40 * 2192071 * 2
def baseEnd_2192071 : Nat := 1125586051781998245831355

theorem tailTrace_2192071 : CollatzResearch.WordTrace tailWord_2192071 prefixEnd_2192071 1125586051781998245831355 := by
  unfold tailWord_2192071
  simp only [CollatzResearch.WordTrace]
  refine ⟨79951397641508617766320067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53300931761005745177546711 79951397641508617766320067)
  ·
    refine ⟨119927096462262926649480101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79951397641508617766320067 119927096462262926649480101)
    ·
      refine ⟨22486330586674298746777519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119927096462262926649480101 22486330586674298746777519)
      ·
        refine ⟨33729495880011448120166279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22486330586674298746777519 33729495880011448120166279)
        ·
          refine ⟨50594243820017172180249419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33729495880011448120166279 50594243820017172180249419)
          ·
            refine ⟨75891365730025758270374129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50594243820017172180249419 75891365730025758270374129)
            ·
              refine ⟨56918524297519318702780597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75891365730025758270374129 56918524297519318702780597)
              ·
                refine ⟨5336111652892436128385681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56918524297519318702780597 5336111652892436128385681)
                ·
                  refine ⟨4002083739669327096289261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5336111652892436128385681 4002083739669327096289261)
                  ·
                    refine ⟨1500781402375997661108473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4002083739669327096289261 1500781402375997661108473)
                    ·
                      refine ⟨1125586051781998245831355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1500781402375997661108473 1125586051781998245831355)
                      ·
                        rfl

theorem cell23_2192071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 3, 2].length) (baseStart_2192071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192071 prefixEnd_2192071 := by exact prefixLift 2192071
  have htrace : WordTrace (prefixWord ++ tailWord_2192071) baseStart_2192071 baseEnd_2192071 := by
    simpa [prefixWord, tailWord_2192071, baseEnd_2192071] using wordTrace_append hprefix tailTrace_2192071
  have hstable : (prefixWord ++ tailWord_2192071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192071).length < 2 ^ (prefixWord ++ tailWord_2192071).sum := by decide
  have hdescent : baseEnd_2192071 < baseStart_2192071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192085 : List Nat := [1, 3, 2, 5, 2, 1, 1, 2, 6]
def baseStart_2192085 : Nat := 118140960795 + 2192085 * 2 ^ 59
def prefixEnd_2192085 : Nat := 4983230072969 + 3 ^ 40 * 2192085 * 2
def baseEnd_2192085 : Nat := 125065915612351243450699

theorem tailTrace_2192085 : CollatzResearch.WordTrace tailWord_2192085 prefixEnd_2192085 125065915612351243450699 := by
  unfold tailWord_2192085
  simp only [CollatzResearch.WordTrace]
  refine ⟨79951908263457898157329709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53301272175638598771553139 79951908263457898157329709)
  ·
    refine ⟨29981965598796711808998641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79951908263457898157329709 29981965598796711808998641)
    ·
      refine ⟨22486474199097533856748981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29981965598796711808998641 22486474199097533856748981)
      ·
        refine ⟨2108106956165393799070217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22486474199097533856748981 2108106956165393799070217)
        ·
          refine ⟨1581080217124045349302663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2108106956165393799070217 1581080217124045349302663)
          ·
            refine ⟨2371620325686068023953995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1581080217124045349302663 2371620325686068023953995)
            ·
              refine ⟨3557430488529102035930993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2371620325686068023953995 3557430488529102035930993)
              ·
                refine ⟨2668072866396826526948245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3557430488529102035930993 2668072866396826526948245)
                ·
                  refine ⟨125065915612351243450699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2668072866396826526948245 125065915612351243450699)
                  ·
                    rfl

theorem cell23_2192085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 6].length) (baseStart_2192085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192085 prefixEnd_2192085 := by exact prefixLift 2192085
  have htrace : WordTrace (prefixWord ++ tailWord_2192085) baseStart_2192085 baseEnd_2192085 := by
    simpa [prefixWord, tailWord_2192085, baseEnd_2192085] using wordTrace_append hprefix tailTrace_2192085
  have hstable : (prefixWord ++ tailWord_2192085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192085).length < 2 ^ (prefixWord ++ tailWord_2192085).sum := by decide
  have hdescent : baseEnd_2192085 < baseStart_2192085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192107 : List Nat := [1, 1, 1, 1, 2, 4, 1, 12]
def baseStart_2192107 : Nat := 118140960795 + 2192107 * 2 ^ 59
def prefixEnd_2192107 : Nat := 4983230072969 + 3 ^ 40 * 2192107 * 2
def baseEnd_2192107 : Nat := 41689056929094818703007

theorem tailTrace_2192107 : CollatzResearch.WordTrace tailWord_2192107 prefixEnd_2192107 41689056929094818703007 := by
  unfold tailWord_2192107
  simp only [CollatzResearch.WordTrace]
  refine ⟨79952710669378195914630575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53301807112918797276420383 79952710669378195914630575)
  ·
    refine ⟨119929066004067293871945863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79952710669378195914630575 119929066004067293871945863)
    ·
      refine ⟨179893599006100940807918795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119929066004067293871945863 179893599006100940807918795)
      ·
        refine ⟨269840398509151411211878193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179893599006100940807918795 269840398509151411211878193)
        ·
          refine ⟨202380298881863558408908645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269840398509151411211878193 202380298881863558408908645)
          ·
            refine ⟨37946306040349417201670371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 202380298881863558408908645 37946306040349417201670371)
            ·
              refine ⟨56919459060524125802505557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37946306040349417201670371 56919459060524125802505557)
              ·
                refine ⟨41689056929094818703007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 56919459060524125802505557 41689056929094818703007)
                ·
                  rfl

theorem cell23_2192107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 12].length) (baseStart_2192107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192107 prefixEnd_2192107 := by exact prefixLift 2192107
  have htrace : WordTrace (prefixWord ++ tailWord_2192107) baseStart_2192107 baseEnd_2192107 := by
    simpa [prefixWord, tailWord_2192107, baseEnd_2192107] using wordTrace_append hprefix tailTrace_2192107
  have hstable : (prefixWord ++ tailWord_2192107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192107).length < 2 ^ (prefixWord ++ tailWord_2192107).sum := by decide
  have hdescent : baseEnd_2192107 < baseStart_2192107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192111 : List Nat := [1, 1, 2, 1, 5, 4, 1, 1, 1, 6]
def baseStart_2192111 : Nat := 118140960795 + 2192111 * 2 ^ 59
def prefixEnd_2192111 : Nat := 4983230072969 + 3 ^ 40 * 2192111 * 2
def baseEnd_2192111 : Nat := 375202197002726029777057

theorem tailTrace_2192111 : CollatzResearch.WordTrace tailWord_2192111 prefixEnd_2192111 375202197002726029777057 := by
  unfold tailWord_2192111
  simp only [CollatzResearch.WordTrace]
  refine ⟨79952856561363704597776187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53301904374242469731850791 79952856561363704597776187)
  ·
    refine ⟨119929284842045556896664281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79952856561363704597776187 119929284842045556896664281)
    ·
      refine ⟨89946963631534167672498211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119929284842045556896664281 89946963631534167672498211)
      ·
        refine ⟨134920445447301251508747317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89946963631534167672498211 134920445447301251508747317)
        ·
          refine ⟨12648791760684492328945061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134920445447301251508747317 12648791760684492328945061)
          ·
            refine ⟨2371648455128342311677199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12648791760684492328945061 2371648455128342311677199)
            ·
              refine ⟨3557472682692513467515799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2371648455128342311677199 3557472682692513467515799)
              ·
                refine ⟨5336209024038770201273699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3557472682692513467515799 5336209024038770201273699)
                ·
                  refine ⟨8004313536058155301910549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5336209024038770201273699 8004313536058155301910549)
                  ·
                    refine ⟨375202197002726029777057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8004313536058155301910549 375202197002726029777057)
                    ·
                      rfl

theorem cell23_2192111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 6].length) (baseStart_2192111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192111 prefixEnd_2192111 := by exact prefixLift 2192111
  have htrace : WordTrace (prefixWord ++ tailWord_2192111) baseStart_2192111 baseEnd_2192111 := by
    simpa [prefixWord, tailWord_2192111, baseEnd_2192111] using wordTrace_append hprefix tailTrace_2192111
  have hstable : (prefixWord ++ tailWord_2192111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192111).length < 2 ^ (prefixWord ++ tailWord_2192111).sum := by decide
  have hdescent : baseEnd_2192111 < baseStart_2192111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192118 : List Nat := [5, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4]
def baseStart_2192118 : Nat := 118140960795 + 2192118 * 2 ^ 59
def prefixEnd_2192118 : Nat := 4983230072969 + 3 ^ 40 * 2192118 * 2
def baseEnd_2192118 : Nat := 1125610185372759561943639

theorem tailTrace_2192118 : CollatzResearch.WordTrace tailWord_2192118 prefixEnd_2192118 1125610185372759561943639 := by
  unfold tailWord_2192118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4997069492021146549580063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53302074581558896528854005 4997069492021146549580063)
  ·
    refine ⟨7495604238031719824370095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4997069492021146549580063 7495604238031719824370095)
    ·
      refine ⟨11243406357047579736555143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7495604238031719824370095 11243406357047579736555143)
      ·
        refine ⟨16865109535571369604832715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11243406357047579736555143 16865109535571369604832715)
        ·
          refine ⟨25297664303357054407249073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16865109535571369604832715 25297664303357054407249073)
          ·
            refine ⟨18973248227517790805436805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25297664303357054407249073 18973248227517790805436805)
            ·
              refine ⟨3557484042659585776019401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18973248227517790805436805 3557484042659585776019401)
              ·
                refine ⟨2668113031994689332014551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3557484042659585776019401 2668113031994689332014551)
                ·
                  refine ⟨4002169547992033998021827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2668113031994689332014551 4002169547992033998021827)
                  ·
                    refine ⟨6003254321988050997032741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4002169547992033998021827 6003254321988050997032741)
                    ·
                      refine ⟨1125610185372759561943639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6003254321988050997032741 1125610185372759561943639)
                      ·
                        rfl

theorem cell23_2192118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_2192118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192118 prefixEnd_2192118 := by exact prefixLift 2192118
  have htrace : WordTrace (prefixWord ++ tailWord_2192118) baseStart_2192118 baseEnd_2192118 := by
    simpa [prefixWord, tailWord_2192118, baseEnd_2192118] using wordTrace_append hprefix tailTrace_2192118
  have hstable : (prefixWord ++ tailWord_2192118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192118).length < 2 ^ (prefixWord ++ tailWord_2192118).sum := by decide
  have hdescent : baseEnd_2192118 < baseStart_2192118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192124 : List Nat := [2, 2, 2, 1, 3, 3, 1, 9]
def baseStart_2192124 : Nat := 118140960795 + 2192124 * 2 ^ 59
def prefixEnd_2192124 : Nat := 4983230072969 + 3 ^ 40 * 2192124 * 2
def baseEnd_2192124 : Nat := 41689380231729131054393

theorem tailTrace_2192124 : CollatzResearch.WordTrace tailWord_2192124 prefixEnd_2192124 41689380231729131054393 := by
  unfold tailWord_2192124
  simp only [CollatzResearch.WordTrace]
  refine ⟨39976665355158303908999713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53302220473544405211999617 39976665355158303908999713)
  ·
    refine ⟨29982499016368727931749785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39976665355158303908999713 29982499016368727931749785)
    ·
      refine ⟨22486874262276545948812339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29982499016368727931749785 22486874262276545948812339)
      ·
        refine ⟨33730311393414818923218509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22486874262276545948812339 33730311393414818923218509)
        ·
          refine ⟨12648866772530557096206941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33730311393414818923218509 12648866772530557096206941)
          ·
            refine ⟨4743325039698958911077603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12648866772530557096206941 4743325039698958911077603)
            ·
              refine ⟨7114987559548438366616405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4743325039698958911077603 7114987559548438366616405)
              ·
                refine ⟨41689380231729131054393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7114987559548438366616405 41689380231729131054393)
                ·
                  rfl

theorem cell23_2192124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 9].length) (baseStart_2192124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192124 prefixEnd_2192124 := by exact prefixLift 2192124
  have htrace : WordTrace (prefixWord ++ tailWord_2192124) baseStart_2192124 baseEnd_2192124 := by
    simpa [prefixWord, tailWord_2192124, baseEnd_2192124] using wordTrace_append hprefix tailTrace_2192124
  have hstable : (prefixWord ++ tailWord_2192124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192124).length < 2 ^ (prefixWord ++ tailWord_2192124).sum := by decide
  have hdescent : baseEnd_2192124 < baseStart_2192124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192154 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 2, 7]
def baseStart_2192154 : Nat := 118140960795 + 2192154 * 2 ^ 59
def prefixEnd_2192154 : Nat := 4983230072969 + 3 ^ 40 * 2192154 * 2
def baseEnd_2192154 : Nat := 375209556892107140364491

theorem tailTrace_2192154 : CollatzResearch.WordTrace tailWord_2192154 prefixEnd_2192154 375209556892107140364491 := by
  unfold tailWord_2192154
  simp only [CollatzResearch.WordTrace]
  refine ⟨19988606225051980735397879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53302949933471948627727677 19988606225051980735397879)
  ·
    refine ⟨29982909337577971103096819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19988606225051980735397879 29982909337577971103096819)
    ·
      refine ⟨44974364006366956654645229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29982909337577971103096819 44974364006366956654645229)
      ·
        refine ⟨16865386502387608745491961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44974364006366956654645229 16865386502387608745491961)
        ·
          refine ⟨12649039876790706559118971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16865386502387608745491961 12649039876790706559118971)
          ·
            refine ⟨18973559815186059838678457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12649039876790706559118971 18973559815186059838678457)
            ·
              refine ⟨14230169861389544879008843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18973559815186059838678457 14230169861389544879008843)
              ·
                refine ⟨21345254792084317318513265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14230169861389544879008843 21345254792084317318513265)
                ·
                  refine ⟨16008941094063237988884949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21345254792084317318513265 16008941094063237988884949)
                  ·
                    refine ⟨375209556892107140364491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16008941094063237988884949 375209556892107140364491)
                    ·
                      rfl

theorem cell23_2192154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_2192154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192154 prefixEnd_2192154 := by exact prefixLift 2192154
  have htrace : WordTrace (prefixWord ++ tailWord_2192154) baseStart_2192154 baseEnd_2192154 := by
    simpa [prefixWord, tailWord_2192154, baseEnd_2192154] using wordTrace_append hprefix tailTrace_2192154
  have hstable : (prefixWord ++ tailWord_2192154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192154).length < 2 ^ (prefixWord ++ tailWord_2192154).sum := by decide
  have hdescent : baseEnd_2192154 < baseStart_2192154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192178 : List Nat := [3, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2]
def baseStart_2192178 : Nat := 118140960795 + 2192178 * 2 ^ 59
def prefixEnd_2192178 : Nat := 4983230072969 + 3 ^ 40 * 2192178 * 2
def baseEnd_2192178 : Nat := 1125640994212029327193363

theorem tailTrace_2192178 : CollatzResearch.WordTrace tailWord_2192178 prefixEnd_2192178 1125640994212029327193363 := by
  unfold tailWord_2192178
  simp only [CollatzResearch.WordTrace]
  refine ⟨19988825063030243760116297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53303533501413983360310125 19988825063030243760116297)
  ·
    refine ⟨14991618797272682820087223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19988825063030243760116297 14991618797272682820087223)
    ·
      refine ⟨22487428195909024230130835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14991618797272682820087223 22487428195909024230130835)
      ·
        refine ⟨33731142293863536345196253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22487428195909024230130835 33731142293863536345196253)
        ·
          refine ⟨12649178360198826129448595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33731142293863536345196253 12649178360198826129448595)
          ·
            refine ⟨18973767540298239194172893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12649178360198826129448595 18973767540298239194172893)
            ·
              refine ⟨7115162827611839697814835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18973767540298239194172893 7115162827611839697814835)
              ·
                refine ⟨10672744241417759546722253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7115162827611839697814835 10672744241417759546722253)
                ·
                  refine ⟨4002279090531659830020845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10672744241417759546722253 4002279090531659830020845)
                  ·
                    refine ⟨1500854658949372436257817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4002279090531659830020845 1500854658949372436257817)
                    ·
                      refine ⟨1125640994212029327193363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1500854658949372436257817 1125640994212029327193363)
                      ·
                        rfl

theorem cell23_2192178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2].length) (baseStart_2192178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192178 prefixEnd_2192178 := by exact prefixLift 2192178
  have htrace : WordTrace (prefixWord ++ tailWord_2192178) baseStart_2192178 baseEnd_2192178 := by
    simpa [prefixWord, tailWord_2192178, baseEnd_2192178] using wordTrace_append hprefix tailTrace_2192178
  have hstable : (prefixWord ++ tailWord_2192178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192178).length < 2 ^ (prefixWord ++ tailWord_2192178).sum := by decide
  have hdescent : baseEnd_2192178 < baseStart_2192178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192195 : List Nat := [1, 1, 1, 3, 1, 4, 5, 1, 1, 3, 2]
def baseStart_2192195 : Nat := 118140960795 + 2192195 * 2 ^ 59
def prefixEnd_2192195 : Nat := 4983230072969 + 3 ^ 40 * 2192195 * 2
def baseEnd_2192195 : Nat := 1125649723383155760680785

theorem tailTrace_2192195 : CollatzResearch.WordTrace tailWord_2192195 prefixEnd_2192195 1125649723383155760680785 := by
  unfold tailWord_2192195
  simp only [CollatzResearch.WordTrace]
  refine ⟨79955920293059386943834039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53303946862039591295889359 79955920293059386943834039)
  ·
    refine ⟨119933880439589080415751059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79955920293059386943834039 119933880439589080415751059)
    ·
      refine ⟨179900820659383620623626589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119933880439589080415751059 179900820659383620623626589)
      ·
        refine ⟨67462807747268857733859971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179900820659383620623626589 67462807747268857733859971)
        ·
          refine ⟨101194211620903286600789957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67462807747268857733859971 101194211620903286600789957)
          ·
            refine ⟨18973914678919366237648117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101194211620903286600789957 18973914678919366237648117)
            ·
              refine ⟨1778804501148690584779511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18973914678919366237648117 1778804501148690584779511)
              ·
                refine ⟨2668206751723035877169267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1778804501148690584779511 2668206751723035877169267)
                ·
                  refine ⟨4002310127584553815753901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2668206751723035877169267 4002310127584553815753901)
                  ·
                    refine ⟨1500866297844207680907713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4002310127584553815753901 1500866297844207680907713)
                    ·
                      refine ⟨1125649723383155760680785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1500866297844207680907713 1125649723383155760680785)
                      ·
                        rfl

theorem cell23_2192195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 1, 3, 2].length) (baseStart_2192195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192195 prefixEnd_2192195 := by exact prefixLift 2192195
  have htrace : WordTrace (prefixWord ++ tailWord_2192195) baseStart_2192195 baseEnd_2192195 := by
    simpa [prefixWord, tailWord_2192195, baseEnd_2192195] using wordTrace_append hprefix tailTrace_2192195
  have hstable : (prefixWord ++ tailWord_2192195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192195).length < 2 ^ (prefixWord ++ tailWord_2192195).sum := by decide
  have hdescent : baseEnd_2192195 < baseStart_2192195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192208 : List Nat := [2, 1, 1, 1, 1, 4, 2, 3, 4, 2, 2]
def baseStart_2192208 : Nat := 118140960795 + 2192208 * 2 ^ 59
def prefixEnd_2192208 : Nat := 4983230072969 + 3 ^ 40 * 2192208 * 2
def baseEnd_2192208 : Nat := 1125656398631664209818225

theorem tailTrace_2192208 : CollatzResearch.WordTrace tailWord_2192208 prefixEnd_2192208 1125656398631664209818225 := by
  unfold tailWord_2192208
  simp only [CollatzResearch.WordTrace]
  refine ⟨39978197221006145082028639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53304262961341526776038185 39978197221006145082028639)
  ·
    refine ⟨59967295831509217623042959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39978197221006145082028639 59967295831509217623042959)
    ·
      refine ⟨89950943747263826434564439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59967295831509217623042959 89950943747263826434564439)
      ·
        refine ⟨134926415620895739651846659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89950943747263826434564439 134926415620895739651846659)
        ·
          refine ⟨202389623431343609477769989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134926415620895739651846659 202389623431343609477769989)
          ·
            refine ⟨37948054393376926777081873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 202389623431343609477769989 37948054393376926777081873)
            ·
              refine ⟨28461040795032695082811405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37948054393376926777081873 28461040795032695082811405)
              ·
                refine ⟨10672890298137260656054277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28461040795032695082811405 10672890298137260656054277)
                ·
                  refine ⟨2001166930900736373010177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10672890298137260656054277 2001166930900736373010177)
                  ·
                    refine ⟨1500875198175552279757633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2001166930900736373010177 1500875198175552279757633)
                    ·
                      refine ⟨1125656398631664209818225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1500875198175552279757633 1125656398631664209818225)
                      ·
                        rfl

theorem cell23_2192208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 4, 2, 2].length) (baseStart_2192208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192208 prefixEnd_2192208 := by exact prefixLift 2192208
  have htrace : WordTrace (prefixWord ++ tailWord_2192208) baseStart_2192208 baseEnd_2192208 := by
    simpa [prefixWord, tailWord_2192208, baseEnd_2192208] using wordTrace_append hprefix tailTrace_2192208
  have hstable : (prefixWord ++ tailWord_2192208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192208).length < 2 ^ (prefixWord ++ tailWord_2192208).sum := by decide
  have hdescent : baseEnd_2192208 < baseStart_2192208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192231 : List Nat := [1, 1, 5, 1, 2, 3, 1, 2, 7]
def baseStart_2192231 : Nat := 118140960795 + 2192231 * 2 ^ 59
def prefixEnd_2192231 : Nat := 4983230072969 + 3 ^ 40 * 2192231 * 2
def baseEnd_2192231 : Nat := 125074245409635291092291

theorem tailTrace_2192231 : CollatzResearch.WordTrace tailWord_2192231 prefixEnd_2192231 125074245409635291092291 := by
  unfold tailWord_2192231
  simp only [CollatzResearch.WordTrace]
  refine ⟨79957233320928965092144547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53304822213952643394763031 79957233320928965092144547)
  ·
    refine ⟨119935849981393447638216821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79957233320928965092144547 119935849981393447638216821)
    ·
      refine ⟨11243985935755635716082827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119935849981393447638216821 11243985935755635716082827)
      ·
        refine ⟨16865978903633453574124241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11243985935755635716082827 16865978903633453574124241)
        ·
          refine ⟨12649484177725090180593181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16865978903633453574124241 12649484177725090180593181)
          ·
            refine ⟨4743556566646908817722443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12649484177725090180593181 4743556566646908817722443)
            ·
              refine ⟨7115334849970363226583665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4743556566646908817722443 7115334849970363226583665)
              ·
                refine ⟨5336501137477772419937749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7115334849970363226583665 5336501137477772419937749)
                ·
                  refine ⟨125074245409635291092291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5336501137477772419937749 125074245409635291092291)
                  ·
                    rfl

theorem cell23_2192231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 7].length) (baseStart_2192231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192231 prefixEnd_2192231 := by exact prefixLift 2192231
  have htrace : WordTrace (prefixWord ++ tailWord_2192231) baseStart_2192231 baseEnd_2192231 := by
    simpa [prefixWord, tailWord_2192231, baseEnd_2192231] using wordTrace_append hprefix tailTrace_2192231
  have hstable : (prefixWord ++ tailWord_2192231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192231).length < 2 ^ (prefixWord ++ tailWord_2192231).sum := by decide
  have hdescent : baseEnd_2192231 < baseStart_2192231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192381 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 5, 6]
def baseStart_2192381 : Nat := 118140960795 + 2192381 * 2 ^ 59
def prefixEnd_2192381 : Nat := 4983230072969 + 3 ^ 40 * 2192381 * 2
def baseEnd_2192381 : Nat := 375248410261630677651643

theorem tailTrace_2192381 : CollatzResearch.WordTrace tailWord_2192381 prefixEnd_2192381 375248410261630677651643 := by
  unfold tailWord_2192381
  simp only [CollatzResearch.WordTrace]
  refine ⟨79962704270385540710104997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53308469513590360473403331 79962704270385540710104997)
  ·
    refine ⟨14993007050697288883144687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79962704270385540710104997 14993007050697288883144687)
    ·
      refine ⟨22489510576045933324717031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14993007050697288883144687 22489510576045933324717031)
      ·
        refine ⟨33734265864068899987075547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22489510576045933324717031 33734265864068899987075547)
        ·
          refine ⟨50601398796103349980613321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33734265864068899987075547 50601398796103349980613321)
          ·
            refine ⟨37951049097077512485459991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50601398796103349980613321 37951049097077512485459991)
            ·
              refine ⟨56926573645616268728189987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37951049097077512485459991 56926573645616268728189987)
              ·
                refine ⟨85389860468424403092284981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56926573645616268728189987 85389860468424403092284981)
                ·
                  refine ⟨8005299418914787789901717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85389860468424403092284981 8005299418914787789901717)
                  ·
                    refine ⟨375248410261630677651643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8005299418914787789901717 375248410261630677651643)
                    ·
                      rfl

theorem cell23_2192381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_2192381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192381 prefixEnd_2192381 := by exact prefixLift 2192381
  have htrace : WordTrace (prefixWord ++ tailWord_2192381) baseStart_2192381 baseEnd_2192381 := by
    simpa [prefixWord, tailWord_2192381, baseEnd_2192381] using wordTrace_append hprefix tailTrace_2192381
  have hstable : (prefixWord ++ tailWord_2192381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192381).length < 2 ^ (prefixWord ++ tailWord_2192381).sum := by decide
  have hdescent : baseEnd_2192381 < baseStart_2192381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192398 : List Nat := [4, 1, 1, 2, 2, 2, 1, 3, 1, 6]
def baseStart_2192398 : Nat := 118140960795 + 2192398 * 2 ^ 59
def prefixEnd_2192398 : Nat := 4983230072969 + 3 ^ 40 * 2192398 * 2
def baseEnd_2192398 : Nat := 375251319985339488814117

theorem tailTrace_2192398 : CollatzResearch.WordTrace tailWord_2192398 prefixEnd_2192398 375251319985339488814117 := by
  unfold tailWord_2192398
  simp only [CollatzResearch.WordTrace]
  refine ⟨9995415538915494076684231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53308882874215968408982565 9995415538915494076684231)
  ·
    refine ⟨14993123308373241115026347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9995415538915494076684231 14993123308373241115026347)
    ·
      refine ⟨22489684962559861672539521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14993123308373241115026347 22489684962559861672539521)
      ·
        refine ⟨16867263721919896254404641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22489684962559861672539521 16867263721919896254404641)
        ·
          refine ⟨12650447791439922190803481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16867263721919896254404641 12650447791439922190803481)
          ·
            refine ⟨9487835843579941643102611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12650447791439922190803481 9487835843579941643102611)
            ·
              refine ⟨14231753765369912464653917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9487835843579941643102611 14231753765369912464653917)
              ·
                refine ⟨5336907662013717174245219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14231753765369912464653917 5336907662013717174245219)
                ·
                  refine ⟨8005361493020575761367829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5336907662013717174245219 8005361493020575761367829)
                  ·
                    refine ⟨375251319985339488814117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8005361493020575761367829 375251319985339488814117)
                    ·
                      rfl

theorem cell23_2192398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_2192398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192398 prefixEnd_2192398 := by exact prefixLift 2192398
  have htrace : WordTrace (prefixWord ++ tailWord_2192398) baseStart_2192398 baseEnd_2192398 := by
    simpa [prefixWord, tailWord_2192398, baseEnd_2192398] using wordTrace_append hprefix tailTrace_2192398
  have hstable : (prefixWord ++ tailWord_2192398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192398).length < 2 ^ (prefixWord ++ tailWord_2192398).sum := by decide
  have hdescent : baseEnd_2192398 < baseStart_2192398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192401 : List Nat := [1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 6]
def baseStart_2192401 : Nat := 118140960795 + 2192401 * 2 ^ 59
def prefixEnd_2192401 : Nat := 4983230072969 + 3 ^ 40 * 2192401 * 2
def baseEnd_2192401 : Nat := 1125755500397981954704837

theorem tailTrace_2192401 : CollatzResearch.WordTrace tailWord_2192401 prefixEnd_2192401 1125755500397981954704837 := by
  unfold tailWord_2192401
  simp only [CollatzResearch.WordTrace]
  refine ⟨79963433730313084125833057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53308955820208722750555371 79963433730313084125833057)
  ·
    refine ⟨59972575297734813094374793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79963433730313084125833057 59972575297734813094374793)
    ·
      refine ⟨44979431473301109820781095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59972575297734813094374793 44979431473301109820781095)
      ·
        refine ⟨67469147209951664731171643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44979431473301109820781095 67469147209951664731171643)
        ·
          refine ⟨101203720814927497096757465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67469147209951664731171643 101203720814927497096757465)
          ·
            refine ⟨75902790611195622822568099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101203720814927497096757465 75902790611195622822568099)
            ·
              refine ⟨113854185916793434233852149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75902790611195622822568099 113854185916793434233852149)
              ·
                refine ⟨10673829929699384459423639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 113854185916793434233852149 10673829929699384459423639)
                ·
                  refine ⟨16010744894549076689135459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10673829929699384459423639 16010744894549076689135459)
                  ·
                    refine ⟨24016117341823615033703189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16010744894549076689135459 24016117341823615033703189)
                    ·
                      refine ⟨1125755500397981954704837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24016117341823615033703189 1125755500397981954704837)
                      ·
                        rfl

theorem cell23_2192401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_2192401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192401 prefixEnd_2192401 := by exact prefixLift 2192401
  have htrace : WordTrace (prefixWord ++ tailWord_2192401) baseStart_2192401 baseEnd_2192401 := by
    simpa [prefixWord, tailWord_2192401, baseEnd_2192401] using wordTrace_append hprefix tailTrace_2192401
  have hstable : (prefixWord ++ tailWord_2192401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192401).length < 2 ^ (prefixWord ++ tailWord_2192401).sum := by decide
  have hdescent : baseEnd_2192401 < baseStart_2192401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192416 : List Nat := [2, 1, 1, 7, 1, 1, 2, 3, 1, 1, 3]
def baseStart_2192416 : Nat := 118140960795 + 2192416 * 2 ^ 59
def prefixEnd_2192416 : Nat := 4983230072969 + 3 ^ 40 * 2192416 * 2
def baseEnd_2192416 : Nat := 1125763202607799396017269

theorem tailTrace_2192416 : CollatzResearch.WordTrace tailWord_2192416 prefixEnd_2192416 1125763202607799396017269 := by
  unfold tailWord_2192416
  simp only [CollatzResearch.WordTrace]
  refine ⟨39981990412629370843814551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53309320550172494458419401 39981990412629370843814551)
  ·
    refine ⟨59972985618944056265721827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39981990412629370843814551 59972985618944056265721827)
    ·
      refine ⟨89959478428416084398582741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59972985618944056265721827 89959478428416084398582741)
      ·
        refine ⟨2108425275666001978091783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 89959478428416084398582741 2108425275666001978091783)
        ·
          refine ⟨3162637913499002967137675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2108425275666001978091783 3162637913499002967137675)
          ·
            refine ⟨4743956870248504450706513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3162637913499002967137675 4743956870248504450706513)
            ·
              refine ⟨3557967652686378338029885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4743956870248504450706513 3557967652686378338029885)
              ·
                refine ⟨1334237869757391876761207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3557967652686378338029885 1334237869757391876761207)
                ·
                  refine ⟨2001356804636087815141811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1334237869757391876761207 2001356804636087815141811)
                  ·
                    refine ⟨3002035206954131722712717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2001356804636087815141811 3002035206954131722712717)
                    ·
                      refine ⟨1125763202607799396017269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3002035206954131722712717 1125763202607799396017269)
                      ·
                        rfl

theorem cell23_2192416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_2192416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192416 prefixEnd_2192416 := by exact prefixLift 2192416
  have htrace : WordTrace (prefixWord ++ tailWord_2192416) baseStart_2192416 baseEnd_2192416 := by
    simpa [prefixWord, tailWord_2192416, baseEnd_2192416] using wordTrace_append hprefix tailTrace_2192416
  have hstable : (prefixWord ++ tailWord_2192416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192416).length < 2 ^ (prefixWord ++ tailWord_2192416).sum := by decide
  have hdescent : baseEnd_2192416 < baseStart_2192416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192449 : List Nat := [1, 2, 5, 1, 3, 1, 3, 1, 2, 4]
def baseStart_2192449 : Nat := 118140960795 + 2192449 * 2 ^ 59
def prefixEnd_2192449 : Nat := 4983230072969 + 3 ^ 40 * 2192449 * 2
def baseEnd_2192449 : Nat := 375260049156465922301539

theorem tailTrace_2192449 : CollatzResearch.WordTrace tailWord_2192449 prefixEnd_2192449 375260049156465922301539 := by
  unfold tailWord_2192449
  simp only [CollatzResearch.WordTrace]
  refine ⟨79965184434139188323580401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53310122956092792215720267 79965184434139188323580401)
  ·
    refine ⟨59973888325604391242685301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79965184434139188323580401 59973888325604391242685301)
    ·
      refine ⟨5622552030525411679001747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59973888325604391242685301 5622552030525411679001747)
      ·
        refine ⟨8433828045788117518502621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5622552030525411679001747 8433828045788117518502621)
        ·
          refine ⟨3162685517170544069438483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8433828045788117518502621 3162685517170544069438483)
          ·
            refine ⟨4744028275755816104157725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3162685517170544069438483 4744028275755816104157725)
            ·
              refine ⟨1779010603408431039059147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4744028275755816104157725 1779010603408431039059147)
              ·
                refine ⟨2668515905112646558588721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1779010603408431039059147 2668515905112646558588721)
                ·
                  refine ⟨2001386928834484918941541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2668515905112646558588721 2001386928834484918941541)
                  ·
                    refine ⟨375260049156465922301539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2001386928834484918941541 375260049156465922301539)
                    ·
                      rfl

theorem cell23_2192449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_2192449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192449 prefixEnd_2192449 := by exact prefixLift 2192449
  have htrace : WordTrace (prefixWord ++ tailWord_2192449) baseStart_2192449 baseEnd_2192449 := by
    simpa [prefixWord, tailWord_2192449, baseEnd_2192449] using wordTrace_append hprefix tailTrace_2192449
  have hstable : (prefixWord ++ tailWord_2192449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192449).length < 2 ^ (prefixWord ++ tailWord_2192449).sum := by decide
  have hdescent : baseEnd_2192449 < baseStart_2192449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192455 : List Nat := [1, 1, 4, 1, 3, 2, 3, 1, 1, 3, 3]
def baseStart_2192455 : Nat := 118140960795 + 2192455 * 2 ^ 59
def prefixEnd_2192455 : Nat := 4983230072969 + 3 ^ 40 * 2192455 * 2
def baseEnd_2192455 : Nat := 1125783228353324743429589

theorem tailTrace_2192455 : CollatzResearch.WordTrace tailWord_2192455 prefixEnd_2192455 1125783228353324743429589 := by
  unfold tailWord_2192455
  simp only [CollatzResearch.WordTrace]
  refine ⟨79965403272117451348298819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53310268848078300898865879 79965403272117451348298819)
  ·
    refine ⟨119948104908176177022448229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79965403272117451348298819 119948104908176177022448229)
    ·
      refine ⟨22490269670283033191709043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119948104908176177022448229 22490269670283033191709043)
      ·
        refine ⟨33735404505424549787563565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22490269670283033191709043 33735404505424549787563565)
        ·
          refine ⟨12650776689534206170336337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33735404505424549787563565 12650776689534206170336337)
          ·
            refine ⟨9488082517150654627752253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12650776689534206170336337 9488082517150654627752253)
            ·
              refine ⟨3558030943931495485407095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9488082517150654627752253 3558030943931495485407095)
              ·
                refine ⟨5337046415897243228110643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3558030943931495485407095 5337046415897243228110643)
                ·
                  refine ⟨8005569623845864842165965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5337046415897243228110643 8005569623845864842165965)
                  ·
                    refine ⟨3002088608942199315812237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8005569623845864842165965 3002088608942199315812237)
                    ·
                      refine ⟨1125783228353324743429589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3002088608942199315812237 1125783228353324743429589)
                      ·
                        rfl

theorem cell23_2192455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_2192455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192455 prefixEnd_2192455 := by exact prefixLift 2192455
  have htrace : WordTrace (prefixWord ++ tailWord_2192455) baseStart_2192455 baseEnd_2192455 := by
    simpa [prefixWord, tailWord_2192455, baseEnd_2192455] using wordTrace_append hprefix tailTrace_2192455
  have hstable : (prefixWord ++ tailWord_2192455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192455).length < 2 ^ (prefixWord ++ tailWord_2192455).sum := by decide
  have hdescent : baseEnd_2192455 < baseStart_2192455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192465 : List Nat := [1, 2, 2, 1, 3, 1, 2, 3, 3, 3, 2]
def baseStart_2192465 : Nat := 118140960795 + 2192465 * 2 ^ 59
def prefixEnd_2192465 : Nat := 4983230072969 + 3 ^ 40 * 2192465 * 2
def baseEnd_2192465 : Nat := 1125788363159869704304543

theorem tailTrace_2192465 : CollatzResearch.WordTrace tailWord_2192465 prefixEnd_2192465 1125788363159869704304543 := by
  unfold tailWord_2192465
  simp only [CollatzResearch.WordTrace]
  refine ⟨79965768002081223056162849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53310512001387482037441899 79965768002081223056162849)
  ·
    refine ⟨59974326001560917292122137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79965768002081223056162849 59974326001560917292122137)
    ·
      refine ⟨44980744501170687969091603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59974326001560917292122137 44980744501170687969091603)
      ·
        refine ⟨67471116751756031953637405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44980744501170687969091603 67471116751756031953637405)
        ·
          refine ⟨25301668781908511982614027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67471116751756031953637405 25301668781908511982614027)
          ·
            refine ⟨37952503172862767973921041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25301668781908511982614027 37952503172862767973921041)
            ·
              refine ⟨28464377379647075980440781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37952503172862767973921041 28464377379647075980440781)
              ·
                refine ⟨10674141517367653492665293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28464377379647075980440781 10674141517367653492665293)
                ·
                  refine ⟨4002803069012870059749485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10674141517367653492665293 4002803069012870059749485)
                  ·
                    refine ⟨1501051150879826272406057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4002803069012870059749485 1501051150879826272406057)
                    ·
                      refine ⟨1125788363159869704304543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1501051150879826272406057 1125788363159869704304543)
                      ·
                        rfl

theorem cell23_2192465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 3, 2].length) (baseStart_2192465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192465 prefixEnd_2192465 := by exact prefixLift 2192465
  have htrace : WordTrace (prefixWord ++ tailWord_2192465) baseStart_2192465 baseEnd_2192465 := by
    simpa [prefixWord, tailWord_2192465, baseEnd_2192465] using wordTrace_append hprefix tailTrace_2192465
  have hstable : (prefixWord ++ tailWord_2192465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192465).length < 2 ^ (prefixWord ++ tailWord_2192465).sum := by decide
  have hdescent : baseEnd_2192465 < baseStart_2192465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192468 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_2192468 : Nat := 118140960795 + 2192468 * 2 ^ 59
def prefixEnd_2192468 : Nat := 4983230072969 + 3 ^ 40 * 2192468 * 2
def baseEnd_2192468 : Nat := 1125789903601833192567029

theorem tailTrace_2192468 : CollatzResearch.WordTrace tailWord_2192468 prefixEnd_2192468 1125789903601833192567029 := by
  unfold tailWord_2192468
  simp only [CollatzResearch.WordTrace]
  refine ⟨39982938710535177284261029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53310584947380236379014705 39982938710535177284261029)
  ·
    refine ⟨7496801008225345740798943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39982938710535177284261029 7496801008225345740798943)
    ·
      refine ⟨11245201512338018611198415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7496801008225345740798943 11245201512338018611198415)
      ·
        refine ⟨16867802268507027916797623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11245201512338018611198415 16867802268507027916797623)
        ·
          refine ⟨25301703402760541875196435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16867802268507027916797623 25301703402760541875196435)
          ·
            refine ⟨37952555104140812812794653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25301703402760541875196435 37952555104140812812794653)
            ·
              refine ⟨14232208164052804804797995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37952555104140812812794653 14232208164052804804797995)
              ·
                refine ⟨21348312246079207207196993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14232208164052804804797995 21348312246079207207196993)
                ·
                  refine ⟨16011234184559405405397745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21348312246079207207196993 16011234184559405405397745)
                  ·
                    refine ⟨12008425638419554054048309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16011234184559405405397745 12008425638419554054048309)
                    ·
                      refine ⟨1125789903601833192567029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12008425638419554054048309 1125789903601833192567029)
                      ·
                        rfl

theorem cell23_2192468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_2192468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192468 prefixEnd_2192468 := by exact prefixLift 2192468
  have htrace : WordTrace (prefixWord ++ tailWord_2192468) baseStart_2192468 baseEnd_2192468 := by
    simpa [prefixWord, tailWord_2192468, baseEnd_2192468] using wordTrace_append hprefix tailTrace_2192468
  have hstable : (prefixWord ++ tailWord_2192468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192468).length < 2 ^ (prefixWord ++ tailWord_2192468).sum := by decide
  have hdescent : baseEnd_2192468 < baseStart_2192468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192498 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 1, 3, 5]
def baseStart_2192498 : Nat := 118140960795 + 2192498 * 2 ^ 59
def prefixEnd_2192498 : Nat := 4983230072969 + 3 ^ 40 * 2192498 * 2
def baseEnd_2192498 : Nat := 1125805308021468075191891

theorem tailTrace_2192498 : CollatzResearch.WordTrace tailWord_2192498 prefixEnd_2192498 1125805308021468075191891 := by
  unfold tailWord_2192498
  simp only [CollatzResearch.WordTrace]
  refine ⟨19991742902740417423028537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53311314407307779794742765 19991742902740417423028537)
  ·
    refine ⟨14993807177055313067271403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19991742902740417423028537 14993807177055313067271403)
    ·
      refine ⟨22490710765582969600907105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14993807177055313067271403 22490710765582969600907105)
      ·
        refine ⟨16868033074187227200680329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22490710765582969600907105 16868033074187227200680329)
        ·
          refine ⟨12651024805640420400510247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16868033074187227200680329 12651024805640420400510247)
          ·
            refine ⟨18976537208460630600765371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12651024805640420400510247 18976537208460630600765371)
            ·
              refine ⟨28464805812690945901148057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18976537208460630600765371 28464805812690945901148057)
              ·
                refine ⟨21348604359518209425861043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28464805812690945901148057 21348604359518209425861043)
                ·
                  refine ⟨32022906539277314138791565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21348604359518209425861043 32022906539277314138791565)
                  ·
                    refine ⟨12008589952228992802046837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32022906539277314138791565 12008589952228992802046837)
                    ·
                      refine ⟨1125805308021468075191891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12008589952228992802046837 1125805308021468075191891)
                      ·
                        rfl

theorem cell23_2192498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_2192498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192498 prefixEnd_2192498 := by exact prefixLift 2192498
  have htrace : WordTrace (prefixWord ++ tailWord_2192498) baseStart_2192498 baseEnd_2192498 := by
    simpa [prefixWord, tailWord_2192498, baseEnd_2192498] using wordTrace_append hprefix tailTrace_2192498
  have hstable : (prefixWord ++ tailWord_2192498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192498).length < 2 ^ (prefixWord ++ tailWord_2192498).sum := by decide
  have hdescent : baseEnd_2192498 < baseStart_2192498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192508 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 1, 4, 4]
def baseStart_2192508 : Nat := 118140960795 + 2192508 * 2 ^ 59
def prefixEnd_2192508 : Nat := 4983230072969 + 3 ^ 40 * 2192508 * 2
def baseEnd_2192508 : Nat := 1125810442828013036066845

theorem tailTrace_2192508 : CollatzResearch.WordTrace tailWord_2192508 prefixEnd_2192508 1125810442828013036066845 := by
  unfold tailWord_2192508
  simp only [CollatzResearch.WordTrace]
  refine ⟨39983668170462720699989089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53311557560616960933318785 39983668170462720699989089)
  ·
    refine ⟨29987751127847040524991817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39983668170462720699989089 29987751127847040524991817)
    ·
      refine ⟨22490813345885280393743863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29987751127847040524991817 22490813345885280393743863)
      ·
        refine ⟨33736220018827920590615795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22490813345885280393743863 33736220018827920590615795)
        ·
          refine ⟨50604330028241880885923693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33736220018827920590615795 50604330028241880885923693)
          ·
            refine ⟨18976623760590705332221385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50604330028241880885923693 18976623760590705332221385)
            ·
              refine ⟨14232467820443028999166039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18976623760590705332221385 14232467820443028999166039)
              ·
                refine ⟨21348701730664543498749059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14232467820443028999166039 21348701730664543498749059)
                ·
                  refine ⟨32023052595996815248123589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21348701730664543498749059 32023052595996815248123589)
                  ·
                    refine ⟨6004322361749402859023173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32023052595996815248123589 6004322361749402859023173)
                    ·
                      refine ⟨1125810442828013036066845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6004322361749402859023173 1125810442828013036066845)
                      ·
                        rfl

theorem cell23_2192508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_2192508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192508 prefixEnd_2192508 := by exact prefixLift 2192508
  have htrace : WordTrace (prefixWord ++ tailWord_2192508) baseStart_2192508 baseEnd_2192508 := by
    simpa [prefixWord, tailWord_2192508, baseEnd_2192508] using wordTrace_append hprefix tailTrace_2192508
  have hstable : (prefixWord ++ tailWord_2192508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192508).length < 2 ^ (prefixWord ++ tailWord_2192508).sum := by decide
  have hdescent : baseEnd_2192508 < baseStart_2192508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192510 : List Nat := [4, 2, 4, 1, 2, 1, 1, 2, 1, 2, 3]
def baseStart_2192510 : Nat := 118140960795 + 2192510 * 2 ^ 59
def prefixEnd_2192510 : Nat := 4983230072969 + 3 ^ 40 * 2192510 * 2
def baseEnd_2192510 : Nat := 1125811469789322028241837

theorem tailTrace_2192510 : CollatzResearch.WordTrace tailWord_2192510 prefixEnd_2192510 1125811469789322028241837 := by
  unfold tailWord_2192510
  simp only [CollatzResearch.WordTrace]
  refine ⟨9995926160864774467693873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53311606191278797161033989 9995926160864774467693873)
  ·
    refine ⟨7496944620648580850770405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9995926160864774467693873 7496944620648580850770405)
    ·
      refine ⟨1405677116371608909519451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7496944620648580850770405 1405677116371608909519451)
      ·
        refine ⟨2108515674557413364279177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1405677116371608909519451 2108515674557413364279177)
        ·
          refine ⟨1581386755918060023209383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2108515674557413364279177 1581386755918060023209383)
          ·
            refine ⟨2372080133877090034814075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1581386755918060023209383 2372080133877090034814075)
            ·
              refine ⟨3558120200815635052221113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2372080133877090034814075 3558120200815635052221113)
              ·
                refine ⟨2668590150611726289165835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3558120200815635052221113 2668590150611726289165835)
                ·
                  refine ⟨4002885225917589433748753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2668590150611726289165835 4002885225917589433748753)
                  ·
                    refine ⟨3002163919438192075311565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4002885225917589433748753 3002163919438192075311565)
                    ·
                      refine ⟨1125811469789322028241837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3002163919438192075311565 1125811469789322028241837)
                      ·
                        rfl

theorem cell23_2192510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_2192510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192510 prefixEnd_2192510 := by exact prefixLift 2192510
  have htrace : WordTrace (prefixWord ++ tailWord_2192510) baseStart_2192510 baseEnd_2192510 := by
    simpa [prefixWord, tailWord_2192510, baseEnd_2192510] using wordTrace_append hprefix tailTrace_2192510
  have hstable : (prefixWord ++ tailWord_2192510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192510).length < 2 ^ (prefixWord ++ tailWord_2192510).sum := by decide
  have hdescent : baseEnd_2192510 < baseStart_2192510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192528 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 3]
def baseStart_2192528 : Nat := 118140960795 + 2192528 * 2 ^ 59
def prefixEnd_2192528 : Nat := 4983230072969 + 3 ^ 40 * 2192528 * 2
def baseEnd_2192528 : Nat := 1125820712441102957816753

theorem tailTrace_2192528 : CollatzResearch.WordTrace tailWord_2192528 prefixEnd_2192528 1125820712441102957816753 := by
  unfold tailWord_2192528
  simp only [CollatzResearch.WordTrace]
  refine ⟨39984032900426492407853119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53312043867235323210470825 39984032900426492407853119)
  ·
    refine ⟨59976049350639738611779679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39984032900426492407853119 59976049350639738611779679)
    ·
      refine ⟨89964074025959607917669519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59976049350639738611779679 89964074025959607917669519)
      ·
        refine ⟨134946111038939411876504279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89964074025959607917669519 134946111038939411876504279)
        ·
          refine ⟨202419166558409117814756419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134946111038939411876504279 202419166558409117814756419)
          ·
            refine ⟨303628749837613676722134629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202419166558409117814756419 303628749837613676722134629)
            ·
              refine ⟨56930390594552564385400243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 303628749837613676722134629 56930390594552564385400243)
              ·
                refine ⟨85395585891828846578100365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56930390594552564385400243 85395585891828846578100365)
                ·
                  refine ⟨32023344709435817466787637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85395585891828846578100365 32023344709435817466787637)
                  ·
                    refine ⟨3002188566509607887511341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32023344709435817466787637 3002188566509607887511341)
                    ·
                      refine ⟨1125820712441102957816753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3002188566509607887511341 1125820712441102957816753)
                      ·
                        rfl

theorem cell23_2192528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 3].length) (baseStart_2192528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192528 prefixEnd_2192528 := by exact prefixLift 2192528
  have htrace : WordTrace (prefixWord ++ tailWord_2192528) baseStart_2192528 baseEnd_2192528 := by
    simpa [prefixWord, tailWord_2192528, baseEnd_2192528] using wordTrace_append hprefix tailTrace_2192528
  have hstable : (prefixWord ++ tailWord_2192528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192528).length < 2 ^ (prefixWord ++ tailWord_2192528).sum := by decide
  have hdescent : baseEnd_2192528 < baseStart_2192528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192545 : List Nat := [1, 2, 3, 3, 1, 1, 2, 2, 2, 3, 3]
def baseStart_2192545 : Nat := 118140960795 + 2192545 * 2 ^ 59
def prefixEnd_2192545 : Nat := 4983230072969 + 3 ^ 40 * 2192545 * 2
def baseEnd_2192545 : Nat := 1125829441612229391304175

theorem tailTrace_2192545 : CollatzResearch.WordTrace tailWord_2192545 prefixEnd_2192545 1125829441612229391304175 := by
  unfold tailWord_2192545
  simp only [CollatzResearch.WordTrace]
  refine ⟨79968685841791396719075089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53312457227860931146050059 79968685841791396719075089)
  ·
    refine ⟨59976514381343547539306317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79968685841791396719075089 59976514381343547539306317)
    ·
      refine ⟨22491192893003830327239869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59976514381343547539306317 22491192893003830327239869)
      ·
        refine ⟨8434197334876436372714951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22491192893003830327239869 8434197334876436372714951)
        ·
          refine ⟨12651296002314654559072427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8434197334876436372714951 12651296002314654559072427)
          ·
            refine ⟨18976944003471981838608641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12651296002314654559072427 18976944003471981838608641)
            ·
              refine ⟨14232708002603986378956481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18976944003471981838608641 14232708002603986378956481)
              ·
                refine ⟨10674531001952989784217361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14232708002603986378956481 10674531001952989784217361)
                ·
                  refine ⟨8005898251464742338163021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10674531001952989784217361 8005898251464742338163021)
                  ·
                    refine ⟨3002211844299278376811133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8005898251464742338163021 3002211844299278376811133)
                    ·
                      refine ⟨1125829441612229391304175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3002211844299278376811133 1125829441612229391304175)
                      ·
                        rfl

theorem cell23_2192545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_2192545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192545 prefixEnd_2192545 := by exact prefixLift 2192545
  have htrace : WordTrace (prefixWord ++ tailWord_2192545) baseStart_2192545 baseEnd_2192545 := by
    simpa [prefixWord, tailWord_2192545, baseEnd_2192545] using wordTrace_append hprefix tailTrace_2192545
  have hstable : (prefixWord ++ tailWord_2192545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192545).length < 2 ^ (prefixWord ++ tailWord_2192545).sum := by decide
  have hdescent : baseEnd_2192545 < baseStart_2192545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192689 : List Nat := [1, 2, 2, 3, 3, 3, 1, 2, 1, 5]
def baseStart_2192689 : Nat := 118140960795 + 2192689 * 2 ^ 59
def prefixEnd_2192689 : Nat := 4983230072969 + 3 ^ 40 * 2192689 * 2
def baseEnd_2192689 : Nat := 375301127608825609301171

theorem tailTrace_2192689 : CollatzResearch.WordTrace tailWord_2192689 prefixEnd_2192689 375301127608825609301171 := by
  unfold tailWord_2192689
  simp only [CollatzResearch.WordTrace]
  refine ⟨79973937953269709312317121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53315958635513139541544747 79973937953269709312317121)
  ·
    refine ⟨59980453464952281984237841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79973937953269709312317121 59980453464952281984237841)
    ·
      refine ⟨44985340098714211488178381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59980453464952281984237841 44985340098714211488178381)
      ·
        refine ⟨16869502537017829308066893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44985340098714211488178381 16869502537017829308066893)
        ·
          refine ⟨6326063451381685990525085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16869502537017829308066893 6326063451381685990525085)
          ·
            refine ⟨2372273794268132246446907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6326063451381685990525085 2372273794268132246446907)
            ·
              refine ⟨3558410691402198369670361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2372273794268132246446907 3558410691402198369670361)
              ·
                refine ⟨2668808018551648777252771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3558410691402198369670361 2668808018551648777252771)
                ·
                  refine ⟨4003212027827473165879157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2668808018551648777252771 4003212027827473165879157)
                  ·
                    refine ⟨375301127608825609301171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4003212027827473165879157 375301127608825609301171)
                    ·
                      rfl

theorem cell23_2192689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 5].length) (baseStart_2192689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192689 prefixEnd_2192689 := by exact prefixLift 2192689
  have htrace : WordTrace (prefixWord ++ tailWord_2192689) baseStart_2192689 baseEnd_2192689 := by
    simpa [prefixWord, tailWord_2192689, baseEnd_2192689] using wordTrace_append hprefix tailTrace_2192689
  have hstable : (prefixWord ++ tailWord_2192689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192689).length < 2 ^ (prefixWord ++ tailWord_2192689).sum := by decide
  have hdescent : baseEnd_2192689 < baseStart_2192689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192702 : List Nat := [4, 2, 1, 2, 1, 1, 3, 2, 1, 6]
def baseStart_2192702 : Nat := 118140960795 + 2192702 * 2 ^ 59
def prefixEnd_2192702 : Nat := 4983230072969 + 3 ^ 40 * 2192702 * 2
def baseEnd_2192702 : Nat := 375303352691661759013651

theorem tailTrace_2192702 : CollatzResearch.WordTrace tailWord_2192702 prefixEnd_2192702 375303352691661759013651 := by
  unfold tailWord_2192702
  simp only [CollatzResearch.WordTrace]
  refine ⟨9996801512777826566567545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53316274734815075021693573 9996801512777826566567545)
  ·
    refine ⟨7497601134583369924925659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9996801512777826566567545 7497601134583369924925659)
    ·
      refine ⟨11246401701875054887388489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7497601134583369924925659 11246401701875054887388489)
      ·
        refine ⟨8434801276406291165541367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11246401701875054887388489 8434801276406291165541367)
        ·
          refine ⟨12652201914609436748312051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8434801276406291165541367 12652201914609436748312051)
          ·
            refine ⟨18978302871914155122468077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12652201914609436748312051 18978302871914155122468077)
            ·
              refine ⟨7116863576967808170925529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18978302871914155122468077 7116863576967808170925529)
              ·
                refine ⟨5337647682725856128194147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7116863576967808170925529 5337647682725856128194147)
                ·
                  refine ⟨8006471524088784192291221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5337647682725856128194147 8006471524088784192291221)
                  ·
                    refine ⟨375303352691661759013651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8006471524088784192291221 375303352691661759013651)
                    ·
                      rfl

theorem cell23_2192702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_2192702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192702 prefixEnd_2192702 := by exact prefixLift 2192702
  have htrace : WordTrace (prefixWord ++ tailWord_2192702) baseStart_2192702 baseEnd_2192702 := by
    simpa [prefixWord, tailWord_2192702, baseEnd_2192702] using wordTrace_append hprefix tailTrace_2192702
  have hstable : (prefixWord ++ tailWord_2192702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192702).length < 2 ^ (prefixWord ++ tailWord_2192702).sum := by decide
  have hdescent : baseEnd_2192702 < baseStart_2192702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192776 : List Nat := [2, 1, 3, 3, 1, 2, 3, 2, 2, 1, 3]
def baseStart_2192776 : Nat := 118140960795 + 2192776 * 2 ^ 59
def prefixEnd_2192776 : Nat := 4983230072969 + 3 ^ 40 * 2192776 * 2
def baseEnd_2192776 : Nat := 1125948055643417987515613

theorem tailTrace_2192776 : CollatzResearch.WordTrace tailWord_2192776 prefixEnd_2192776 1125948055643417987515613 := by
  unfold tailWord_2192776
  simp only [CollatzResearch.WordTrace]
  refine ⟨39988555551977261585367091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53318074069303015447156121 39988555551977261585367091)
  ·
    refine ⟨59982833327965892378050637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39988555551977261585367091 59982833327965892378050637)
    ·
      refine ⟨22493562497987209641768989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59982833327965892378050637 22493562497987209641768989)
      ·
        refine ⟨8435085936745203615663371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22493562497987209641768989 8435085936745203615663371)
        ·
          refine ⟨12652628905117805423495057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8435085936745203615663371 12652628905117805423495057)
          ·
            refine ⟨9489471678838354067621293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12652628905117805423495057 9489471678838354067621293)
            ·
              refine ⟨3558551879564382775357985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9489471678838354067621293 3558551879564382775357985)
              ·
                refine ⟨2668913909673287081518489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3558551879564382775357985 2668913909673287081518489)
                ·
                  refine ⟨2001685432254965311138867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2668913909673287081518489 2001685432254965311138867)
                  ·
                    refine ⟨3002528148382447966708301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2001685432254965311138867 3002528148382447966708301)
                    ·
                      refine ⟨1125948055643417987515613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3002528148382447966708301 1125948055643417987515613)
                      ·
                        rfl

theorem cell23_2192776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_2192776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192776 prefixEnd_2192776 := by exact prefixLift 2192776
  have htrace : WordTrace (prefixWord ++ tailWord_2192776) baseStart_2192776 baseEnd_2192776 := by
    simpa [prefixWord, tailWord_2192776, baseEnd_2192776] using wordTrace_append hprefix tailTrace_2192776
  have hstable : (prefixWord ++ tailWord_2192776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192776).length < 2 ^ (prefixWord ++ tailWord_2192776).sum := by decide
  have hdescent : baseEnd_2192776 < baseStart_2192776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192785 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 5]
def baseStart_2192785 : Nat := 118140960795 + 2192785 * 2 ^ 59
def prefixEnd_2192785 : Nat := 4983230072969 + 3 ^ 40 * 2192785 * 2
def baseEnd_2192785 : Nat := 1125952676969308452303071

theorem tailTrace_2192785 : CollatzResearch.WordTrace tailWord_2192785 prefixEnd_2192785 1125952676969308452303071 := by
  unfold tailWord_2192785
  simp only [CollatzResearch.WordTrace]
  refine ⟨79977439360921917707811809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53318292907281278471874539 79977439360921917707811809)
  ·
    refine ⟨59983079520691438280858857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79977439360921917707811809 59983079520691438280858857)
    ·
      refine ⟨44987309640518578710644143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59983079520691438280858857 44987309640518578710644143)
      ·
        refine ⟨67480964460777868065966215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44987309640518578710644143 67480964460777868065966215)
        ·
          refine ⟨101221446691166802098949323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67480964460777868065966215 101221446691166802098949323)
          ·
            refine ⟨151832170036750203148423985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101221446691166802098949323 151832170036750203148423985)
            ·
              refine ⟨113874127527562652361317989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151832170036750203148423985 113874127527562652361317989)
              ·
                refine ⟨21351398911417997317747123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113874127527562652361317989 21351398911417997317747123)
                ·
                  refine ⟨32027098367126995976620685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21351398911417997317747123 32027098367126995976620685)
                  ·
                    refine ⟨12010161887672623491232757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32027098367126995976620685 12010161887672623491232757)
                    ·
                      refine ⟨1125952676969308452303071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12010161887672623491232757 1125952676969308452303071)
                      ·
                        rfl

theorem cell23_2192785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_2192785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192785 prefixEnd_2192785 := by exact prefixLift 2192785
  have htrace : WordTrace (prefixWord ++ tailWord_2192785) baseStart_2192785 baseEnd_2192785 := by
    simpa [prefixWord, tailWord_2192785, baseEnd_2192785] using wordTrace_append hprefix tailTrace_2192785
  have hstable : (prefixWord ++ tailWord_2192785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192785).length < 2 ^ (prefixWord ++ tailWord_2192785).sum := by decide
  have hdescent : baseEnd_2192785 < baseStart_2192785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192805 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 9]
def baseStart_2192805 : Nat := 118140960795 + 2192805 * 2 ^ 59
def prefixEnd_2192805 : Nat := 4983230072969 + 3 ^ 40 * 2192805 * 2
def baseEnd_2192805 : Nat := 125106994064710930450331

theorem tailTrace_2192805 : CollatzResearch.WordTrace tailWord_2192805 prefixEnd_2192805 125106994064710930450331 := by
  unfold tailWord_2192805
  simp only [CollatzResearch.WordTrace]
  refine ⟨79978168820849461123539869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53318779213899640749026579 79978168820849461123539869)
  ·
    refine ⟨29991813307818547921327451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79978168820849461123539869 29991813307818547921327451)
    ·
      refine ⟨44987719961727821881991177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29991813307818547921327451 44987719961727821881991177)
      ·
        refine ⟨33740789971295866411493383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44987719961727821881991177 33740789971295866411493383)
        ·
          refine ⟨50611184956943799617240075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33740789971295866411493383 50611184956943799617240075)
          ·
            refine ⟨75916777435415699425860113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50611184956943799617240075 75916777435415699425860113)
            ·
              refine ⟨56937583076561774569395085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75916777435415699425860113 56937583076561774569395085)
              ·
                refine ⟨21351593653710665463523157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56937583076561774569395085 21351593653710665463523157)
                ·
                  refine ⟨125106994064710930450331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21351593653710665463523157 125106994064710930450331)
                  ·
                    rfl

theorem cell23_2192805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 9].length) (baseStart_2192805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192805 prefixEnd_2192805 := by exact prefixLift 2192805
  have htrace : WordTrace (prefixWord ++ tailWord_2192805) baseStart_2192805 baseEnd_2192805 := by
    simpa [prefixWord, tailWord_2192805, baseEnd_2192805] using wordTrace_append hprefix tailTrace_2192805
  have hstable : (prefixWord ++ tailWord_2192805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192805).length < 2 ^ (prefixWord ++ tailWord_2192805).sum := by decide
  have hdescent : baseEnd_2192805 < baseStart_2192805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192832 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 3]
def baseStart_2192832 : Nat := 118140960795 + 2192832 * 2 ^ 59
def prefixEnd_2192832 : Nat := 4983230072969 + 3 ^ 40 * 2192832 * 2
def baseEnd_2192832 : Nat := 1125976810560069768415355

theorem tailTrace_2192832 : CollatzResearch.WordTrace tailWord_2192832 prefixEnd_2192832 1125976810560069768415355 := by
  unfold tailWord_2192832
  simp only [CollatzResearch.WordTrace]
  refine ⟨39989576795875822367386375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53319435727834429823181833 39989576795875822367386375)
  ·
    refine ⟨59984365193813733551079563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39989576795875822367386375 59984365193813733551079563)
    ·
      refine ⟨89976547790720600326619345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59984365193813733551079563 89976547790720600326619345)
      ·
        refine ⟨67482410843040450244964509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89976547790720600326619345 67482410843040450244964509)
        ·
          refine ⟨25305904066140168841861691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67482410843040450244964509 25305904066140168841861691)
          ·
            refine ⟨37958856099210253262792537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25305904066140168841861691 37958856099210253262792537)
            ·
              refine ⟨28469142074407689947094403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37958856099210253262792537 28469142074407689947094403)
              ·
                refine ⟨42703713111611534920641605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28469142074407689947094403 42703713111611534920641605)
                ·
                  refine ⟨8006946208427162797620301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42703713111611534920641605 8006946208427162797620301)
                  ·
                    refine ⟨3002604828160186049107613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8006946208427162797620301 3002604828160186049107613)
                    ·
                      refine ⟨1125976810560069768415355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3002604828160186049107613 1125976810560069768415355)
                      ·
                        rfl

theorem cell23_2192832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 3].length) (baseStart_2192832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192832 prefixEnd_2192832 := by exact prefixLift 2192832
  have htrace : WordTrace (prefixWord ++ tailWord_2192832) baseStart_2192832 baseEnd_2192832 := by
    simpa [prefixWord, tailWord_2192832, baseEnd_2192832] using wordTrace_append hprefix tailTrace_2192832
  have hstable : (prefixWord ++ tailWord_2192832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192832).length < 2 ^ (prefixWord ++ tailWord_2192832).sum := by decide
  have hdescent : baseEnd_2192832 < baseStart_2192832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192869 : List Nat := [1, 3, 1, 5, 1, 1, 1, 3, 2, 5]
def baseStart_2192869 : Nat := 118140960795 + 2192869 * 2 ^ 59
def prefixEnd_2192869 : Nat := 4983230072969 + 3 ^ 40 * 2192869 * 2
def baseEnd_2192869 : Nat := 375331936448095374550895

theorem tailTrace_2192869 : CollatzResearch.WordTrace tailWord_2192869 prefixEnd_2192869 375331936448095374550895 := by
  unfold tailWord_2192869
  simp only [CollatzResearch.WordTrace]
  refine ⟨79980503092617600053869661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53320335395078400035913107 79980503092617600053869661)
  ·
    refine ⟨29992688659731600020201123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79980503092617600053869661 29992688659731600020201123)
    ·
      refine ⟨44989032989597400030301685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29992688659731600020201123 44989032989597400030301685)
      ·
        refine ⟨4217721842774756252840783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44989032989597400030301685 4217721842774756252840783)
        ·
          refine ⟨6326582764162134379261175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4217721842774756252840783 6326582764162134379261175)
          ·
            refine ⟨9489874146243201568891763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6326582764162134379261175 9489874146243201568891763)
            ·
              refine ⟨14234811219364802353337645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9489874146243201568891763 14234811219364802353337645)
              ·
                refine ⟨5338054207261800882501617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14234811219364802353337645 5338054207261800882501617)
                ·
                  refine ⟨4003540655446350661876213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5338054207261800882501617 4003540655446350661876213)
                  ·
                    refine ⟨375331936448095374550895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4003540655446350661876213 375331936448095374550895)
                    ·
                      rfl

theorem cell23_2192869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 5].length) (baseStart_2192869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192869 prefixEnd_2192869 := by exact prefixLift 2192869
  have htrace : WordTrace (prefixWord ++ tailWord_2192869) baseStart_2192869 baseEnd_2192869 := by
    simpa [prefixWord, tailWord_2192869, baseEnd_2192869] using wordTrace_append hprefix tailTrace_2192869
  have hstable : (prefixWord ++ tailWord_2192869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192869).length < 2 ^ (prefixWord ++ tailWord_2192869).sum := by decide
  have hdescent : baseEnd_2192869 < baseStart_2192869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192889 : List Nat := [1, 2, 1, 3, 1, 2, 1, 4, 2, 4, 2]
def baseStart_2192889 : Nat := 118140960795 + 2192889 * 2 ^ 59
def prefixEnd_2192889 : Nat := 4983230072969 + 3 ^ 40 * 2192889 * 2
def baseEnd_2192889 : Nat := 1126006078957376045402593

theorem tailTrace_2192889 : CollatzResearch.WordTrace tailWord_2192889 prefixEnd_2192889 1126006078957376045402593 := by
  unfold tailWord_2192889
  simp only [CollatzResearch.WordTrace]
  refine ⟨79981232552545143469597721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53320821701696762313065147 79981232552545143469597721)
  ·
    refine ⟨59985924414408857602198291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79981232552545143469597721 59985924414408857602198291)
    ·
      refine ⟨89978886621613286403297437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59985924414408857602198291 89978886621613286403297437)
      ·
        refine ⟨33742082483104982401236539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89978886621613286403297437 33742082483104982401236539)
        ·
          refine ⟨50613123724657473601854809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33742082483104982401236539 50613123724657473601854809)
          ·
            refine ⟨37959842793493105201391107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50613123724657473601854809 37959842793493105201391107)
            ·
              refine ⟨56939764190239657802086661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37959842793493105201391107 56939764190239657802086661)
              ·
                refine ⟨10676205785669935837891249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56939764190239657802086661 10676205785669935837891249)
                ·
                  refine ⟨8007154339252451878418437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10676205785669935837891249 8007154339252451878418437)
                  ·
                    refine ⟨1501341438609834727203457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8007154339252451878418437 1501341438609834727203457)
                    ·
                      refine ⟨1126006078957376045402593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1501341438609834727203457 1126006078957376045402593)
                      ·
                        rfl

theorem cell23_2192889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 4, 2].length) (baseStart_2192889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192889 prefixEnd_2192889 := by exact prefixLift 2192889
  have htrace : WordTrace (prefixWord ++ tailWord_2192889) baseStart_2192889 baseEnd_2192889 := by
    simpa [prefixWord, tailWord_2192889, baseEnd_2192889] using wordTrace_append hprefix tailTrace_2192889
  have hstable : (prefixWord ++ tailWord_2192889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192889).length < 2 ^ (prefixWord ++ tailWord_2192889).sum := by decide
  have hdescent : baseEnd_2192889 < baseStart_2192889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192906 : List Nat := [3, 1, 2, 2, 2, 3, 1, 1, 2, 4, 2]
def baseStart_2192906 : Nat := 118140960795 + 2192906 * 2 ^ 59
def prefixEnd_2192906 : Nat := 4983230072969 + 3 ^ 40 * 2192906 * 2
def baseEnd_2192906 : Nat := 1126014808128502478890015

theorem tailTrace_2192906 : CollatzResearch.WordTrace tailWord_2192906 prefixEnd_2192906 1126014808128502478890015 := by
  unfold tailWord_2192906
  simp only [CollatzResearch.WordTrace]
  refine ⟨19995463148370888843241643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53321235062322370248644381 19995463148370888843241643)
  ·
    refine ⟨29993194722556333264862465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19995463148370888843241643 29993194722556333264862465)
    ·
      refine ⟨22494896041917249948646849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29993194722556333264862465 22494896041917249948646849)
      ·
        refine ⟨16871172031437937461485137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22494896041917249948646849 16871172031437937461485137)
        ·
          refine ⟨12653379023578453096113853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16871172031437937461485137 12653379023578453096113853)
          ·
            refine ⟨4745017133841919911042695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12653379023578453096113853 4745017133841919911042695)
            ·
              refine ⟨7117525700762879866564043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4745017133841919911042695 7117525700762879866564043)
              ·
                refine ⟨10676288551144319799846065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7117525700762879866564043 10676288551144319799846065)
                ·
                  refine ⟨8007216413358239849884549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10676288551144319799846065 8007216413358239849884549)
                  ·
                    refine ⟨1501353077504669971853353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8007216413358239849884549 1501353077504669971853353)
                    ·
                      refine ⟨1126014808128502478890015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1501353077504669971853353 1126014808128502478890015)
                      ·
                        rfl

theorem cell23_2192906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_2192906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192906 prefixEnd_2192906 := by exact prefixLift 2192906
  have htrace : WordTrace (prefixWord ++ tailWord_2192906) baseStart_2192906 baseEnd_2192906 := by
    simpa [prefixWord, tailWord_2192906, baseEnd_2192906] using wordTrace_append hprefix tailTrace_2192906
  have hstable : (prefixWord ++ tailWord_2192906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192906).length < 2 ^ (prefixWord ++ tailWord_2192906).sum := by decide
  have hdescent : baseEnd_2192906 < baseStart_2192906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192996 : List Nat := [2, 3, 1, 1, 2, 3, 2, 3, 1, 1, 4]
def baseStart_2192996 : Nat := 118140960795 + 2192996 * 2 ^ 59
def prefixEnd_2192996 : Nat := 4983230072969 + 3 ^ 40 * 2192996 * 2
def baseEnd_2192996 : Nat := 1126061021387407126764601

theorem tailTrace_2192996 : CollatzResearch.WordTrace tailWord_2192996 prefixEnd_2192996 1126061021387407126764601 := by
  unfold tailWord_2192996
  simp only [CollatzResearch.WordTrace]
  refine ⟨39992567581578750371871421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53323423442105000495828561 39992567581578750371871421)
  ·
    refine ⟨14997212843092031389451783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39992567581578750371871421 14997212843092031389451783)
    ·
      refine ⟨22495819264638047084177675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14997212843092031389451783 22495819264638047084177675)
      ·
        refine ⟨33743728896957070626266513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22495819264638047084177675 33743728896957070626266513)
        ·
          refine ⟨25307796672717802969699885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33743728896957070626266513 25307796672717802969699885)
          ·
            refine ⟨9490423752269176113637457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25307796672717802969699885 9490423752269176113637457)
            ·
              refine ⟨7117817814201882085228093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9490423752269176113637457 7117817814201882085228093)
              ·
                refine ⟨2669181680325705781960535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7117817814201882085228093 2669181680325705781960535)
                ·
                  refine ⟨4003772520488558672940803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2669181680325705781960535 4003772520488558672940803)
                  ·
                    refine ⟨6005658780732838009411205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4003772520488558672940803 6005658780732838009411205)
                    ·
                      refine ⟨1126061021387407126764601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6005658780732838009411205 1126061021387407126764601)
                      ·
                        rfl

theorem cell23_2192996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_2192996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192996 prefixEnd_2192996 := by exact prefixLift 2192996
  have htrace : WordTrace (prefixWord ++ tailWord_2192996) baseStart_2192996 baseEnd_2192996 := by
    simpa [prefixWord, tailWord_2192996, baseEnd_2192996] using wordTrace_append hprefix tailTrace_2192996
  have hstable : (prefixWord ++ tailWord_2192996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192996).length < 2 ^ (prefixWord ++ tailWord_2192996).sum := by decide
  have hdescent : baseEnd_2192996 < baseStart_2192996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2192999 : List Nat := [1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_2192999 : Nat := 118140960795 + 2192999 * 2 ^ 59
def prefixEnd_2192999 : Nat := 4983230072969 + 3 ^ 40 * 2192999 * 2
def baseEnd_2192999 : Nat := 1126062561829370615027087

theorem tailTrace_2192999 : CollatzResearch.WordTrace tailWord_2192999 prefixEnd_2192999 1126062561829370615027087 := by
  unfold tailWord_2192999
  simp only [CollatzResearch.WordTrace]
  refine ⟨79985244582146632256102051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53323496388097754837401367 79985244582146632256102051)
  ·
    refine ⟨119977866873219948384153077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79985244582146632256102051 119977866873219948384153077)
    ·
      refine ⟨11247925019364370161014351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119977866873219948384153077 11247925019364370161014351)
      ·
        refine ⟨16871887529046555241521527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11247925019364370161014351 16871887529046555241521527)
        ·
          refine ⟨25307831293569832862282291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16871887529046555241521527 25307831293569832862282291)
          ·
            refine ⟨37961746940354749293423437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25307831293569832862282291 37961746940354749293423437)
            ·
              refine ⟨14235655102633030985033789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37961746940354749293423437 14235655102633030985033789)
              ·
                refine ⟨5338370663487386619387671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14235655102633030985033789 5338370663487386619387671)
                ·
                  refine ⟨8007555995231079929081507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5338370663487386619387671 8007555995231079929081507)
                  ·
                    refine ⟨12011333992846619893622261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8007555995231079929081507 12011333992846619893622261)
                    ·
                      refine ⟨1126062561829370615027087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12011333992846619893622261 1126062561829370615027087)
                      ·
                        rfl

theorem cell23_2192999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_2192999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2192999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2192999 prefixEnd_2192999 := by exact prefixLift 2192999
  have htrace : WordTrace (prefixWord ++ tailWord_2192999) baseStart_2192999 baseEnd_2192999 := by
    simpa [prefixWord, tailWord_2192999, baseEnd_2192999] using wordTrace_append hprefix tailTrace_2192999
  have hstable : (prefixWord ++ tailWord_2192999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2192999).length < 2 ^ (prefixWord ++ tailWord_2192999).sum := by decide
  have hdescent : baseEnd_2192999 < baseStart_2192999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2192999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193070 : List Nat := [4, 1, 4, 1, 3, 1, 1, 8]
def baseStart_2193070 : Nat := 118140960795 + 2193070 * 2 ^ 59
def prefixEnd_2193070 : Nat := 4983230072969 + 3 ^ 40 * 2193070 * 2
def baseEnd_2193070 : Nat := 41707371072438512490343

theorem tailTrace_2193070 : CollatzResearch.WordTrace tailWord_2193070 prefixEnd_2193070 41707371072438512490343 := by
  unfold tailWord_2193070
  simp only [CollatzResearch.WordTrace]
  refine ⟨9998479270611176422742083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53325222776592940921291109 9998479270611176422742083)
  ·
    refine ⟨14997718905916764634113125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9998479270611176422742083 14997718905916764634113125)
    ·
      refine ⟨2812072294859393368896211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14997718905916764634113125 2812072294859393368896211)
      ·
        refine ⟨4218108442289090053344317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2812072294859393368896211 4218108442289090053344317)
        ·
          refine ⟨1581790665858408770004119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4218108442289090053344317 1581790665858408770004119)
          ·
            refine ⟨2372685998787613155006179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1581790665858408770004119 2372685998787613155006179)
            ·
              refine ⟨3559028998181419732509269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2372685998787613155006179 3559028998181419732509269)
              ·
                refine ⟨41707371072438512490343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3559028998181419732509269 41707371072438512490343)
                ·
                  rfl

theorem cell23_2193070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 8].length) (baseStart_2193070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193070 prefixEnd_2193070 := by exact prefixLift 2193070
  have htrace : WordTrace (prefixWord ++ tailWord_2193070) baseStart_2193070 baseEnd_2193070 := by
    simpa [prefixWord, tailWord_2193070, baseEnd_2193070] using wordTrace_append hprefix tailTrace_2193070
  have hstable : (prefixWord ++ tailWord_2193070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193070).length < 2 ^ (prefixWord ++ tailWord_2193070).sum := by decide
  have hdescent : baseEnd_2193070 < baseStart_2193070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193079 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 1, 8]
def baseStart_2193079 : Nat := 118140960795 + 2193079 * 2 ^ 59
def prefixEnd_2193079 : Nat := 4983230072969 + 3 ^ 40 * 2193079 * 2
def baseEnd_2193079 : Nat := 375367880093910100675573

theorem tailTrace_2193079 : CollatzResearch.WordTrace tailWord_2193079 prefixEnd_2193079 375367880093910100675573 := by
  unfold tailWord_2193079
  simp only [CollatzResearch.WordTrace]
  refine ⟨79988162421856805919014291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53325441614571203946009527 79988162421856805919014291)
  ·
    refine ⟨119982243632785208878521437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79988162421856805919014291 119982243632785208878521437)
    ·
      refine ⟨44993341362294453329445539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119982243632785208878521437 44993341362294453329445539)
      ·
        refine ⟨67490012043441679994168309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44993341362294453329445539 67490012043441679994168309)
        ·
          refine ⟨6327188629072657499453279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67490012043441679994168309 6327188629072657499453279)
          ·
            refine ⟨9490782943608986249179919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6327188629072657499453279 9490782943608986249179919)
            ·
              refine ⟨14236174415413479373769879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9490782943608986249179919 14236174415413479373769879)
              ·
                refine ⟨21354261623120219060654819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14236174415413479373769879 21354261623120219060654819)
                ·
                  refine ⟨32031392434680328590982229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21354261623120219060654819 32031392434680328590982229)
                  ·
                    refine ⟨375367880093910100675573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32031392434680328590982229 375367880093910100675573)
                    ·
                      rfl

theorem cell23_2193079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 8].length) (baseStart_2193079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193079 prefixEnd_2193079 := by exact prefixLift 2193079
  have htrace : WordTrace (prefixWord ++ tailWord_2193079) baseStart_2193079 baseEnd_2193079 := by
    simpa [prefixWord, tailWord_2193079, baseEnd_2193079] using wordTrace_append hprefix tailTrace_2193079
  have hstable : (prefixWord ++ tailWord_2193079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193079).length < 2 ^ (prefixWord ++ tailWord_2193079).sum := by decide
  have hdescent : baseEnd_2193079 < baseStart_2193079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193120 : List Nat := [2, 1, 1, 3, 1, 2, 5, 2, 2, 2, 2]
def baseStart_2193120 : Nat := 118140960795 + 2193120 * 2 ^ 59
def prefixEnd_2193120 : Nat := 4983230072969 + 3 ^ 40 * 2193120 * 2
def baseEnd_2193120 : Nat := 1126124692988564641614031

theorem tailTrace_2193120 : CollatzResearch.WordTrace tailWord_2193120 prefixEnd_2193120 1126124692988564641614031 := by
  unfold tailWord_2193120
  simp only [CollatzResearch.WordTrace]
  refine ⟨39994828907354134960628407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53326438543138846614171209 39994828907354134960628407)
  ·
    refine ⟨59992243361031202440942611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39994828907354134960628407 59992243361031202440942611)
    ·
      refine ⟨89988365041546803661413917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59992243361031202440942611 89988365041546803661413917)
      ·
        refine ⟨33745636890580051373030219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89988365041546803661413917 33745636890580051373030219)
        ·
          refine ⟨50618455335870077059545329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33745636890580051373030219 50618455335870077059545329)
          ·
            refine ⟨37963841501902557794658997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50618455335870077059545329 37963841501902557794658997)
            ·
              refine ⟨3559110140803364793249281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37963841501902557794658997 3559110140803364793249281)
              ·
                refine ⟨2669332605602523594936961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3559110140803364793249281 2669332605602523594936961)
                ·
                  refine ⟨2001999454201892696202721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2669332605602523594936961 2001999454201892696202721)
                  ·
                    refine ⟨1501499590651419522152041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2001999454201892696202721 1501499590651419522152041)
                    ·
                      refine ⟨1126124692988564641614031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1501499590651419522152041 1126124692988564641614031)
                      ·
                        rfl

theorem cell23_2193120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 2, 2, 2].length) (baseStart_2193120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193120 prefixEnd_2193120 := by exact prefixLift 2193120
  have htrace : WordTrace (prefixWord ++ tailWord_2193120) baseStart_2193120 baseEnd_2193120 := by
    simpa [prefixWord, tailWord_2193120, baseEnd_2193120] using wordTrace_append hprefix tailTrace_2193120
  have hstable : (prefixWord ++ tailWord_2193120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193120).length < 2 ^ (prefixWord ++ tailWord_2193120).sum := by decide
  have hdescent : baseEnd_2193120 < baseStart_2193120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193137 : List Nat := [1, 2, 2, 2, 2, 4, 3, 1, 2, 2, 2]
def baseStart_2193137 : Nat := 118140960795 + 2193137 * 2 ^ 59
def prefixEnd_2193137 : Nat := 4983230072969 + 3 ^ 40 * 2193137 * 2
def baseEnd_2193137 : Nat := 1126133422159691075101453

theorem tailTrace_2193137 : CollatzResearch.WordTrace tailWord_2193137 prefixEnd_2193137 1126133422159691075101453 := by
  unfold tailWord_2193137
  simp only [CollatzResearch.WordTrace]
  refine ⟨79990277855646681824625665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53326851903764454549750443 79990277855646681824625665)
  ·
    refine ⟨59992708391735011368469249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79990277855646681824625665 59992708391735011368469249)
    ·
      refine ⟨44994531293801258526351937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59992708391735011368469249 44994531293801258526351937)
      ·
        refine ⟨33745898470350943894763953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44994531293801258526351937 33745898470350943894763953)
        ·
          refine ⟨25309423852763207921072965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33745898470350943894763953 25309423852763207921072965)
          ·
            refine ⟨4745516972393101485201181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25309423852763207921072965 4745516972393101485201181)
            ·
              refine ⟨1779568864647413056950443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4745516972393101485201181 1779568864647413056950443)
              ·
                refine ⟨2669353296971119585425665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1779568864647413056950443 2669353296971119585425665)
                ·
                  refine ⟨2002014972728339689069249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2669353296971119585425665 2002014972728339689069249)
                  ·
                    refine ⟨1501511229546254766801937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2002014972728339689069249 1501511229546254766801937)
                    ·
                      refine ⟨1126133422159691075101453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1501511229546254766801937 1126133422159691075101453)
                      ·
                        rfl

theorem cell23_2193137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 2, 2, 2].length) (baseStart_2193137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193137 prefixEnd_2193137 := by exact prefixLift 2193137
  have htrace : WordTrace (prefixWord ++ tailWord_2193137) baseStart_2193137 baseEnd_2193137 := by
    simpa [prefixWord, tailWord_2193137, baseEnd_2193137] using wordTrace_append hprefix tailTrace_2193137
  have hstable : (prefixWord ++ tailWord_2193137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193137).length < 2 ^ (prefixWord ++ tailWord_2193137).sum := by decide
  have hdescent : baseEnd_2193137 < baseStart_2193137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193139 : List Nat := [1, 1, 1, 2, 2, 3, 3, 2, 1, 7]
def baseStart_2193139 : Nat := 118140960795 + 2193139 * 2 ^ 59
def prefixEnd_2193139 : Nat := 4983230072969 + 3 ^ 40 * 2193139 * 2
def baseEnd_2193139 : Nat := 375378149707000022425481

theorem tailTrace_2193139 : CollatzResearch.WordTrace tailWord_2193139 prefixEnd_2193139 375378149707000022425481 := by
  unfold tailWord_2193139
  simp only [CollatzResearch.WordTrace]
  refine ⟨79990350801639436166198471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53326900534426290777465647 79990350801639436166198471)
  ·
    refine ⟨119985526202459154249297707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79990350801639436166198471 119985526202459154249297707)
    ·
      refine ⟨179978289303688731373946561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119985526202459154249297707 179978289303688731373946561)
      ·
        refine ⟨134983716977766548530459921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179978289303688731373946561 134983716977766548530459921)
        ·
          refine ⟨101237787733324911397844941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134983716977766548530459921 101237787733324911397844941)
          ·
            refine ⟨37964170399996841774191853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101237787733324911397844941 37964170399996841774191853)
            ·
              refine ⟨14236563899998815665321945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37964170399996841774191853 14236563899998815665321945)
              ·
                refine ⟨10677422924999111748991459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14236563899998815665321945 10677422924999111748991459)
                ·
                  refine ⟨16016134387498667623487189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10677422924999111748991459 16016134387498667623487189)
                  ·
                    refine ⟨375378149707000022425481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16016134387498667623487189 375378149707000022425481)
                    ·
                      rfl

theorem cell23_2193139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 7].length) (baseStart_2193139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193139 prefixEnd_2193139 := by exact prefixLift 2193139
  have htrace : WordTrace (prefixWord ++ tailWord_2193139) baseStart_2193139 baseEnd_2193139 := by
    simpa [prefixWord, tailWord_2193139, baseEnd_2193139] using wordTrace_append hprefix tailTrace_2193139
  have hstable : (prefixWord ++ tailWord_2193139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193139).length < 2 ^ (prefixWord ++ tailWord_2193139).sum := by decide
  have hdescent : baseEnd_2193139 < baseStart_2193139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193149 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 3, 1, 7]
def baseStart_2193149 : Nat := 118140960795 + 2193149 * 2 ^ 59
def prefixEnd_2193149 : Nat := 4983230072969 + 3 ^ 40 * 2193149 * 2
def baseEnd_2193149 : Nat := 1126139583927545028151397

theorem tailTrace_2193149 : CollatzResearch.WordTrace tailWord_2193149 prefixEnd_2193149 1126139583927545028151397 := by
  unfold tailWord_2193149
  simp only [CollatzResearch.WordTrace]
  refine ⟨79990715531603207874062501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53327143687735471916041667 79990715531603207874062501)
  ·
    refine ⟨14998259162175601476386719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79990715531603207874062501 14998259162175601476386719)
    ·
      refine ⟨22497388743263402214580079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14998259162175601476386719 22497388743263402214580079)
      ·
        refine ⟨33746083114895103321870119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22497388743263402214580079 33746083114895103321870119)
        ·
          refine ⟨50619124672342654982805179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33746083114895103321870119 50619124672342654982805179)
          ·
            refine ⟨75928687008513982474207769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50619124672342654982805179 75928687008513982474207769)
            ·
              refine ⟨56946515256385486855655827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75928687008513982474207769 56946515256385486855655827)
              ·
                refine ⟨85419772884578230283483741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56946515256385486855655827 85419772884578230283483741)
                ·
                  refine ⟨32032414831716836356306403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85419772884578230283483741 32032414831716836356306403)
                  ·
                    refine ⟨48048622247575254534459605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32032414831716836356306403 48048622247575254534459605)
                    ·
                      refine ⟨1126139583927545028151397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48048622247575254534459605 1126139583927545028151397)
                      ·
                        rfl

theorem cell23_2193149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_2193149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193149 prefixEnd_2193149 := by exact prefixLift 2193149
  have htrace : WordTrace (prefixWord ++ tailWord_2193149) baseStart_2193149 baseEnd_2193149 := by
    simpa [prefixWord, tailWord_2193149, baseEnd_2193149] using wordTrace_append hprefix tailTrace_2193149
  have hstable : (prefixWord ++ tailWord_2193149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193149).length < 2 ^ (prefixWord ++ tailWord_2193149).sum := by decide
  have hdescent : baseEnd_2193149 < baseStart_2193149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193156 : List Nat := [2, 3, 2, 2, 1, 2, 2, 1, 1, 7]
def baseStart_2193156 : Nat := 118140960795 + 2193156 * 2 ^ 59
def prefixEnd_2193156 : Nat := 4983230072969 + 3 ^ 40 * 2193156 * 2
def baseEnd_2193156 : Nat := 375381059430708833587955

theorem tailTrace_2193156 : CollatzResearch.WordTrace tailWord_2193156 prefixEnd_2193156 375381059430708833587955 := by
  unfold tailWord_2193156
  simp only [CollatzResearch.WordTrace]
  refine ⟨39995485421288924034783661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53327313895051898713044881 39995485421288924034783661)
  ·
    refine ⟨14998307032983346513043873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39995485421288924034783661 14998307032983346513043873)
    ·
      refine ⟨11248730274737509884782905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14998307032983346513043873 11248730274737509884782905)
      ·
        refine ⟨8436547706053132413587179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11248730274737509884782905 8436547706053132413587179)
        ·
          refine ⟨12654821559079698620380769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8436547706053132413587179 12654821559079698620380769)
          ·
            refine ⟨9491116169309773965285577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12654821559079698620380769 9491116169309773965285577)
            ·
              refine ⟨7118337126982330473964183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9491116169309773965285577 7118337126982330473964183)
              ·
                refine ⟨10677505690473495710946275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7118337126982330473964183 10677505690473495710946275)
                ·
                  refine ⟨16016258535710243566419413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10677505690473495710946275 16016258535710243566419413)
                  ·
                    refine ⟨375381059430708833587955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16016258535710243566419413 375381059430708833587955)
                    ·
                      rfl

theorem cell23_2193156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_2193156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193156 prefixEnd_2193156 := by exact prefixLift 2193156
  have htrace : WordTrace (prefixWord ++ tailWord_2193156) baseStart_2193156 baseEnd_2193156 := by
    simpa [prefixWord, tailWord_2193156, baseEnd_2193156] using wordTrace_append hprefix tailTrace_2193156
  have hstable : (prefixWord ++ tailWord_2193156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193156).length < 2 ^ (prefixWord ++ tailWord_2193156).sum := by decide
  have hdescent : baseEnd_2193156 < baseStart_2193156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193176 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 4, 1, 4]
def baseStart_2193176 : Nat := 118140960795 + 2193176 * 2 ^ 59
def prefixEnd_2193176 : Nat := 4983230072969 + 3 ^ 40 * 2193176 * 2
def baseEnd_2193176 : Nat := 1126153447905216422513773

theorem tailTrace_2193176 : CollatzResearch.WordTrace tailWord_2193176 prefixEnd_2193176 1126153447905216422513773 := by
  unfold tailWord_2193176
  simp only [CollatzResearch.WordTrace]
  refine ⟨39995850151252695742647691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53327800201670260990196921 39995850151252695742647691)
  ·
    refine ⟨59993775226879043613971537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39995850151252695742647691 59993775226879043613971537)
    ·
      refine ⟨44995331420159282710478653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59993775226879043613971537 44995331420159282710478653)
      ·
        refine ⟨16873249282559731016429495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44995331420159282710478653 16873249282559731016429495)
        ·
          refine ⟨25309873923839596524644243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16873249282559731016429495 25309873923839596524644243)
          ·
            refine ⟨37964810885759394786966365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25309873923839596524644243 37964810885759394786966365)
            ·
              refine ⟨14236804082159773045112387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37964810885759394786966365 14236804082159773045112387)
              ·
                refine ⟨21355206123239659567668581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14236804082159773045112387 21355206123239659567668581)
                ·
                  refine ⟨4004101148107436168937859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21355206123239659567668581 4004101148107436168937859)
                  ·
                    refine ⟨6006151722161154253406789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4004101148107436168937859 6006151722161154253406789)
                    ·
                      refine ⟨1126153447905216422513773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6006151722161154253406789 1126153447905216422513773)
                      ·
                        rfl

theorem cell23_2193176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_2193176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193176 prefixEnd_2193176 := by exact prefixLift 2193176
  have htrace : WordTrace (prefixWord ++ tailWord_2193176) baseStart_2193176 baseEnd_2193176 := by
    simpa [prefixWord, tailWord_2193176, baseEnd_2193176] using wordTrace_append hprefix tailTrace_2193176
  have hstable : (prefixWord ++ tailWord_2193176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193176).length < 2 ^ (prefixWord ++ tailWord_2193176).sum := by decide
  have hdescent : baseEnd_2193176 < baseStart_2193176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193179 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 5]
def baseStart_2193179 : Nat := 118140960795 + 2193179 * 2 ^ 59
def prefixEnd_2193179 : Nat := 4983230072969 + 3 ^ 40 * 2193179 * 2
def baseEnd_2193179 : Nat := 1126154988347179910776259

theorem tailTrace_2193179 : CollatzResearch.WordTrace tailWord_2193179 prefixEnd_2193179 1126154988347179910776259 := by
  unfold tailWord_2193179
  simp only [CollatzResearch.WordTrace]
  refine ⟨79991809721494522997654591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53327873147663015331769727 79991809721494522997654591)
  ·
    refine ⟨119987714582241784496481887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79991809721494522997654591 119987714582241784496481887)
    ·
      refine ⟨179981571873362676744722831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119987714582241784496481887 179981571873362676744722831)
      ·
        refine ⟨269972357810044015117084247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179981571873362676744722831 269972357810044015117084247)
        ·
          refine ⟨404958536715066022675626371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269972357810044015117084247 404958536715066022675626371)
          ·
            refine ⟨607437805072599034013439557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404958536715066022675626371 607437805072599034013439557)
            ·
              refine ⟨113894588451112318877519917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 607437805072599034013439557 113894588451112318877519917)
              ·
                refine ⟨42710470669167119579069969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113894588451112318877519917 42710470669167119579069969)
                ·
                  refine ⟨32032853001875339684302477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42710470669167119579069969 32032853001875339684302477)
                  ·
                    refine ⟨12012319875703252381613429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32032853001875339684302477 12012319875703252381613429)
                    ·
                      refine ⟨1126154988347179910776259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12012319875703252381613429 1126154988347179910776259)
                      ·
                        rfl

theorem cell23_2193179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 5].length) (baseStart_2193179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193179 prefixEnd_2193179 := by exact prefixLift 2193179
  have htrace : WordTrace (prefixWord ++ tailWord_2193179) baseStart_2193179 baseEnd_2193179 := by
    simpa [prefixWord, tailWord_2193179, baseEnd_2193179] using wordTrace_append hprefix tailTrace_2193179
  have hstable : (prefixWord ++ tailWord_2193179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193179).length < 2 ^ (prefixWord ++ tailWord_2193179).sum := by decide
  have hdescent : baseEnd_2193179 < baseStart_2193179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193233 : List Nat := [1, 2, 2, 1, 5, 2, 2, 2, 6]
def baseStart_2193233 : Nat := 118140960795 + 2193233 * 2 ^ 59
def prefixEnd_2193233 : Nat := 4983230072969 + 3 ^ 40 * 2193233 * 2
def baseEnd_2193233 : Nat := 125131412922502522166779

theorem tailTrace_2193233 : CollatzResearch.WordTrace tailWord_2193233 prefixEnd_2193233 125131412922502522166779 := by
  unfold tailWord_2193233
  simp only [CollatzResearch.WordTrace]
  refine ⟨79993779263298890220120353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53329186175532593480080235 79993779263298890220120353)
  ·
    refine ⟨59995334447474167665090265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79993779263298890220120353 59995334447474167665090265)
    ·
      refine ⟨44996500835605625748817699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59995334447474167665090265 44996500835605625748817699)
      ·
        refine ⟨67494751253408438623226549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44996500835605625748817699 67494751253408438623226549)
        ·
          refine ⟨6327632930007041120927489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67494751253408438623226549 6327632930007041120927489)
          ·
            refine ⟨4745724697505280840695617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6327632930007041120927489 4745724697505280840695617)
            ·
              refine ⟨3559293523128960630521713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4745724697505280840695617 3559293523128960630521713)
              ·
                refine ⟨2669470142346720472891285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3559293523128960630521713 2669470142346720472891285)
                ·
                  refine ⟨125131412922502522166779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2669470142346720472891285 125131412922502522166779)
                  ·
                    rfl

theorem cell23_2193233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 6].length) (baseStart_2193233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193233 prefixEnd_2193233 := by exact prefixLift 2193233
  have htrace : WordTrace (prefixWord ++ tailWord_2193233) baseStart_2193233 baseEnd_2193233 := by
    simpa [prefixWord, tailWord_2193233, baseEnd_2193233] using wordTrace_append hprefix tailTrace_2193233
  have hstable : (prefixWord ++ tailWord_2193233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193233).length < 2 ^ (prefixWord ++ tailWord_2193233).sum := by decide
  have hdescent : baseEnd_2193233 < baseStart_2193233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193237 : List Nat := [1, 3, 2, 2, 2, 2, 4, 2, 1, 4]
def baseStart_2193237 : Nat := 118140960795 + 2193237 * 2 ^ 59
def prefixEnd_2193237 : Nat := 4983230072969 + 3 ^ 40 * 2193237 * 2
def baseEnd_2193237 : Nat := 375394923408380227950331

theorem tailTrace_2193237 : CollatzResearch.WordTrace tailWord_2193237 prefixEnd_2193237 375394923408380227950331 := by
  unfold tailWord_2193237
  simp only [CollatzResearch.WordTrace]
  refine ⟨79993925155284398903265965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53329283436856265935510643 79993925155284398903265965)
  ·
    refine ⟨29997721933231649588724737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79993925155284398903265965 29997721933231649588724737)
    ·
      refine ⟨22498291449923737191543553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29997721933231649588724737 22498291449923737191543553)
      ·
        refine ⟨16873718587442802893657665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22498291449923737191543553 16873718587442802893657665)
        ·
          refine ⟨12655288940582102170243249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16873718587442802893657665 12655288940582102170243249)
          ·
            refine ⟨9491466705436576627682437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12655288940582102170243249 9491466705436576627682437)
            ·
              refine ⟨1779650007269358117690457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9491466705436576627682437 1779650007269358117690457)
              ·
                refine ⟨1334737505452018588267843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1779650007269358117690457 1334737505452018588267843)
                ·
                  refine ⟨2002106258178027882401765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1334737505452018588267843 2002106258178027882401765)
                  ·
                    refine ⟨375394923408380227950331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2002106258178027882401765 375394923408380227950331)
                    ·
                      rfl

theorem cell23_2193237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_2193237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193237 prefixEnd_2193237 := by exact prefixLift 2193237
  have htrace : WordTrace (prefixWord ++ tailWord_2193237) baseStart_2193237 baseEnd_2193237 := by
    simpa [prefixWord, tailWord_2193237, baseEnd_2193237] using wordTrace_append hprefix tailTrace_2193237
  have hstable : (prefixWord ++ tailWord_2193237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193237).length < 2 ^ (prefixWord ++ tailWord_2193237).sum := by decide
  have hdescent : baseEnd_2193237 < baseStart_2193237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193253 : List Nat := [1, 3, 1, 3, 1, 1, 1, 4, 1, 5, 2]
def baseStart_2193253 : Nat := 118140960795 + 2193253 * 2 ^ 59
def prefixEnd_2193253 : Nat := 4983230072969 + 3 ^ 40 * 2193253 * 2
def baseEnd_2193253 : Nat := 1126192985915612621250919

theorem tailTrace_2193253 : CollatzResearch.WordTrace tailWord_2193253 prefixEnd_2193253 1126192985915612621250919 := by
  unfold tailWord_2193253
  simp only [CollatzResearch.WordTrace]
  refine ⟨79994508723226433635848413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53329672482150955757232275 79994508723226433635848413)
  ·
    refine ⟨29997940771209912613443155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79994508723226433635848413 29997940771209912613443155)
    ·
      refine ⟨44996911156814868920164733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29997940771209912613443155 44996911156814868920164733)
      ·
        refine ⟨16873841683805575845061775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44996911156814868920164733 16873841683805575845061775)
        ·
          refine ⟨25310762525708363767592663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16873841683805575845061775 25310762525708363767592663)
          ·
            refine ⟨37966143788562545651388995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25310762525708363767592663 37966143788562545651388995)
            ·
              refine ⟨56949215682843818477083493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37966143788562545651388995 56949215682843818477083493)
              ·
                refine ⟨10677977940533215964453155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56949215682843818477083493 10677977940533215964453155)
                ·
                  refine ⟨16016966910799823946679733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10677977940533215964453155 16016966910799823946679733)
                  ·
                    refine ⟨1501590647887483495001225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16016966910799823946679733 1501590647887483495001225)
                    ·
                      refine ⟨1126192985915612621250919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1501590647887483495001225 1126192985915612621250919)
                      ·
                        rfl

theorem cell23_2193253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_2193253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193253 prefixEnd_2193253 := by exact prefixLift 2193253
  have htrace : WordTrace (prefixWord ++ tailWord_2193253) baseStart_2193253 baseEnd_2193253 := by
    simpa [prefixWord, tailWord_2193253, baseEnd_2193253] using wordTrace_append hprefix tailTrace_2193253
  have hstable : (prefixWord ++ tailWord_2193253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193253).length < 2 ^ (prefixWord ++ tailWord_2193253).sum := by decide
  have hdescent : baseEnd_2193253 < baseStart_2193253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193256 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_2193256 : Nat := 118140960795 + 2193256 * 2 ^ 59
def prefixEnd_2193256 : Nat := 4983230072969 + 3 ^ 40 * 2193256 * 2
def baseEnd_2193256 : Nat := 1126194526357576109513405

theorem tailTrace_2193256 : CollatzResearch.WordTrace tailWord_2193256 prefixEnd_2193256 1126194526357576109513405 := by
  unfold tailWord_2193256
  simp only [CollatzResearch.WordTrace]
  refine ⟨39997309071107782574103811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53329745428143710098805081 39997309071107782574103811)
  ·
    refine ⟨59995963606661673861155717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39997309071107782574103811 59995963606661673861155717)
    ·
      refine ⟨11249243176249063848966697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59995963606661673861155717 11249243176249063848966697)
      ·
        refine ⟨8436932382186797886725023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11249243176249063848966697 8436932382186797886725023)
        ·
          refine ⟨12655398573280196830087535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8436932382186797886725023 12655398573280196830087535)
          ·
            refine ⟨18983097859920295245131303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12655398573280196830087535 18983097859920295245131303)
            ·
              refine ⟨28474646789880442867696955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18983097859920295245131303 28474646789880442867696955)
              ·
                refine ⟨42711970184820664301545433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28474646789880442867696955 42711970184820664301545433)
                ·
                  refine ⟨32033977638615498226159075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42711970184820664301545433 32033977638615498226159075)
                  ·
                    refine ⟨48050966457923247339238613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32033977638615498226159075 48050966457923247339238613)
                    ·
                      refine ⟨1126194526357576109513405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48050966457923247339238613 1126194526357576109513405)
                      ·
                        rfl

theorem cell23_2193256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_2193256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193256 prefixEnd_2193256 := by exact prefixLift 2193256
  have htrace : WordTrace (prefixWord ++ tailWord_2193256) baseStart_2193256 baseEnd_2193256 := by
    simpa [prefixWord, tailWord_2193256, baseEnd_2193256] using wordTrace_append hprefix tailTrace_2193256
  have hstable : (prefixWord ++ tailWord_2193256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193256).length < 2 ^ (prefixWord ++ tailWord_2193256).sum := by decide
  have hdescent : baseEnd_2193256 < baseStart_2193256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193260 : List Nat := [2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 3]
def baseStart_2193260 : Nat := 118140960795 + 2193260 * 2 ^ 59
def prefixEnd_2193260 : Nat := 4983230072969 + 3 ^ 40 * 2193260 * 2
def baseEnd_2193260 : Nat := 1126196580280194093863387

theorem tailTrace_2193260 : CollatzResearch.WordTrace tailWord_2193260 prefixEnd_2193260 1126196580280194093863387 := by
  unfold tailWord_2193260
  simp only [CollatzResearch.WordTrace]
  refine ⟨39997382017100536915676617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53329842689467382554235489 39997382017100536915676617)
  ·
    refine ⟨29998036512825402686757463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39997382017100536915676617 29998036512825402686757463)
    ·
      refine ⟨44997054769238104030136195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29998036512825402686757463 44997054769238104030136195)
      ·
        refine ⟨67495582153857156045204293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44997054769238104030136195 67495582153857156045204293)
        ·
          refine ⟨12655421653848216758475805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67495582153857156045204293 12655421653848216758475805)
          ·
            refine ⟨4745783120193081284428427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12655421653848216758475805 4745783120193081284428427)
            ·
              refine ⟨7118674680289621926642641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4745783120193081284428427 7118674680289621926642641)
              ·
                refine ⟨5339006010217216444981981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7118674680289621926642641 5339006010217216444981981)
                ·
                  refine ⟨2002127253831456166868243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5339006010217216444981981 2002127253831456166868243)
                  ·
                    refine ⟨3003190880747184250302365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2002127253831456166868243 3003190880747184250302365)
                    ·
                      refine ⟨1126196580280194093863387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3003190880747184250302365 1126196580280194093863387)
                      ·
                        rfl

theorem cell23_2193260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 3].length) (baseStart_2193260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193260 prefixEnd_2193260 := by exact prefixLift 2193260
  have htrace : WordTrace (prefixWord ++ tailWord_2193260) baseStart_2193260 baseEnd_2193260 := by
    simpa [prefixWord, tailWord_2193260, baseEnd_2193260] using wordTrace_append hprefix tailTrace_2193260
  have hstable : (prefixWord ++ tailWord_2193260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193260).length < 2 ^ (prefixWord ++ tailWord_2193260).sum := by decide
  have hdescent : baseEnd_2193260 < baseStart_2193260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193294 : List Nat := [4, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3]
def baseStart_2193294 : Nat := 118140960795 + 2193294 * 2 ^ 59
def prefixEnd_2193294 : Nat := 4983230072969 + 3 ^ 40 * 2193294 * 2
def baseEnd_2193294 : Nat := 1126214038622446960838231

theorem tailTrace_2193294 : CollatzResearch.WordTrace tailWord_2193294 prefixEnd_2193294 1126214038622446960838231 := by
  unfold tailWord_2193294
  simp only [CollatzResearch.WordTrace]
  refine ⟨9999500514509737204761367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53330669410718598425393957 9999500514509737204761367)
  ·
    refine ⟨14999250771764605807142051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9999500514509737204761367 14999250771764605807142051)
    ·
      refine ⟨22498876157646908710713077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14999250771764605807142051 22498876157646908710713077)
      ·
        refine ⟨2109269639779397691629351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22498876157646908710713077 2109269639779397691629351)
        ·
          refine ⟨3163904459669096537444027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2109269639779397691629351 3163904459669096537444027)
          ·
            refine ⟨4745856689503644806166041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3163904459669096537444027 4745856689503644806166041)
            ·
              refine ⟨3559392517127733604624531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4745856689503644806166041 3559392517127733604624531)
              ·
                refine ⟨5339088775691600406936797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3559392517127733604624531 5339088775691600406936797)
                ·
                  refine ⟨2002158290884350152601299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5339088775691600406936797 2002158290884350152601299)
                  ·
                    refine ⟨3003237436326525228901949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2002158290884350152601299 3003237436326525228901949)
                    ·
                      refine ⟨1126214038622446960838231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3003237436326525228901949 1126214038622446960838231)
                      ·
                        rfl

theorem cell23_2193294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_2193294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193294 prefixEnd_2193294 := by exact prefixLift 2193294
  have htrace : WordTrace (prefixWord ++ tailWord_2193294) baseStart_2193294 baseEnd_2193294 := by
    simpa [prefixWord, tailWord_2193294, baseEnd_2193294] using wordTrace_append hprefix tailTrace_2193294
  have hstable : (prefixWord ++ tailWord_2193294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193294).length < 2 ^ (prefixWord ++ tailWord_2193294).sum := by decide
  have hdescent : baseEnd_2193294 < baseStart_2193294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193296 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 4]
def baseStart_2193296 : Nat := 118140960795 + 2193296 * 2 ^ 59
def prefixEnd_2193296 : Nat := 4983230072969 + 3 ^ 40 * 2193296 * 2
def baseEnd_2193296 : Nat := 1126215065583755953013221

theorem tailTrace_2193296 : CollatzResearch.WordTrace tailWord_2193296 prefixEnd_2193296 1126215065583755953013221 := by
  unfold tailWord_2193296
  simp only [CollatzResearch.WordTrace]
  refine ⟨39998038531035325989831871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53330718041380434653109161 39998038531035325989831871)
  ·
    refine ⟨59997057796552988984747807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39998038531035325989831871 59997057796552988984747807)
    ·
      refine ⟨89995586694829483477121711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59997057796552988984747807 89995586694829483477121711)
      ·
        refine ⟨134993380042244225215682567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89995586694829483477121711 134993380042244225215682567)
        ·
          refine ⟨202490070063366337823523851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134993380042244225215682567 202490070063366337823523851)
          ·
            refine ⟨303735105095049506735285777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202490070063366337823523851 303735105095049506735285777)
            ·
              refine ⟨227801328821287130051464333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 303735105095049506735285777 227801328821287130051464333)
              ·
                refine ⟨85425498307982673769299125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227801328821287130051464333 85425498307982673769299125)
                ·
                  refine ⟨8008640466373375665871793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85425498307982673769299125 8008640466373375665871793)
                  ·
                    refine ⟨6006480349780031749403845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8008640466373375665871793 6006480349780031749403845)
                    ·
                      refine ⟨1126215065583755953013221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6006480349780031749403845 1126215065583755953013221)
                      ·
                        rfl

theorem cell23_2193296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 4].length) (baseStart_2193296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193296 prefixEnd_2193296 := by exact prefixLift 2193296
  have htrace : WordTrace (prefixWord ++ tailWord_2193296) baseStart_2193296 baseEnd_2193296 := by
    simpa [prefixWord, tailWord_2193296, baseEnd_2193296] using wordTrace_append hprefix tailTrace_2193296
  have hstable : (prefixWord ++ tailWord_2193296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193296).length < 2 ^ (prefixWord ++ tailWord_2193296).sum := by decide
  have hdescent : baseEnd_2193296 < baseStart_2193296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193303 : List Nat := [1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 5]
def baseStart_2193303 : Nat := 118140960795 + 2193303 * 2 ^ 59
def prefixEnd_2193303 : Nat := 4983230072969 + 3 ^ 40 * 2193303 * 2
def baseEnd_2193303 : Nat := 1126218659948337425625689

theorem tailTrace_2193303 : CollatzResearch.WordTrace tailWord_2193303 prefixEnd_2193303 1126218659948337425625689 := by
  unfold tailWord_2193303
  simp only [CollatzResearch.WordTrace]
  refine ⟨79996332373045292175168563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53330888248696861450112375 79996332373045292175168563)
  ·
    refine ⟨119994498559567938262752845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79996332373045292175168563 119994498559567938262752845)
    ·
      refine ⟨44997936959837976848532317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119994498559567938262752845 44997936959837976848532317)
      ·
        refine ⟨16874226359939241318199619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44997936959837976848532317 16874226359939241318199619)
        ·
          refine ⟨25311339539908861977299429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16874226359939241318199619 25311339539908861977299429)
          ·
            refine ⟨4745876163732911620743643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25311339539908861977299429 4745876163732911620743643)
            ·
              refine ⟨7118814245599367431115465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4745876163732911620743643 7118814245599367431115465)
              ·
                refine ⟨5339110684199525573336599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7118814245599367431115465 5339110684199525573336599)
                ·
                  refine ⟨8008666026299288360004899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5339110684199525573336599 8008666026299288360004899)
                  ·
                    refine ⟨12012999039448932540007349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8008666026299288360004899 12012999039448932540007349)
                    ·
                      refine ⟨1126218659948337425625689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12012999039448932540007349 1126218659948337425625689)
                      ·
                        rfl

theorem cell23_2193303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_2193303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193303 prefixEnd_2193303 := by exact prefixLift 2193303
  have htrace : WordTrace (prefixWord ++ tailWord_2193303) baseStart_2193303 baseEnd_2193303 := by
    simpa [prefixWord, tailWord_2193303, baseEnd_2193303] using wordTrace_append hprefix tailTrace_2193303
  have hstable : (prefixWord ++ tailWord_2193303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193303).length < 2 ^ (prefixWord ++ tailWord_2193303).sum := by decide
  have hdescent : baseEnd_2193303 < baseStart_2193303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193340 : List Nat := [2, 2, 2, 5, 1, 2, 9]
def baseStart_2193340 : Nat := 118140960795 + 2193340 * 2 ^ 59
def prefixEnd_2193340 : Nat := 4983230072969 + 3 ^ 40 * 2193340 * 2
def baseEnd_2193340 : Nat := 13904168626327824455099

theorem tailTrace_2193340 : CollatzResearch.WordTrace tailWord_2193340 prefixEnd_2193340 13904168626327824455099 := by
  unfold tailWord_2193340
  simp only [CollatzResearch.WordTrace]
  refine ⟨39998840936955623747132737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53331787915940831662843649 39998840936955623747132737)
  ·
    refine ⟨29999130702716717810349553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39998840936955623747132737 29999130702716717810349553)
    ·
      refine ⟨22499348027037538357762165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29999130702716717810349553 22499348027037538357762165)
      ·
        refine ⟨2109313877534769221040203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22499348027037538357762165 2109313877534769221040203)
        ·
          refine ⟨3163970816302153831560305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2109313877534769221040203 3163970816302153831560305)
          ·
            refine ⟨2372978112226615373670229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3163970816302153831560305 2372978112226615373670229)
            ·
              refine ⟨13904168626327824455099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2372978112226615373670229 13904168626327824455099)
              ·
                rfl

theorem cell23_2193340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 9].length) (baseStart_2193340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193340 prefixEnd_2193340 := by exact prefixLift 2193340
  have htrace : WordTrace (prefixWord ++ tailWord_2193340) baseStart_2193340 baseEnd_2193340 := by
    simpa [prefixWord, tailWord_2193340, baseEnd_2193340] using wordTrace_append hprefix tailTrace_2193340
  have hstable : (prefixWord ++ tailWord_2193340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193340).length < 2 ^ (prefixWord ++ tailWord_2193340).sum := by decide
  have hdescent : baseEnd_2193340 < baseStart_2193340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193377 : List Nat := [1, 2, 3, 1, 2, 1, 5, 2, 1, 3, 2]
def baseStart_2193377 : Nat := 118140960795 + 2193377 * 2 ^ 59
def prefixEnd_2193377 : Nat := 4983230072969 + 3 ^ 40 * 2193377 * 2
def baseEnd_2193377 : Nat := 1126256657516770136100349

theorem tailTrace_2193377 : CollatzResearch.WordTrace tailWord_2193377 prefixEnd_2193377 1126256657516770136100349 := by
  unfold tailWord_2193377
  simp only [CollatzResearch.WordTrace]
  refine ⟨79999031374777202813362385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53332687583184801875574923 79999031374777202813362385)
  ·
    refine ⟨59999273531082902110021789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79999031374777202813362385 59999273531082902110021789)
    ·
      refine ⟨22499727574156088291258171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59999273531082902110021789 22499727574156088291258171)
      ·
        refine ⟨33749591361234132436887257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22499727574156088291258171 33749591361234132436887257)
        ·
          refine ⟨25312193520925599327665443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33749591361234132436887257 25312193520925599327665443)
          ·
            refine ⟨37968290281388398991498165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25312193520925599327665443 37968290281388398991498165)
            ·
              refine ⟨3559527213880162405452953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37968290281388398991498165 3559527213880162405452953)
              ·
                refine ⟨2669645410410121804089715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3559527213880162405452953 2669645410410121804089715)
                ·
                  refine ⟨4004468115615182706134573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2669645410410121804089715 4004468115615182706134573)
                  ·
                    refine ⟨1501675543355693514800465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4004468115615182706134573 1501675543355693514800465)
                    ·
                      refine ⟨1126256657516770136100349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1501675543355693514800465 1126256657516770136100349)
                      ·
                        rfl

theorem cell23_2193377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 3, 2].length) (baseStart_2193377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193377 prefixEnd_2193377 := by exact prefixLift 2193377
  have htrace : WordTrace (prefixWord ++ tailWord_2193377) baseStart_2193377 baseEnd_2193377 := by
    simpa [prefixWord, tailWord_2193377, baseEnd_2193377] using wordTrace_append hprefix tailTrace_2193377
  have hstable : (prefixWord ++ tailWord_2193377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193377).length < 2 ^ (prefixWord ++ tailWord_2193377).sum := by decide
  have hdescent : baseEnd_2193377 < baseStart_2193377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193443 : List Nat := [1, 1, 1, 4, 3, 1, 3, 1, 1, 7]
def baseStart_2193443 : Nat := 118140960795 + 2193443 * 2 ^ 59
def prefixEnd_2193443 : Nat := 4983230072969 + 3 ^ 40 * 2193443 * 2
def baseEnd_2193443 : Nat := 375430182413322292625015

theorem tailTrace_2193443 : CollatzResearch.WordTrace tailWord_2193443 prefixEnd_2193443 375430182413322292625015 := by
  unfold tailWord_2193443
  simp only [CollatzResearch.WordTrace]
  refine ⟨80001438592538096085264983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53334292395025397390176655 80001438592538096085264983)
  ·
    refine ⟨120002157888807144127897475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80001438592538096085264983 120002157888807144127897475)
    ·
      refine ⟨180003236833210716191846213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120002157888807144127897475 180003236833210716191846213)
      ·
        refine ⟨33750606906227009285971165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 180003236833210716191846213 33750606906227009285971165)
        ·
          refine ⟨12656477589835128482239187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33750606906227009285971165 12656477589835128482239187)
          ·
            refine ⟨18984716384752692723358781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12656477589835128482239187 18984716384752692723358781)
            ·
              refine ⟨7119268644282259771259543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18984716384752692723358781 7119268644282259771259543)
              ·
                refine ⟨10678902966423389656889315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7119268644282259771259543 10678902966423389656889315)
                ·
                  refine ⟨16018354449635084485333973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10678902966423389656889315 16018354449635084485333973)
                  ·
                    refine ⟨375430182413322292625015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16018354449635084485333973 375430182413322292625015)
                    ·
                      rfl

theorem cell23_2193443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 7].length) (baseStart_2193443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193443 prefixEnd_2193443 := by exact prefixLift 2193443
  have htrace : WordTrace (prefixWord ++ tailWord_2193443) baseStart_2193443 baseEnd_2193443 := by
    simpa [prefixWord, tailWord_2193443, baseEnd_2193443] using wordTrace_append hprefix tailTrace_2193443
  have hstable : (prefixWord ++ tailWord_2193443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193443).length < 2 ^ (prefixWord ++ tailWord_2193443).sum := by decide
  have hdescent : baseEnd_2193443 < baseStart_2193443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193480 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 1, 6, 2]
def baseStart_2193480 : Nat := 118140960795 + 2193480 * 2 ^ 59
def prefixEnd_2193480 : Nat := 4983230072969 + 3 ^ 40 * 2193480 * 2
def baseEnd_2193480 : Nat := 1126309546024183233112375

theorem tailTrace_2193480 : CollatzResearch.WordTrace tailWord_2193480 prefixEnd_2193480 1126309546024183233112375 := by
  unfold tailWord_2193480
  simp only [CollatzResearch.WordTrace]
  refine ⟨40001394046702025702180947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53335192062269367602907929 40001394046702025702180947)
  ·
    refine ⟨60002091070053038553271421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40001394046702025702180947 60002091070053038553271421)
    ·
      refine ⟨22500784151269889457476783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60002091070053038553271421 22500784151269889457476783)
      ·
        refine ⟨33751176226904834186215175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22500784151269889457476783 33751176226904834186215175)
        ·
          refine ⟨50626764340357251279322763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33751176226904834186215175 50626764340357251279322763)
          ·
            refine ⟨75940146510535876918984145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50626764340357251279322763 75940146510535876918984145)
            ·
              refine ⟨56955109882901907689238109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75940146510535876918984145 56955109882901907689238109)
              ·
                refine ⟨21358166206088215383464291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56955109882901907689238109 21358166206088215383464291)
                ·
                  refine ⟨32037249309132323075196437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21358166206088215383464291 32037249309132323075196437)
                  ·
                    refine ⟨1501746061365577644149833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32037249309132323075196437 1501746061365577644149833)
                    ·
                      refine ⟨1126309546024183233112375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1501746061365577644149833 1126309546024183233112375)
                      ·
                        rfl

theorem cell23_2193480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 1, 6, 2].length) (baseStart_2193480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193480 prefixEnd_2193480 := by exact prefixLift 2193480
  have htrace : WordTrace (prefixWord ++ tailWord_2193480) baseStart_2193480 baseEnd_2193480 := by
    simpa [prefixWord, tailWord_2193480, baseEnd_2193480] using wordTrace_append hprefix tailTrace_2193480
  have hstable : (prefixWord ++ tailWord_2193480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193480).length < 2 ^ (prefixWord ++ tailWord_2193480).sum := by decide
  have hdescent : baseEnd_2193480 < baseStart_2193480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193517 : List Nat := [1, 5, 1, 1, 2, 1, 3, 2, 2, 2, 3]
def baseStart_2193517 : Nat := 118140960795 + 2193517 * 2 ^ 59
def prefixEnd_2193517 : Nat := 4983230072969 + 3 ^ 40 * 2193517 * 2
def baseEnd_2193517 : Nat := 1126328544808399588349705

theorem tailTrace_2193517 : CollatzResearch.WordTrace tailWord_2193517 prefixEnd_2193517 1126328544808399588349705 := by
  unfold tailWord_2193517
  simp only [CollatzResearch.WordTrace]
  refine ⟨80004137594270006723458805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53336091729513337815639203 80004137594270006723458805)
  ·
    refine ⟨7500387899462813130324263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80004137594270006723458805 7500387899462813130324263)
    ·
      refine ⟨11250581849194219695486395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7500387899462813130324263 11250581849194219695486395)
      ·
        refine ⟨16875872773791329543229593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11250581849194219695486395 16875872773791329543229593)
        ·
          refine ⟨12656904580343497157422195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16875872773791329543229593 12656904580343497157422195)
          ·
            refine ⟨18985356870515245736133293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12656904580343497157422195 18985356870515245736133293)
            ·
              refine ⟨7119508826443217151049985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18985356870515245736133293 7119508826443217151049985)
              ·
                refine ⟨5339631619832412863287489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7119508826443217151049985 5339631619832412863287489)
                ·
                  refine ⟨4004723714874309647465617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5339631619832412863287489 4004723714874309647465617)
                  ·
                    refine ⟨3003542786155732235599213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4004723714874309647465617 3003542786155732235599213)
                    ·
                      refine ⟨1126328544808399588349705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3003542786155732235599213 1126328544808399588349705)
                      ·
                        rfl

theorem cell23_2193517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_2193517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193517 prefixEnd_2193517 := by exact prefixLift 2193517
  have htrace : WordTrace (prefixWord ++ tailWord_2193517) baseStart_2193517 baseEnd_2193517 := by
    simpa [prefixWord, tailWord_2193517, baseEnd_2193517] using wordTrace_append hprefix tailTrace_2193517
  have hstable : (prefixWord ++ tailWord_2193517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193517).length < 2 ^ (prefixWord ++ tailWord_2193517).sum := by decide
  have hdescent : baseEnd_2193517 < baseStart_2193517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193537 : List Nat := [1, 2, 4, 2, 3, 1, 1, 3, 6]
def baseStart_2193537 : Nat := 118140960795 + 2193537 * 2 ^ 59
def prefixEnd_2193537 : Nat := 4983230072969 + 3 ^ 40 * 2193537 * 2
def baseEnd_2193537 : Nat := 125148757157943278899957

theorem tailTrace_2193537 : CollatzResearch.WordTrace tailWord_2193537 prefixEnd_2193537 125148757157943278899957 := by
  unfold tailWord_2193537
  simp only [CollatzResearch.WordTrace]
  refine ⟨80004867054197550139186865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53336578036131700092791243 80004867054197550139186865)
  ·
    refine ⟨60003650290648162604390149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80004867054197550139186865 60003650290648162604390149)
    ·
      refine ⟨11250684429496530488323153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60003650290648162604390149 11250684429496530488323153)
      ·
        refine ⟨8438013322122397866242365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11250684429496530488323153 8438013322122397866242365)
        ·
          refine ⟨3164254995795899199840887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8438013322122397866242365 3164254995795899199840887)
          ·
            refine ⟨4746382493693848799761331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3164254995795899199840887 4746382493693848799761331)
            ·
              refine ⟨7119573740540773199641997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4746382493693848799761331 7119573740540773199641997)
              ·
                refine ⟨2669840152702789949865749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7119573740540773199641997 2669840152702789949865749)
                ·
                  refine ⟨125148757157943278899957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2669840152702789949865749 125148757157943278899957)
                  ·
                    rfl

theorem cell23_2193537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 6].length) (baseStart_2193537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193537 prefixEnd_2193537 := by exact prefixLift 2193537
  have htrace : WordTrace (prefixWord ++ tailWord_2193537) baseStart_2193537 baseEnd_2193537 := by
    simpa [prefixWord, tailWord_2193537, baseEnd_2193537] using wordTrace_append hprefix tailTrace_2193537
  have hstable : (prefixWord ++ tailWord_2193537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193537).length < 2 ^ (prefixWord ++ tailWord_2193537).sum := by decide
  have hdescent : baseEnd_2193537 < baseStart_2193537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193575 : List Nat := [1, 1, 6, 2, 3, 1, 2, 2, 1, 4]
def baseStart_2193575 : Nat := 118140960795 + 2193575 * 2 ^ 59
def prefixEnd_2193575 : Nat := 4983230072969 + 3 ^ 40 * 2193575 * 2
def baseEnd_2193575 : Nat := 375452775562120120474813

theorem tailTrace_2193575 : CollatzResearch.WordTrace tailWord_2193575 prefixEnd_2193575 375452775562120120474813 := by
  unfold tailWord_2193575
  simp only [CollatzResearch.WordTrace]
  refine ⟨80006253028059882629070179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53337502018706588419380119 80006253028059882629070179)
  ·
    refine ⟨120009379542089823943605269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80006253028059882629070179 120009379542089823943605269)
    ·
      refine ⟨5625439666035460497356497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 120009379542089823943605269 5625439666035460497356497)
      ·
        refine ⟨4219079749526595373017373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5625439666035460497356497 4219079749526595373017373)
        ·
          refine ⟨1582154906072473264881515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4219079749526595373017373 1582154906072473264881515)
          ·
            refine ⟨2373232359108709897322273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1582154906072473264881515 2373232359108709897322273)
            ·
              refine ⟨1779924269331532422991705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2373232359108709897322273 1779924269331532422991705)
              ·
                refine ⟨1334943201998649317243779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1779924269331532422991705 1334943201998649317243779)
                ·
                  refine ⟨2002414802997973975865669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1334943201998649317243779 2002414802997973975865669)
                  ·
                    refine ⟨375452775562120120474813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2002414802997973975865669 375452775562120120474813)
                    ·
                      rfl

theorem cell23_2193575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_2193575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193575 prefixEnd_2193575 := by exact prefixLift 2193575
  have htrace : WordTrace (prefixWord ++ tailWord_2193575) baseStart_2193575 baseEnd_2193575 := by
    simpa [prefixWord, tailWord_2193575, baseEnd_2193575] using wordTrace_append hprefix tailTrace_2193575
  have hstable : (prefixWord ++ tailWord_2193575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193575).length < 2 ^ (prefixWord ++ tailWord_2193575).sum := by decide
  have hdescent : baseEnd_2193575 < baseStart_2193575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193580 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 8, 4]
def baseStart_2193580 : Nat := 118140960795 + 2193580 * 2 ^ 59
def prefixEnd_2193580 : Nat := 4983230072969 + 3 ^ 40 * 2193580 * 2
def baseEnd_2193580 : Nat := 375453631363210947287305

theorem tailTrace_2193580 : CollatzResearch.WordTrace tailWord_2193580 prefixEnd_2193580 375453631363210947287305 := by
  unfold tailWord_2193580
  simp only [CollatzResearch.WordTrace]
  refine ⟨40003217696520884241501097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53337623595361178988668129 40003217696520884241501097)
  ·
    refine ⟨30002413272390663181125823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40003217696520884241501097 30002413272390663181125823)
    ·
      refine ⟨45003619908585994771688735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30002413272390663181125823 45003619908585994771688735)
      ·
        refine ⟨67505429862878992157533103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45003619908585994771688735 67505429862878992157533103)
        ·
          refine ⟨101258144794318488236299655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67505429862878992157533103 101258144794318488236299655)
          ·
            refine ⟨151887217191477732354449483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101258144794318488236299655 151887217191477732354449483)
            ·
              refine ⟨227830825787216598531674225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151887217191477732354449483 227830825787216598531674225)
              ·
                refine ⟨170873119340412448898755669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227830825787216598531674225 170873119340412448898755669)
                ·
                  refine ⟨2002419367270458385532293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 170873119340412448898755669 2002419367270458385532293)
                  ·
                    refine ⟨375453631363210947287305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2002419367270458385532293 375453631363210947287305)
                    ·
                      rfl

theorem cell23_2193580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 4].length) (baseStart_2193580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193580 prefixEnd_2193580 := by exact prefixLift 2193580
  have htrace : WordTrace (prefixWord ++ tailWord_2193580) baseStart_2193580 baseEnd_2193580 := by
    simpa [prefixWord, tailWord_2193580, baseEnd_2193580] using wordTrace_append hprefix tailTrace_2193580
  have hstable : (prefixWord ++ tailWord_2193580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193580).length < 2 ^ (prefixWord ++ tailWord_2193580).sum := by decide
  have hdescent : baseEnd_2193580 < baseStart_2193580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193624 : List Nat := [2, 1, 2, 2, 4, 2, 1, 3, 1, 2, 3]
def baseStart_2193624 : Nat := 118140960795 + 2193624 * 2 ^ 59
def prefixEnd_2193624 : Nat := 4983230072969 + 3 ^ 40 * 2193624 * 2
def baseEnd_2193624 : Nat := 1126383487238430669711713

theorem tailTrace_2193624 : CollatzResearch.WordTrace tailWord_2193624 prefixEnd_2193624 1126383487238430669711713 := by
  unfold tailWord_2193624
  simp only [CollatzResearch.WordTrace]
  refine ⟨40004020102441181998801963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53338693469921575998402617 40004020102441181998801963)
  ·
    refine ⟨60006030153661772998202945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40004020102441181998801963 60006030153661772998202945)
    ·
      refine ⟨45004522615246329748652209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60006030153661772998202945 45004522615246329748652209)
      ·
        refine ⟨33753391961434747311489157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45004522615246329748652209 33753391961434747311489157)
        ·
          refine ⟨6328760992769015120904217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33753391961434747311489157 6328760992769015120904217)
          ·
            refine ⟨4746570744576761340678163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6328760992769015120904217 4746570744576761340678163)
            ·
              refine ⟨7119856116865142011017245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4746570744576761340678163 7119856116865142011017245)
              ·
                refine ⟨2669946043824428254131467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7119856116865142011017245 2669946043824428254131467)
                ·
                  refine ⟨4004919065736642381197201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2669946043824428254131467 4004919065736642381197201)
                  ·
                    refine ⟨3003689299302481785897901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4004919065736642381197201 3003689299302481785897901)
                    ·
                      refine ⟨1126383487238430669711713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3003689299302481785897901 1126383487238430669711713)
                      ·
                        rfl

theorem cell23_2193624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_2193624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193624 prefixEnd_2193624 := by exact prefixLift 2193624
  have htrace : WordTrace (prefixWord ++ tailWord_2193624) baseStart_2193624 baseEnd_2193624 := by
    simpa [prefixWord, tailWord_2193624, baseEnd_2193624] using wordTrace_append hprefix tailTrace_2193624
  have hstable : (prefixWord ++ tailWord_2193624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193624).length < 2 ^ (prefixWord ++ tailWord_2193624).sum := by decide
  have hdescent : baseEnd_2193624 < baseStart_2193624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193654 : List Nat := [5, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3]
def baseStart_2193654 : Nat := 118140960795 + 2193654 * 2 ^ 59
def prefixEnd_2193654 : Nat := 4983230072969 + 3 ^ 40 * 2193654 * 2
def baseEnd_2193654 : Nat := 1126398891658065552336575

theorem tailTrace_2193654 : CollatzResearch.WordTrace tailWord_2193654 prefixEnd_2193654 1126398891658065552336575 := by
  unfold tailWord_2193654
  simp only [CollatzResearch.WordTrace]
  refine ⟨5000570899673354945074751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53339422929849119414130677 5000570899673354945074751)
  ·
    refine ⟨7500856349510032417612127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5000570899673354945074751 7500856349510032417612127)
    ·
      refine ⟨11251284524265048626418191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7500856349510032417612127 11251284524265048626418191)
      ·
        refine ⟨16876926786397572939627287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11251284524265048626418191 16876926786397572939627287)
        ·
          refine ⟨25315390179596359409440931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16876926786397572939627287 25315390179596359409440931)
          ·
            refine ⟨37973085269394539114161397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25315390179596359409440931 37973085269394539114161397)
            ·
              refine ⟨3559976744005738041952631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37973085269394539114161397 3559976744005738041952631)
              ·
                refine ⟨5339965116008607062928947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3559976744005738041952631 5339965116008607062928947)
                ·
                  refine ⟨8009947674012910594393421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5339965116008607062928947 8009947674012910594393421)
                  ·
                    refine ⟨3003730377754841472897533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8009947674012910594393421 3003730377754841472897533)
                    ·
                      refine ⟨1126398891658065552336575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3003730377754841472897533 1126398891658065552336575)
                      ·
                        rfl

theorem cell23_2193654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_2193654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193654 prefixEnd_2193654 := by exact prefixLift 2193654
  have htrace : WordTrace (prefixWord ++ tailWord_2193654) baseStart_2193654 baseEnd_2193654 := by
    simpa [prefixWord, tailWord_2193654, baseEnd_2193654] using wordTrace_append hprefix tailTrace_2193654
  have hstable : (prefixWord ++ tailWord_2193654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193654).length < 2 ^ (prefixWord ++ tailWord_2193654).sum := by decide
  have hdescent : baseEnd_2193654 < baseStart_2193654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193664 : List Nat := [2, 1, 1, 2, 1, 1, 5, 4, 1, 3, 2]
def baseStart_2193664 : Nat := 118140960795 + 2193664 * 2 ^ 59
def prefixEnd_2193664 : Nat := 4983230072969 + 3 ^ 40 * 2193664 * 2
def baseEnd_2193664 : Nat := 1126404026464610513211529

theorem tailTrace_2193664 : CollatzResearch.WordTrace tailWord_2193664 prefixEnd_2193664 1126404026464610513211529 := by
  unfold tailWord_2193664
  simp only [CollatzResearch.WordTrace]
  refine ⟨40004749562368725414530023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53339666083158300552706697 40004749562368725414530023)
  ·
    refine ⟨60007124343553088121795035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40004749562368725414530023 60007124343553088121795035)
    ·
      refine ⟨90010686515329632182692553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60007124343553088121795035 90010686515329632182692553)
      ·
        refine ⟨67508014886497224137019415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90010686515329632182692553 67508014886497224137019415)
        ·
          refine ⟨101262022329745836205529123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67508014886497224137019415 101262022329745836205529123)
          ·
            refine ⟨151893033494618754308293685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101262022329745836205529123 151893033494618754308293685)
            ·
              refine ⟨14239971890120508216402533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 151893033494618754308293685 14239971890120508216402533)
              ·
                refine ⟨2669994729397595290575475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14239971890120508216402533 2669994729397595290575475)
                ·
                  refine ⟨4004992094096392935863213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2669994729397595290575475 4004992094096392935863213)
                  ·
                    refine ⟨1501872035286147350948705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4004992094096392935863213 1501872035286147350948705)
                    ·
                      refine ⟨1126404026464610513211529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1501872035286147350948705 1126404026464610513211529)
                      ·
                        rfl

theorem cell23_2193664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 1, 3, 2].length) (baseStart_2193664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193664 prefixEnd_2193664 := by exact prefixLift 2193664
  have htrace : WordTrace (prefixWord ++ tailWord_2193664) baseStart_2193664 baseEnd_2193664 := by
    simpa [prefixWord, tailWord_2193664, baseEnd_2193664] using wordTrace_append hprefix tailTrace_2193664
  have hstable : (prefixWord ++ tailWord_2193664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193664).length < 2 ^ (prefixWord ++ tailWord_2193664).sum := by decide
  have hdescent : baseEnd_2193664 < baseStart_2193664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193781 : List Nat := [1, 3, 4, 1, 2, 3, 1, 1, 2, 5]
def baseStart_2193781 : Nat := 118140960795 + 2193781 * 2 ^ 59
def prefixEnd_2193781 : Nat := 4983230072969 + 3 ^ 40 * 2193781 * 2
def baseEnd_2193781 : Nat := 375488034567062185149497

theorem tailTrace_2193781 : CollatzResearch.WordTrace tailWord_2193781 prefixEnd_2193781 375488034567062185149497 := by
  unfold tailWord_2193781
  simp only [CollatzResearch.WordTrace]
  refine ⟨80013766465313579811069197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53342510976875719874046131 80013766465313579811069197)
  ·
    refine ⟨30005162424492592429150949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80013766465313579811069197 30005162424492592429150949)
    ·
      refine ⟨5625967954592361080465803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30005162424492592429150949 5625967954592361080465803)
      ·
        refine ⟨8438951931888541620698705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5625967954592361080465803 8438951931888541620698705)
        ·
          refine ⟨6329213948916406215524029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8438951931888541620698705 6329213948916406215524029)
          ·
            refine ⟨2373455230843652330821511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6329213948916406215524029 2373455230843652330821511)
            ·
              refine ⟨3560182846265478496232267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2373455230843652330821511 3560182846265478496232267)
              ·
                refine ⟨5340274269398217744348401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3560182846265478496232267 5340274269398217744348401)
                ·
                  refine ⟨4005205702048663308261301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5340274269398217744348401 4005205702048663308261301)
                  ·
                    refine ⟨375488034567062185149497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4005205702048663308261301 375488034567062185149497)
                    ·
                      rfl

theorem cell23_2193781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_2193781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193781 prefixEnd_2193781 := by exact prefixLift 2193781
  have htrace : WordTrace (prefixWord ++ tailWord_2193781) baseStart_2193781 baseEnd_2193781 := by
    simpa [prefixWord, tailWord_2193781, baseEnd_2193781] using wordTrace_append hprefix tailTrace_2193781
  have hstable : (prefixWord ++ tailWord_2193781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193781).length < 2 ^ (prefixWord ++ tailWord_2193781).sum := by decide
  have hdescent : baseEnd_2193781 < baseStart_2193781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193845 : List Nat := [1, 3, 3, 2, 3, 2, 1, 3, 1, 4]
def baseStart_2193845 : Nat := 118140960795 + 2193845 * 2 ^ 59
def prefixEnd_2193845 : Nat := 4983230072969 + 3 ^ 40 * 2193845 * 2
def baseEnd_2193845 : Nat := 375498988821024768349399

theorem tailTrace_2193845 : CollatzResearch.WordTrace tailWord_2193845 prefixEnd_2193845 375498988821024768349399 := by
  unfold tailWord_2193845
  simp only [CollatzResearch.WordTrace]
  refine ⟨80016100737081718741398989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53344067158054479160932659 80016100737081718741398989)
  ·
    refine ⟨30006037776405644528024621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80016100737081718741398989 30006037776405644528024621)
    ·
      refine ⟨11252264166152116698009233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30006037776405644528024621 11252264166152116698009233)
      ·
        refine ⟨8439198124614087523506925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11252264166152116698009233 8439198124614087523506925)
        ·
          refine ⟨3164699296730282821315097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8439198124614087523506925 3164699296730282821315097)
          ·
            refine ⟨2373524472547712115986323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3164699296730282821315097 2373524472547712115986323)
            ·
              refine ⟨3560286708821568173979485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2373524472547712115986323 3560286708821568173979485)
              ·
                refine ⟨1335107515808088065242307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3560286708821568173979485 1335107515808088065242307)
                ·
                  refine ⟨2002661273712132097863461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1335107515808088065242307 2002661273712132097863461)
                  ·
                    refine ⟨375498988821024768349399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2002661273712132097863461 375498988821024768349399)
                    ·
                      rfl

theorem cell23_2193845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_2193845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193845 prefixEnd_2193845 := by exact prefixLift 2193845
  have htrace : WordTrace (prefixWord ++ tailWord_2193845) baseStart_2193845 baseEnd_2193845 := by
    simpa [prefixWord, tailWord_2193845, baseEnd_2193845] using wordTrace_append hprefix tailTrace_2193845
  have hstable : (prefixWord ++ tailWord_2193845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193845).length < 2 ^ (prefixWord ++ tailWord_2193845).sum := by decide
  have hdescent : baseEnd_2193845 < baseStart_2193845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193878 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2]
def baseStart_2193878 : Nat := 118140960795 + 2193878 * 2 ^ 59
def prefixEnd_2193878 : Nat := 4983230072969 + 3 ^ 40 * 2193878 * 2
def baseEnd_2193878 : Nat := 1126513911324672675935545

theorem tailTrace_2193878 : CollatzResearch.WordTrace tailWord_2193878 prefixEnd_2193878 1126513911324672675935545 := by
  unfold tailWord_2193878
  simp only [CollatzResearch.WordTrace]
  refine ⟨5001081521622635336084393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53344869563974776918233525 5001081521622635336084393)
  ·
    refine ⟨3750811141216976502063295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5001081521622635336084393 3750811141216976502063295)
    ·
      refine ⟨5626216711825464753094943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3750811141216976502063295 5626216711825464753094943)
      ·
        refine ⟨8439325067738197129642415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5626216711825464753094943 8439325067738197129642415)
        ·
          refine ⟨12658987601607295694463623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8439325067738197129642415 12658987601607295694463623)
          ·
            refine ⟨18988481402410943541695435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12658987601607295694463623 18988481402410943541695435)
            ·
              refine ⟨28482722103616415312543153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18988481402410943541695435 28482722103616415312543153)
              ·
                refine ⟨21362041577712311484407365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28482722103616415312543153 21362041577712311484407365)
                ·
                  refine ⟨4005382795821058403326381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21362041577712311484407365 4005382795821058403326381)
                  ·
                    refine ⟨1502018548432896901247393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4005382795821058403326381 1502018548432896901247393)
                    ·
                      refine ⟨1126513911324672675935545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1502018548432896901247393 1126513911324672675935545)
                      ·
                        rfl

theorem cell23_2193878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_2193878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193878 prefixEnd_2193878 := by exact prefixLift 2193878
  have htrace : WordTrace (prefixWord ++ tailWord_2193878) baseStart_2193878 baseEnd_2193878 := by
    simpa [prefixWord, tailWord_2193878, baseEnd_2193878] using wordTrace_append hprefix tailTrace_2193878
  have hstable : (prefixWord ++ tailWord_2193878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193878).length < 2 ^ (prefixWord ++ tailWord_2193878).sum := by decide
  have hdescent : baseEnd_2193878 < baseStart_2193878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193891 : List Nat := [1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 4]
def baseStart_2193891 : Nat := 118140960795 + 2193891 * 2 ^ 59
def prefixEnd_2193891 : Nat := 4983230072969 + 3 ^ 40 * 2193891 * 2
def baseEnd_2193891 : Nat := 1126520586573181125072985

theorem tailTrace_2193891 : CollatzResearch.WordTrace tailWord_2193891 prefixEnd_2193891 1126520586573181125072985 := by
  unfold tailWord_2193891
  simp only [CollatzResearch.WordTrace]
  refine ⟨80017778494915068597573527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53345185663276712398382351 80017778494915068597573527)
  ·
    refine ⟨120026667742372602896360291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80017778494915068597573527 120026667742372602896360291)
    ·
      refine ⟨180040001613558904344540437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120026667742372602896360291 180040001613558904344540437)
      ·
        refine ⟨8439375075635573641150333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 180040001613558904344540437 8439375075635573641150333)
        ·
          refine ⟨3164765653363340115431375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8439375075635573641150333 3164765653363340115431375)
          ·
            refine ⟨4747148480045010173147063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3164765653363340115431375 4747148480045010173147063)
            ·
              refine ⟨7120722720067515259720595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4747148480045010173147063 7120722720067515259720595)
              ·
                refine ⟨10681084080101272889580893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7120722720067515259720595 10681084080101272889580893)
                ·
                  refine ⟨4005406530037977333592835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10681084080101272889580893 4005406530037977333592835)
                  ·
                    refine ⟨6008109795056966000389253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4005406530037977333592835 6008109795056966000389253)
                    ·
                      refine ⟨1126520586573181125072985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6008109795056966000389253 1126520586573181125072985)
                      ·
                        rfl

theorem cell23_2193891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_2193891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193891 prefixEnd_2193891 := by exact prefixLift 2193891
  have htrace : WordTrace (prefixWord ++ tailWord_2193891) baseStart_2193891 baseEnd_2193891 := by
    simpa [prefixWord, tailWord_2193891, baseEnd_2193891] using wordTrace_append hprefix tailTrace_2193891
  have hstable : (prefixWord ++ tailWord_2193891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193891).length < 2 ^ (prefixWord ++ tailWord_2193891).sum := by decide
  have hdescent : baseEnd_2193891 < baseStart_2193891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193901 : List Nat := [1, 5, 1, 3, 1, 2, 1, 2, 1, 6]
def baseStart_2193901 : Nat := 118140960795 + 2193901 * 2 ^ 59
def prefixEnd_2193901 : Nat := 4983230072969 + 3 ^ 40 * 2193901 * 2
def baseEnd_2193901 : Nat := 375508573793242028649313

theorem tailTrace_2193901 : CollatzResearch.WordTrace tailWord_2193901 prefixEnd_2193901 375508573793242028649313 := by
  unfold tailWord_2193901
  simp only [CollatzResearch.WordTrace]
  refine ⟨80018143224878840305437557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53345428816585893536958371 80018143224878840305437557)
  ·
    refine ⟨7501700927332391278634771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80018143224878840305437557 7501700927332391278634771)
    ·
      refine ⟨11252551390998586917952157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7501700927332391278634771 11252551390998586917952157)
      ·
        refine ⟨4219706771624470094232059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11252551390998586917952157 4219706771624470094232059)
        ·
          refine ⟨6329560157436705141348089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4219706771624470094232059 6329560157436705141348089)
          ·
            refine ⟨4747170118077528856011067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6329560157436705141348089 4747170118077528856011067)
            ·
              refine ⟨7120755177116293284016601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4747170118077528856011067 7120755177116293284016601)
              ·
                refine ⟨5340566382837219963012451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7120755177116293284016601 5340566382837219963012451)
                ·
                  refine ⟨8010849574255829944518677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5340566382837219963012451 8010849574255829944518677)
                  ·
                    refine ⟨375508573793242028649313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8010849574255829944518677 375508573793242028649313)
                    ·
                      rfl

theorem cell23_2193901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_2193901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193901 prefixEnd_2193901 := by exact prefixLift 2193901
  have htrace : WordTrace (prefixWord ++ tailWord_2193901) baseStart_2193901 baseEnd_2193901 := by
    simpa [prefixWord, tailWord_2193901, baseEnd_2193901] using wordTrace_append hprefix tailTrace_2193901
  have hstable : (prefixWord ++ tailWord_2193901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193901).length < 2 ^ (prefixWord ++ tailWord_2193901).sum := by decide
  have hdescent : baseEnd_2193901 < baseStart_2193901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193904 : List Nat := [2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 4]
def baseStart_2193904 : Nat := 118140960795 + 2193904 * 2 ^ 59
def prefixEnd_2193904 : Nat := 4983230072969 + 3 ^ 40 * 2193904 * 2
def baseEnd_2193904 : Nat := 1126527261821689574210425

theorem tailTrace_2193904 : CollatzResearch.WordTrace tailWord_2193904 prefixEnd_2193904 1126527261821689574210425 := by
  unfold tailWord_2193904
  simp only [CollatzResearch.WordTrace]
  refine ⟨40009126321933985908898383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53345501762578647878531177 40009126321933985908898383)
  ·
    refine ⟨60013689482900978863347575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40009126321933985908898383 60013689482900978863347575)
    ·
      refine ⟨90020534224351468295021363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60013689482900978863347575 90020534224351468295021363)
      ·
        refine ⟨135030801336527202442532045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90020534224351468295021363 135030801336527202442532045)
        ·
          refine ⟨50636550501197700915949517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135030801336527202442532045 50636550501197700915949517)
          ·
            refine ⟨18988706437949137843481069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50636550501197700915949517 18988706437949137843481069)
            ·
              refine ⟨7120764914230926691305401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18988706437949137843481069 7120764914230926691305401)
              ·
                refine ⟨5340573685673195018479051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7120764914230926691305401 5340573685673195018479051)
                ·
                  refine ⟨8010860528509792527718577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5340573685673195018479051 8010860528509792527718577)
                  ·
                    refine ⟨6008145396382344395788933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8010860528509792527718577 6008145396382344395788933)
                    ·
                      refine ⟨1126527261821689574210425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6008145396382344395788933 1126527261821689574210425)
                      ·
                        rfl

theorem cell23_2193904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 4].length) (baseStart_2193904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193904 prefixEnd_2193904 := by exact prefixLift 2193904
  have htrace : WordTrace (prefixWord ++ tailWord_2193904) baseStart_2193904 baseEnd_2193904 := by
    simpa [prefixWord, tailWord_2193904, baseEnd_2193904] using wordTrace_append hprefix tailTrace_2193904
  have hstable : (prefixWord ++ tailWord_2193904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193904).length < 2 ^ (prefixWord ++ tailWord_2193904).sum := by decide
  have hdescent : baseEnd_2193904 < baseStart_2193904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193941 : List Nat := [1, 3, 2, 1, 3, 1, 4, 1, 1, 3, 3]
def baseStart_2193941 : Nat := 118140960795 + 2193941 * 2 ^ 59
def prefixEnd_2193941 : Nat := 4983230072969 + 3 ^ 40 * 2193941 * 2
def baseEnd_2193941 : Nat := 1126546260605905929447755

theorem tailTrace_2193941 : CollatzResearch.WordTrace tailWord_2193941 prefixEnd_2193941 1126546260605905929447755 := by
  unfold tailWord_2193941
  simp only [CollatzResearch.WordTrace]
  refine ⟨80019602144733927136893677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53346401429822618091262451 80019602144733927136893677)
  ·
    refine ⟨30007350804275222676335129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80019602144733927136893677 30007350804275222676335129)
    ·
      refine ⟨22505513103206417007251347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30007350804275222676335129 22505513103206417007251347)
      ·
        refine ⟨33758269654809625510877021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22505513103206417007251347 33758269654809625510877021)
        ·
          refine ⟨12659351120553609566578883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33758269654809625510877021 12659351120553609566578883)
          ·
            refine ⟨18989026680830414349868325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12659351120553609566578883 18989026680830414349868325)
            ·
              refine ⟨3560442502655702690600311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18989026680830414349868325 3560442502655702690600311)
              ·
                refine ⟨5340663753983554035900467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3560442502655702690600311 5340663753983554035900467)
                ·
                  refine ⟨8010995630975331053850701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5340663753983554035900467 8010995630975331053850701)
                  ·
                    refine ⟨3004123361615749145194013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8010995630975331053850701 3004123361615749145194013)
                    ·
                      refine ⟨1126546260605905929447755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3004123361615749145194013 1126546260605905929447755)
                      ·
                        rfl

theorem cell23_2193941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_2193941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193941 prefixEnd_2193941 := by exact prefixLift 2193941
  have htrace : WordTrace (prefixWord ++ tailWord_2193941) baseStart_2193941 baseEnd_2193941 := by
    simpa [prefixWord, tailWord_2193941, baseEnd_2193941] using wordTrace_append hprefix tailTrace_2193941
  have hstable : (prefixWord ++ tailWord_2193941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193941).length < 2 ^ (prefixWord ++ tailWord_2193941).sum := by decide
  have hdescent : baseEnd_2193941 < baseStart_2193941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
