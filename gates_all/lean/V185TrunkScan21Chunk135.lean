import V185TrunkScan21Chunk134

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1646069 : List Nat := [1, 3, 5, 1, 1, 1, 3, 3, 3]
def baseStart_1646069 : Nat := 118140960795 + 1646069 * 2 ^ 59
def prefixEnd_1646069 : Nat := 4983230072969 + 3 ^ 40 * 1646069 * 2
def baseEnd_1646069 : Nat := 375655372207033547185499

theorem tailTrace_1646069 : CollatzResearch.WordTrace tailWord_1646069 prefixEnd_1646069 375655372207033547185499 := by
  unfold tailWord_1646069
  simp only [CollatzResearch.WordTrace]
  refine ⟨60037068673580614048709261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40024712449053742699139507 60037068673580614048709261)
  ·
    refine ⟨22513900752592730268265973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60037068673580614048709261 22513900752592730268265973)
    ·
      refine ⟨2110678195555568462649935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22513900752592730268265973 2110678195555568462649935)
      ·
        refine ⟨3166017293333352693974903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2110678195555568462649935 3166017293333352693974903)
        ·
          refine ⟨4749025940000029040962355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3166017293333352693974903 4749025940000029040962355)
          ·
            refine ⟨7123538910000043561443533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4749025940000029040962355 7123538910000043561443533)
            ·
              refine ⟨2671327091250016335541325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7123538910000043561443533 2671327091250016335541325)
              ·
                refine ⟨1001747659218756125827997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2671327091250016335541325 1001747659218756125827997)
                ·
                  refine ⟨375655372207033547185499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1001747659218756125827997 375655372207033547185499)
                  ·
                    rfl

theorem cell21_1646069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3, 3].length) (baseStart_1646069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1646069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1646069 prefixEnd_1646069 := by exact prefixLift 1646069
  have htrace : WordTrace (prefixWord ++ tailWord_1646069) baseStart_1646069 baseEnd_1646069 := by
    simpa [prefixWord, tailWord_1646069, baseEnd_1646069] using wordTrace_append hprefix tailTrace_1646069
  have hstable : (prefixWord ++ tailWord_1646069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646069).length < 2 ^ (prefixWord ++ tailWord_1646069).sum := by decide
  have hdescent : baseEnd_1646069 < baseStart_1646069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646153 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 9]
def baseStart_1646153 : Nat := 118140960795 + 1646153 * 2 ^ 59
def prefixEnd_1646153 : Nat := 4983230072969 + 3 ^ 40 * 1646153 * 2
def baseEnd_1646153 : Nat := 375674542151468067785327

theorem tailTrace_1646153 : CollatzResearch.WordTrace tailWord_1646153 prefixEnd_1646153 375674542151468067785327 := by
  unfold tailWord_1646153
  simp only [CollatzResearch.WordTrace]
  refine ⟨60040132405276296394767113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40026754936850864263178075 60040132405276296394767113)
  ·
    refine ⟨45030099303957222296075335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60040132405276296394767113 45030099303957222296075335)
    ·
      refine ⟨67545148955935833444113003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45030099303957222296075335 67545148955935833444113003)
      ·
        refine ⟨101317723433903750166169505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67545148955935833444113003 101317723433903750166169505)
        ·
          refine ⟨75988292575427812624627129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101317723433903750166169505 75988292575427812624627129)
          ·
            refine ⟨56991219431570859468470347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75988292575427812624627129 56991219431570859468470347)
            ·
              refine ⟨85486829147356289202705521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56991219431570859468470347 85486829147356289202705521)
              ·
                refine ⟨64115121860517216902029141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85486829147356289202705521 64115121860517216902029141)
                ·
                  refine ⟨375674542151468067785327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64115121860517216902029141 375674542151468067785327)
                  ·
                    rfl

theorem cell21_1646153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_1646153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1646153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1646153 prefixEnd_1646153 := by exact prefixLift 1646153
  have htrace : WordTrace (prefixWord ++ tailWord_1646153) baseStart_1646153 baseEnd_1646153 := by
    simpa [prefixWord, tailWord_1646153, baseEnd_1646153] using wordTrace_append hprefix tailTrace_1646153
  have hstable : (prefixWord ++ tailWord_1646153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646153).length < 2 ^ (prefixWord ++ tailWord_1646153).sum := by decide
  have hdescent : baseEnd_1646153 < baseStart_1646153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646156 : List Nat := [2, 2, 1, 3, 1, 5, 1, 6]
def baseStart_1646156 : Nat := 118140960795 + 1646156 * 2 ^ 59
def prefixEnd_1646156 : Nat := 4983230072969 + 3 ^ 40 * 1646156 * 2
def baseEnd_1646156 : Nat := 125225075597446909745107

theorem tailTrace_1646156 : CollatzResearch.WordTrace tailWord_1646156 prefixEnd_1646156 125225075597446909745107 := by
  unfold tailWord_1646156
  simp only [CollatzResearch.WordTrace]
  refine ⟨30020120912132713953563161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40026827882843618604750881 30020120912132713953563161)
  ·
    refine ⟨22515090684099535465172371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30020120912132713953563161 22515090684099535465172371)
    ·
      refine ⟨33772636026149303197758557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22515090684099535465172371 33772636026149303197758557)
      ·
        refine ⟨12664738509805988699159459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33772636026149303197758557 12664738509805988699159459)
        ·
          refine ⟨18997107764708983048739189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12664738509805988699159459 18997107764708983048739189)
          ·
            refine ⟨1780978852941467160819299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18997107764708983048739189 1780978852941467160819299)
            ·
              refine ⟨2671468279412200741228949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1780978852941467160819299 2671468279412200741228949)
              ·
                refine ⟨125225075597446909745107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2671468279412200741228949 125225075597446909745107)
                ·
                  rfl

theorem cell21_1646156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 6].length) (baseStart_1646156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1646156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1646156 prefixEnd_1646156 := by exact prefixLift 1646156
  have htrace : WordTrace (prefixWord ++ tailWord_1646156) baseStart_1646156 baseEnd_1646156 := by
    simpa [prefixWord, tailWord_1646156, baseEnd_1646156] using wordTrace_append hprefix tailTrace_1646156
  have hstable : (prefixWord ++ tailWord_1646156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646156).length < 2 ^ (prefixWord ++ tailWord_1646156).sum := by decide
  have hdescent : baseEnd_1646156 < baseStart_1646156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646232 : List Nat := [2, 1, 2, 4, 1, 2, 4, 5]
def baseStart_1646232 : Nat := 118140960795 + 1646232 * 2 ^ 59
def prefixEnd_1646232 : Nat := 4983230072969 + 3 ^ 40 * 1646232 * 2
def baseEnd_1646232 : Nat := 125230857009260495322833

theorem tailTrace_1646232 : CollatzResearch.WordTrace tailWord_1646232 prefixEnd_1646232 125230857009260495322833 := by
  unfold tailWord_1646232
  simp only [CollatzResearch.WordTrace]
  refine ⟨30021506885995046443446475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40028675847993395257928633 30021506885995046443446475)
  ·
    refine ⟨45032260328992569665169713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30021506885995046443446475 45032260328992569665169713)
    ·
      refine ⟨33774195246744427248877285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45032260328992569665169713 33774195246744427248877285)
      ·
        refine ⟨6332661608764580109164491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33774195246744427248877285 6332661608764580109164491)
        ·
          refine ⟨9498992413146870163746737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6332661608764580109164491 9498992413146870163746737)
          ·
            refine ⟨7124244309860152622810053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9498992413146870163746737 7124244309860152622810053)
            ·
              refine ⟨1335795808098778616776885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7124244309860152622810053 1335795808098778616776885)
              ·
                refine ⟨125230857009260495322833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1335795808098778616776885 125230857009260495322833)
                ·
                  rfl

theorem cell21_1646232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 5].length) (baseStart_1646232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1646232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1646232 prefixEnd_1646232 := by exact prefixLift 1646232
  have htrace : WordTrace (prefixWord ++ tailWord_1646232) baseStart_1646232 baseEnd_1646232 := by
    simpa [prefixWord, tailWord_1646232, baseEnd_1646232] using wordTrace_append hprefix tailTrace_1646232
  have hstable : (prefixWord ++ tailWord_1646232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646232).length < 2 ^ (prefixWord ++ tailWord_1646232).sum := by decide
  have hdescent : baseEnd_1646232 < baseStart_1646232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646263 : List Nat := [1, 1, 3, 1, 5, 3, 1, 1, 5]
def baseStart_1646263 : Nat := 118140960795 + 1646263 * 2 ^ 59
def prefixEnd_1646263 : Nat := 4983230072969 + 3 ^ 40 * 1646263 * 2
def baseEnd_1646263 : Nat := 375699645650132320951769

theorem tailTrace_1646263 : CollatzResearch.WordTrace tailWord_1646263 prefixEnd_1646263 375699645650132320951769 := by
  unfold tailWord_1646263
  simp only [CollatzResearch.WordTrace]
  refine ⟨60044144434877785181271443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40029429623251856787514295 60044144434877785181271443)
  ·
    refine ⟨90066216652316677771907165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60044144434877785181271443 90066216652316677771907165)
    ·
      refine ⟨33774831244618754164465187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90066216652316677771907165 33774831244618754164465187)
      ·
        refine ⟨50662246866928131246697781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33774831244618754164465187 50662246866928131246697781)
        ·
          refine ⟨4749585643774512304377917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50662246866928131246697781 4749585643774512304377917)
          ·
            refine ⟨1781094616415442114141719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4749585643774512304377917 1781094616415442114141719)
            ·
              refine ⟨2671641924623163171212579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1781094616415442114141719 2671641924623163171212579)
              ·
                refine ⟨4007462886934744756818869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2671641924623163171212579 4007462886934744756818869)
                ·
                  refine ⟨375699645650132320951769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4007462886934744756818869 375699645650132320951769)
                  ·
                    rfl

theorem cell21_1646263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 5].length) (baseStart_1646263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1646263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1646263 prefixEnd_1646263 := by exact prefixLift 1646263
  have htrace : WordTrace (prefixWord ++ tailWord_1646263) baseStart_1646263 baseEnd_1646263 := by
    simpa [prefixWord, tailWord_1646263, baseEnd_1646263] using wordTrace_append hprefix tailTrace_1646263
  have hstable : (prefixWord ++ tailWord_1646263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646263).length < 2 ^ (prefixWord ++ tailWord_1646263).sum := by decide
  have hdescent : baseEnd_1646263 < baseStart_1646263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646311 : List Nat := [1, 1, 5, 4, 1, 1, 2, 2, 4]
def baseStart_1646311 : Nat := 118140960795 + 1646311 * 2 ^ 59
def prefixEnd_1646311 : Nat := 4983230072969 + 3 ^ 40 * 1646311 * 2
def baseEnd_1646311 : Nat := 375710599904094904151671

theorem tailTrace_1646311 : CollatzResearch.WordTrace tailWord_1646311 prefixEnd_1646311 375710599904094904151671 := by
  unfold tailWord_1646311
  simp only [CollatzResearch.WordTrace]
  refine ⟨60045895138703889379018787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40030596759135926252679191 60045895138703889379018787)
  ·
    refine ⟨90068842708055834068528181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60045895138703889379018787 90068842708055834068528181)
    ·
      refine ⟨8443954003880234443924517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90068842708055834068528181 8443954003880234443924517)
      ·
        refine ⟨1583241375727543958235847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8443954003880234443924517 1583241375727543958235847)
        ·
          refine ⟨2374862063591315937353771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1583241375727543958235847 2374862063591315937353771)
          ·
            refine ⟨3562293095386973906030657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2374862063591315937353771 3562293095386973906030657)
            ·
              refine ⟨2671719821540230429522993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3562293095386973906030657 2671719821540230429522993)
              ·
                refine ⟨2003789866155172822142245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2671719821540230429522993 2003789866155172822142245)
                ·
                  refine ⟨375710599904094904151671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2003789866155172822142245 375710599904094904151671)
                  ·
                    rfl

theorem cell21_1646311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 4].length) (baseStart_1646311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1646311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1646311 prefixEnd_1646311 := by exact prefixLift 1646311
  have htrace : WordTrace (prefixWord ++ tailWord_1646311) baseStart_1646311 baseEnd_1646311 := by
    simpa [prefixWord, tailWord_1646311, baseEnd_1646311] using wordTrace_append hprefix tailTrace_1646311
  have hstable : (prefixWord ++ tailWord_1646311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646311).length < 2 ^ (prefixWord ++ tailWord_1646311).sum := by decide
  have hdescent : baseEnd_1646311 < baseStart_1646311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646322 : List Nat := [3, 2, 1, 3, 1, 1, 2, 3, 5]
def baseStart_1646322 : Nat := 118140960795 + 1646322 * 2 ^ 59
def prefixEnd_1646322 : Nat := 4983230072969 + 3 ^ 40 * 1646322 * 2
def baseEnd_1646322 : Nat := 375713110253961329468315

theorem tailTrace_1646322 : CollatzResearch.WordTrace tailWord_1646322 prefixEnd_1646322 375713110253961329468315 := by
  unfold tailWord_1646322
  simp only [CollatzResearch.WordTrace]
  refine ⟨15011574085416009564417305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40030864227776025505112813 15011574085416009564417305)
  ·
    refine ⟨11258680564062007173312979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15011574085416009564417305 11258680564062007173312979)
    ·
      refine ⟨16888020846093010759969469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11258680564062007173312979 16888020846093010759969469)
      ·
        refine ⟨6333007817284879034988551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16888020846093010759969469 6333007817284879034988551)
        ·
          refine ⟨9499511725927318552482827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6333007817284879034988551 9499511725927318552482827)
          ·
            refine ⟨14249267588890977828724241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9499511725927318552482827 14249267588890977828724241)
            ·
              refine ⟨10686950691668233371543181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14249267588890977828724241 10686950691668233371543181)
              ·
                refine ⟨4007606509375587514328693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10686950691668233371543181 4007606509375587514328693)
                ·
                  refine ⟨375713110253961329468315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4007606509375587514328693 375713110253961329468315)
                  ·
                    rfl

theorem cell21_1646322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_1646322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1646322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1646322 prefixEnd_1646322 := by exact prefixLift 1646322
  have htrace : WordTrace (prefixWord ++ tailWord_1646322) baseStart_1646322 baseEnd_1646322 := by
    simpa [prefixWord, tailWord_1646322, baseEnd_1646322] using wordTrace_append hprefix tailTrace_1646322
  have hstable : (prefixWord ++ tailWord_1646322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646322).length < 2 ^ (prefixWord ++ tailWord_1646322).sum := by decide
  have hdescent : baseEnd_1646322 < baseStart_1646322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646432 : List Nat := [2, 1, 1, 3, 3, 3, 3, 2, 3]
def baseStart_1646432 : Nat := 118140960795 + 1646432 * 2 ^ 59
def prefixEnd_1646432 : Nat := 4983230072969 + 3 ^ 40 * 1646432 * 2
def baseEnd_1646432 : Nat := 375738213752625582634757

theorem tailTrace_1646432 : CollatzResearch.WordTrace tailWord_1646432 prefixEnd_1646432 375738213752625582634757 := by
  unfold tailWord_1646432
  simp only [CollatzResearch.WordTrace]
  refine ⟨30025154185632763522086775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40033538914177018029449033 30025154185632763522086775)
  ·
    refine ⟨45037731278449145283130163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30025154185632763522086775 45037731278449145283130163)
    ·
      refine ⟨67556596917673717924695245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45037731278449145283130163 67556596917673717924695245)
      ·
        refine ⟨25333723844127644221760717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67556596917673717924695245 25333723844127644221760717)
        ·
          refine ⟨9500146441547866583160269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25333723844127644221760717 9500146441547866583160269)
          ·
            refine ⟨3562554915580449968685101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9500146441547866583160269 3562554915580449968685101)
            ·
              refine ⟨1335958093342668738256913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3562554915580449968685101 1335958093342668738256913)
              ·
                refine ⟨1001968570007001553692685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1335958093342668738256913 1001968570007001553692685)
                ·
                  refine ⟨375738213752625582634757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1001968570007001553692685 375738213752625582634757)
                  ·
                    rfl

theorem cell21_1646432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2, 3].length) (baseStart_1646432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1646432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1646432 prefixEnd_1646432 := by exact prefixLift 1646432
  have htrace : WordTrace (prefixWord ++ tailWord_1646432) baseStart_1646432 baseEnd_1646432 := by
    simpa [prefixWord, tailWord_1646432, baseEnd_1646432] using wordTrace_append hprefix tailTrace_1646432
  have hstable : (prefixWord ++ tailWord_1646432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646432).length < 2 ^ (prefixWord ++ tailWord_1646432).sum := by decide
  have hdescent : baseEnd_1646432 < baseStart_1646432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646446 : List Nat := [4, 1, 2, 3, 1, 2, 1, 3, 4]
def baseStart_1646446 : Nat := 118140960795 + 1646446 * 2 ^ 59
def prefixEnd_1646446 : Nat := 4983230072969 + 3 ^ 40 * 1646446 * 2
def baseEnd_1646446 : Nat := 375741408743364669401395

theorem tailTrace_1646446 : CollatzResearch.WordTrace tailWord_1646446 prefixEnd_1646446 375741408743364669401395 := by
  unfold tailWord_1646446
  simp only [CollatzResearch.WordTrace]
  refine ⟨7506352374151850929397899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40033879328809871623455461 7506352374151850929397899)
  ·
    refine ⟨11259528561227776394096849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7506352374151850929397899 11259528561227776394096849)
    ·
      refine ⟨8444646420920832295572637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11259528561227776394096849 8444646420920832295572637)
      ·
        refine ⟨3166742407845312110839739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8444646420920832295572637 3166742407845312110839739)
        ·
          refine ⟨4750113611767968166259609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3166742407845312110839739 4750113611767968166259609)
          ·
            refine ⟨3562585208825976124694707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4750113611767968166259609 3562585208825976124694707)
            ·
              refine ⟨5343877813238964187042061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3562585208825976124694707 5343877813238964187042061)
              ·
                refine ⟨2003954179964611570140773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5343877813238964187042061 2003954179964611570140773)
                ·
                  refine ⟨375741408743364669401395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2003954179964611570140773 375741408743364669401395)
                  ·
                    rfl

theorem cell21_1646446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_1646446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1646446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1646446 prefixEnd_1646446 := by exact prefixLift 1646446
  have htrace : WordTrace (prefixWord ++ tailWord_1646446) baseStart_1646446 baseEnd_1646446 := by
    simpa [prefixWord, tailWord_1646446, baseEnd_1646446] using wordTrace_append hprefix tailTrace_1646446
  have hstable : (prefixWord ++ tailWord_1646446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646446).length < 2 ^ (prefixWord ++ tailWord_1646446).sum := by decide
  have hdescent : baseEnd_1646446 < baseStart_1646446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646457 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 7]
def baseStart_1646457 : Nat := 118140960795 + 1646457 * 2 ^ 59
def prefixEnd_1646457 : Nat := 4983230072969 + 3 ^ 40 * 1646457 * 2
def baseEnd_1646457 : Nat := 375743919093231094718039

theorem tailTrace_1646457 : CollatzResearch.WordTrace tailWord_1646457 prefixEnd_1646457 375743919093231094718039 := by
  unfold tailWord_1646457
  simp only [CollatzResearch.WordTrace]
  refine ⟨60051220196174956313833625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40034146797449970875889083 60051220196174956313833625)
  ·
    refine ⟨45038415147131217235375219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60051220196174956313833625 45038415147131217235375219)
    ·
      refine ⟨67557622720696825853062829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45038415147131217235375219 67557622720696825853062829)
      ·
        refine ⟨25334108520261309694898561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67557622720696825853062829 25334108520261309694898561)
        ·
          refine ⟨19000581390195982271173921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25334108520261309694898561 19000581390195982271173921)
          ·
            refine ⟨14250436042646986703380441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19000581390195982271173921 14250436042646986703380441)
            ·
              refine ⟨10687827031985240027535331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14250436042646986703380441 10687827031985240027535331)
              ·
                refine ⟨16031740547977860041302997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10687827031985240027535331 16031740547977860041302997)
                ·
                  refine ⟨375743919093231094718039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16031740547977860041302997 375743919093231094718039)
                  ·
                    rfl

theorem cell21_1646457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 7].length) (baseStart_1646457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1646457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1646457 prefixEnd_1646457 := by exact prefixLift 1646457
  have htrace : WordTrace (prefixWord ++ tailWord_1646457) baseStart_1646457 baseEnd_1646457 := by
    simpa [prefixWord, tailWord_1646457, baseEnd_1646457] using wordTrace_append hprefix tailTrace_1646457
  have hstable : (prefixWord ++ tailWord_1646457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646457).length < 2 ^ (prefixWord ++ tailWord_1646457).sum := by decide
  have hdescent : baseEnd_1646457 < baseStart_1646457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646494 : List Nat := [4, 3, 1, 3, 1, 2, 1, 6]
def baseStart_1646494 : Nat := 118140960795 + 1646494 * 2 ^ 59
def prefixEnd_1646494 : Nat := 4983230072969 + 3 ^ 40 * 1646494 * 2
def baseEnd_1646494 : Nat := 125250787665775750867099

theorem tailTrace_1646494 : CollatzResearch.WordTrace tailWord_1646494 prefixEnd_1646494 125250787665775750867099 := by
  unfold tailWord_1646494
  simp only [CollatzResearch.WordTrace]
  refine ⟨7506571212130113954116317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40035046464693941088620357 7506571212130113954116317)
  ·
    refine ⟨2814964204548792732793619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7506571212130113954116317 2814964204548792732793619)
    ·
      refine ⟨4222446306823189099190429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2814964204548792732793619 4222446306823189099190429)
      ·
        refine ⟨1583417365058695912196411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4222446306823189099190429 1583417365058695912196411)
        ·
          refine ⟨2375126047588043868294617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1583417365058695912196411 2375126047588043868294617)
          ·
            refine ⟨1781344535691032901220963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2375126047588043868294617 1781344535691032901220963)
            ·
              refine ⟨2672016803536549351831445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1781344535691032901220963 2672016803536549351831445)
              ·
                refine ⟨125250787665775750867099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2672016803536549351831445 125250787665775750867099)
                ·
                  rfl

theorem cell21_1646494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_1646494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1646494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1646494 prefixEnd_1646494 := by exact prefixLift 1646494
  have htrace : WordTrace (prefixWord ++ tailWord_1646494) baseStart_1646494 baseEnd_1646494 := by
    simpa [prefixWord, tailWord_1646494, baseEnd_1646494] using wordTrace_append hprefix tailTrace_1646494
  have hstable : (prefixWord ++ tailWord_1646494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646494).length < 2 ^ (prefixWord ++ tailWord_1646494).sum := by decide
  have hdescent : baseEnd_1646494 < baseStart_1646494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646615 : List Nat := [1, 1, 3, 5, 2, 2, 2, 1, 4]
def baseStart_1646615 : Nat := 118140960795 + 1646615 * 2 ^ 59
def prefixEnd_1646615 : Nat := 4983230072969 + 3 ^ 40 * 1646615 * 2
def baseEnd_1646615 : Nat := 375779976845857931084383

theorem tailTrace_1646615 : CollatzResearch.WordTrace tailWord_1646615 prefixEnd_1646615 375779976845857931084383 := by
  unfold tailWord_1646615
  simp only [CollatzResearch.WordTrace]
  refine ⟨60056982929602549298085299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40037988619735032865390199 60056982929602549298085299)
  ·
    refine ⟨90085474394403823947127949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60056982929602549298085299 90085474394403823947127949)
    ·
      refine ⟨33782052897901433980172981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90085474394403823947127949 33782052897901433980172981)
      ·
        refine ⟨3167067459178259435641217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33782052897901433980172981 3167067459178259435641217)
        ·
          refine ⟨2375300594383694576730913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3167067459178259435641217 2375300594383694576730913)
          ·
            refine ⟨1781475445787770932548185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2375300594383694576730913 1781475445787770932548185)
            ·
              refine ⟨1336106584340828199411139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1781475445787770932548185 1336106584340828199411139)
              ·
                refine ⟨2004159876511242299116709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1336106584340828199411139 2004159876511242299116709)
                ·
                  refine ⟨375779976845857931084383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2004159876511242299116709 375779976845857931084383)
                  ·
                    rfl

theorem cell21_1646615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 4].length) (baseStart_1646615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1646615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1646615 prefixEnd_1646615 := by exact prefixLift 1646615
  have htrace : WordTrace (prefixWord ++ tailWord_1646615) baseStart_1646615 baseEnd_1646615 := by
    simpa [prefixWord, tailWord_1646615, baseEnd_1646615] using wordTrace_append hprefix tailTrace_1646615
  have hstable : (prefixWord ++ tailWord_1646615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646615).length < 2 ^ (prefixWord ++ tailWord_1646615).sum := by decide
  have hdescent : baseEnd_1646615 < baseStart_1646615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646657 : List Nat := [1, 2, 5, 1, 2, 1, 1, 4, 4]
def baseStart_1646657 : Nat := 118140960795 + 1646657 * 2 ^ 59
def prefixEnd_1646657 : Nat := 4983230072969 + 3 ^ 40 * 1646657 * 2
def baseEnd_1646657 : Nat := 375789561818075191384297

theorem tailTrace_1646657 : CollatzResearch.WordTrace tailWord_1646657 prefixEnd_1646657 375789561818075191384297 := by
  unfold tailWord_1646657
  simp only [CollatzResearch.WordTrace]
  refine ⟨60058514795450390471114225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40039009863633593647409483 60058514795450390471114225)
  ·
    refine ⟨45043886096587792853335669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60058514795450390471114225 45043886096587792853335669)
    ·
      refine ⟨4222864321555105580000219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45043886096587792853335669 4222864321555105580000219)
      ·
        refine ⟨6334296482332658370000329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4222864321555105580000219 6334296482332658370000329)
        ·
          refine ⟨4750722361749493777500247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6334296482332658370000329 4750722361749493777500247)
          ·
            refine ⟨7126083542624240666250371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4750722361749493777500247 7126083542624240666250371)
            ·
              refine ⟨10689125313936360999375557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7126083542624240666250371 10689125313936360999375557)
              ·
                refine ⟨2004210996363067687382917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10689125313936360999375557 2004210996363067687382917)
                ·
                  refine ⟨375789561818075191384297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2004210996363067687382917 375789561818075191384297)
                  ·
                    rfl

theorem cell21_1646657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 4].length) (baseStart_1646657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1646657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1646657 prefixEnd_1646657 := by exact prefixLift 1646657
  have htrace : WordTrace (prefixWord ++ tailWord_1646657) baseStart_1646657 baseEnd_1646657 := by
    simpa [prefixWord, tailWord_1646657, baseEnd_1646657] using wordTrace_append hprefix tailTrace_1646657
  have hstable : (prefixWord ++ tailWord_1646657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646657).length < 2 ^ (prefixWord ++ tailWord_1646657).sum := by decide
  have hdescent : baseEnd_1646657 < baseStart_1646657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646716 : List Nat := [2, 2, 2, 1, 1, 5, 1, 1, 6]
def baseStart_1646716 : Nat := 118140960795 + 1646716 * 2 ^ 59
def prefixEnd_1646716 : Nat := 4983230072969 + 3 ^ 40 * 1646716 * 2
def baseEnd_1646716 : Nat := 375803026421904199900843

theorem tailTrace_1646716 : CollatzResearch.WordTrace tailWord_1646716 prefixEnd_1646716 375803026421904199900843 := by
  unfold tailWord_1646716
  simp only [CollatzResearch.WordTrace]
  refine ⟨30030333351118321773756001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40040444468157762365008001 30030333351118321773756001)
  ·
    refine ⟨22522750013338741330317001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30030333351118321773756001 22522750013338741330317001)
    ·
      refine ⟨16892062510004055997737751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22522750013338741330317001 16892062510004055997737751)
      ·
        refine ⟨25338093765006083996606627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16892062510004055997737751 25338093765006083996606627)
        ·
          refine ⟨38007140647509125994909941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25338093765006083996606627 38007140647509125994909941)
          ·
            refine ⟨3563169435703980562022807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38007140647509125994909941 3563169435703980562022807)
            ·
              refine ⟨5344754153555970843034211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3563169435703980562022807 5344754153555970843034211)
              ·
                refine ⟨8017131230333956264551317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5344754153555970843034211 8017131230333956264551317)
                ·
                  refine ⟨375803026421904199900843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8017131230333956264551317 375803026421904199900843)
                  ·
                    rfl

theorem cell21_1646716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_1646716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1646716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1646716 prefixEnd_1646716 := by exact prefixLift 1646716
  have htrace : WordTrace (prefixWord ++ tailWord_1646716) baseStart_1646716 baseEnd_1646716 := by
    simpa [prefixWord, tailWord_1646716, baseEnd_1646716] using wordTrace_append hprefix tailTrace_1646716
  have hstable : (prefixWord ++ tailWord_1646716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646716).length < 2 ^ (prefixWord ++ tailWord_1646716).sum := by decide
  have hdescent : baseEnd_1646716 < baseStart_1646716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646778 : List Nat := [3, 1, 1, 1, 2, 2, 2, 6, 3]
def baseStart_1646778 : Nat := 118140960795 + 1646778 * 2 ^ 59
def prefixEnd_1646778 : Nat := 4983230072969 + 3 ^ 40 * 1646778 * 2
def baseEnd_1646778 : Nat := 375817175666605869867383

theorem tailTrace_1646778 : CollatzResearch.WordTrace tailWord_1646778 prefixEnd_1646778 375817175666605869867383 := by
  unfold tailWord_1646778
  simp only [CollatzResearch.WordTrace]
  refine ⟨15015732007003007034067247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40041952018674685424179325 15015732007003007034067247)
  ·
    refine ⟨22523598010504510551100871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15015732007003007034067247 22523598010504510551100871)
    ·
      refine ⟨33785397015756765826651307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22523598010504510551100871 33785397015756765826651307)
      ·
        refine ⟨50678095523635148739976961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33785397015756765826651307 50678095523635148739976961)
        ·
          refine ⟨38008571642726361554982721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50678095523635148739976961 38008571642726361554982721)
          ·
            refine ⟨28506428732044771166237041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38008571642726361554982721 28506428732044771166237041)
            ·
              refine ⟨21379821549033578374677781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28506428732044771166237041 21379821549033578374677781)
              ·
                refine ⟨1002179135110948986313021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21379821549033578374677781 1002179135110948986313021)
                ·
                  refine ⟨375817175666605869867383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1002179135110948986313021 375817175666605869867383)
                  ·
                    rfl

theorem cell21_1646778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6, 3].length) (baseStart_1646778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1646778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1646778 prefixEnd_1646778 := by exact prefixLift 1646778
  have htrace : WordTrace (prefixWord ++ tailWord_1646778) baseStart_1646778 baseEnd_1646778 := by
    simpa [prefixWord, tailWord_1646778, baseEnd_1646778] using wordTrace_append hprefix tailTrace_1646778
  have hstable : (prefixWord ++ tailWord_1646778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646778).length < 2 ^ (prefixWord ++ tailWord_1646778).sum := by decide
  have hdescent : baseEnd_1646778 < baseStart_1646778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646829 : List Nat := [1, 5, 1, 2, 3, 2, 2, 2, 3]
def baseStart_1646829 : Nat := 118140960795 + 1646829 * 2 ^ 59
def prefixEnd_1646829 : Nat := 4983230072969 + 3 ^ 40 * 1646829 * 2
def baseEnd_1646829 : Nat := 375828814561441114517279

theorem tailTrace_1646829 : CollatzResearch.WordTrace tailWord_1646829 prefixEnd_1646829 375828814561441114517279 := by
  unfold tailWord_1646829
  simp only [CollatzResearch.WordTrace]
  refine ⟨60064788150827263846375541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40043192100551509230917027 60064788150827263846375541)
  ·
    refine ⟨5631073889140055985597707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60064788150827263846375541 5631073889140055985597707)
    ·
      refine ⟨8446610833710083978396561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5631073889140055985597707 8446610833710083978396561)
      ·
        refine ⟨6334958125282562983797421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8446610833710083978396561 6334958125282562983797421)
        ·
          refine ⟨2375609296980961118924033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6334958125282562983797421 2375609296980961118924033)
          ·
            refine ⟨1781706972735720839193025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2375609296980961118924033 1781706972735720839193025)
            ·
              refine ⟨1336280229551790629394769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1781706972735720839193025 1336280229551790629394769)
              ·
                refine ⟨1002210172163842972046077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1336280229551790629394769 1002210172163842972046077)
                ·
                  refine ⟨375828814561441114517279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1002210172163842972046077 375828814561441114517279)
                  ·
                    rfl

theorem cell21_1646829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_1646829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1646829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1646829 prefixEnd_1646829 := by exact prefixLift 1646829
  have htrace : WordTrace (prefixWord ++ tailWord_1646829) baseStart_1646829 baseEnd_1646829 := by
    simpa [prefixWord, tailWord_1646829, baseEnd_1646829] using wordTrace_append hprefix tailTrace_1646829
  have hstable : (prefixWord ++ tailWord_1646829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646829).length < 2 ^ (prefixWord ++ tailWord_1646829).sum := by decide
  have hdescent : baseEnd_1646829 < baseStart_1646829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646871 : List Nat := [1, 1, 3, 4, 1, 3, 2, 3, 3]
def baseStart_1646871 : Nat := 118140960795 + 1646871 * 2 ^ 59
def prefixEnd_1646871 : Nat := 4983230072969 + 3 ^ 40 * 1646871 * 2
def baseEnd_1646871 : Nat := 375838399533658374817193

theorem tailTrace_1646871 : CollatzResearch.WordTrace tailWord_1646871 prefixEnd_1646871 375838399533658374817193 := by
  unfold tailWord_1646871
  simp only [CollatzResearch.WordTrace]
  refine ⟨60066320016675105019404467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40044213344450070012936311 60066320016675105019404467)
  ·
    refine ⟨90099480025012657529106701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60066320016675105019404467 90099480025012657529106701)
    ·
      refine ⟨33787305009379746573415013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90099480025012657529106701 33787305009379746573415013)
      ·
        refine ⟨6335119689258702482515315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33787305009379746573415013 6335119689258702482515315)
        ·
          refine ⟨9502679533888053723772973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6335119689258702482515315 9502679533888053723772973)
          ·
            refine ⟨3563504825208020146414865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9502679533888053723772973 3563504825208020146414865)
            ·
              refine ⟨2672628618906015109811149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3563504825208020146414865 2672628618906015109811149)
              ·
                refine ⟨1002235732089755666179181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2672628618906015109811149 1002235732089755666179181)
                ·
                  refine ⟨375838399533658374817193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1002235732089755666179181 375838399533658374817193)
                  ·
                    rfl

theorem cell21_1646871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3, 3].length) (baseStart_1646871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1646871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1646871 prefixEnd_1646871 := by exact prefixLift 1646871
  have htrace : WordTrace (prefixWord ++ tailWord_1646871) baseStart_1646871 baseEnd_1646871 := by
    simpa [prefixWord, tailWord_1646871, baseEnd_1646871] using wordTrace_append hprefix tailTrace_1646871
  have hstable : (prefixWord ++ tailWord_1646871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646871).length < 2 ^ (prefixWord ++ tailWord_1646871).sum := by decide
  have hdescent : baseEnd_1646871 < baseStart_1646871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646916 : List Nat := [2, 3, 4, 1, 2, 1, 1, 7]
def baseStart_1646916 : Nat := 118140960795 + 1646916 * 2 ^ 59
def prefixEnd_1646916 : Nat := 4983230072969 + 3 ^ 40 * 1646916 * 2
def baseEnd_1646916 : Nat := 125282889715582765522367

theorem tailTrace_1646916 : CollatzResearch.WordTrace tailWord_1646916 prefixEnd_1646916 125282889715582765522367 := by
  unfold tailWord_1646916
  simp only [CollatzResearch.WordTrace]
  refine ⟨30033980650756038852396301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40045307534341385136528401 30033980650756038852396301)
  ·
    refine ⟨11262742744033514569648613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30033980650756038852396301 11262742744033514569648613)
    ·
      refine ⟨2111764264506283981809115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11262742744033514569648613 2111764264506283981809115)
      ·
        refine ⟨3167646396759425972713673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2111764264506283981809115 3167646396759425972713673)
        ·
          refine ⟨2375734797569569479535255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3167646396759425972713673 2375734797569569479535255)
          ·
            refine ⟨3563602196354354219302883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2375734797569569479535255 3563602196354354219302883)
            ·
              refine ⟨5345403294531531328954325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3563602196354354219302883 5345403294531531328954325)
              ·
                refine ⟨125282889715582765522367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5345403294531531328954325 125282889715582765522367)
                ·
                  rfl

theorem cell21_1646916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 7].length) (baseStart_1646916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1646916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1646916 prefixEnd_1646916 := by exact prefixLift 1646916
  have htrace : WordTrace (prefixWord ++ tailWord_1646916) baseStart_1646916 baseEnd_1646916 := by
    simpa [prefixWord, tailWord_1646916, baseEnd_1646916] using wordTrace_append hprefix tailTrace_1646916
  have hstable : (prefixWord ++ tailWord_1646916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646916).length < 2 ^ (prefixWord ++ tailWord_1646916).sum := by decide
  have hdescent : baseEnd_1646916 < baseStart_1646916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646947 : List Nat := [1, 1, 1, 5, 2, 1, 5, 2, 3]
def baseStart_1646947 : Nat := 118140960795 + 1646947 * 2 ^ 59
def prefixEnd_1646947 : Nat := 4983230072969 + 3 ^ 40 * 1646947 * 2
def baseEnd_1646947 : Nat := 375855743769099131550371

theorem tailTrace_1646947 : CollatzResearch.WordTrace tailWord_1646947 prefixEnd_1646947 375855743769099131550371 := by
  unfold tailWord_1646947
  simp only [CollatzResearch.WordTrace]
  refine ⟨60069091964399769999171095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40046061309599846666114063 60069091964399769999171095)
  ·
    refine ⟨90103637946599654998756643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60069091964399769999171095 90103637946599654998756643)
    ·
      refine ⟨135155456919899482498134965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90103637946599654998756643 135155456919899482498134965)
      ·
        refine ⟨12670824086240576484200153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135155456919899482498134965 12670824086240576484200153)
        ·
          refine ⟨9503118064680432363150115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12670824086240576484200153 9503118064680432363150115)
          ·
            refine ⟨14254677097020648544725173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9503118064680432363150115 14254677097020648544725173)
            ·
              refine ⟨1336375977845685801067985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14254677097020648544725173 1336375977845685801067985)
              ·
                refine ⟨1002281983384264350800989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1336375977845685801067985 1002281983384264350800989)
                ·
                  refine ⟨375855743769099131550371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1002281983384264350800989 375855743769099131550371)
                  ·
                    rfl

theorem cell21_1646947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2, 3].length) (baseStart_1646947 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1646947 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1646947 prefixEnd_1646947 := by exact prefixLift 1646947
  have htrace : WordTrace (prefixWord ++ tailWord_1646947) baseStart_1646947 baseEnd_1646947 := by
    simpa [prefixWord, tailWord_1646947, baseEnd_1646947] using wordTrace_append hprefix tailTrace_1646947
  have hstable : (prefixWord ++ tailWord_1646947).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646947).length < 2 ^ (prefixWord ++ tailWord_1646947).sum := by decide
  have hdescent : baseEnd_1646947 < baseStart_1646947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646998 : List Nat := [5, 3, 1, 2, 1, 1, 1, 4, 3]
def baseStart_1646998 : Nat := 118140960795 + 1646998 * 2 ^ 59
def prefixEnd_1646998 : Nat := 4983230072969 + 3 ^ 40 * 1646998 * 2
def baseEnd_1646998 : Nat := 375867382663934376200267

theorem tailTrace_1646998 : CollatzResearch.WordTrace tailWord_1646998 prefixEnd_1646998 375867382663934376200267 := by
  unfold tailWord_1646998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3754434505450937856829853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40047301391476670472851765 3754434505450937856829853)
  ·
    refine ⟨1407912939544101696311195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3754434505450937856829853 1407912939544101696311195)
    ·
      refine ⟨2111869409316152544466793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1407912939544101696311195 2111869409316152544466793)
      ·
        refine ⟨1583902056987114408350095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2111869409316152544466793 1583902056987114408350095)
        ·
          refine ⟨2375853085480671612525143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1583902056987114408350095 2375853085480671612525143)
          ·
            refine ⟨3563779628221007418787715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2375853085480671612525143 3563779628221007418787715)
            ·
              refine ⟨5345669442331511128181573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3563779628221007418787715 5345669442331511128181573)
              ·
                refine ⟨1002313020437158336534045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5345669442331511128181573 1002313020437158336534045)
                ·
                  refine ⟨375867382663934376200267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1002313020437158336534045 375867382663934376200267)
                  ·
                    rfl

theorem cell21_1646998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_1646998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1646998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1646998 prefixEnd_1646998 := by exact prefixLift 1646998
  have htrace : WordTrace (prefixWord ++ tailWord_1646998) baseStart_1646998 baseEnd_1646998 := by
    simpa [prefixWord, tailWord_1646998, baseEnd_1646998] using wordTrace_append hprefix tailTrace_1646998
  have hstable : (prefixWord ++ tailWord_1646998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646998).length < 2 ^ (prefixWord ++ tailWord_1646998).sum := by decide
  have hdescent : baseEnd_1646998 < baseStart_1646998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647009 : List Nat := [1, 2, 3, 5, 2, 1, 1, 6]
def baseStart_1647009 : Nat := 118140960795 + 1647009 * 2 ^ 59
def prefixEnd_1647009 : Nat := 4983230072969 + 3 ^ 40 * 1647009 * 2
def baseEnd_1647009 : Nat := 125289964337933600505637

theorem tailTrace_1647009 : CollatzResearch.WordTrace tailWord_1647009 prefixEnd_1647009 125289964337933600505637 := by
  unfold tailWord_1647009
  simp only [CollatzResearch.WordTrace]
  refine ⟨60071353290175154587928081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40047568860116769725285387 60071353290175154587928081)
  ·
    refine ⟨45053514967631365940946061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60071353290175154587928081 45053514967631365940946061)
    ·
      refine ⟨16895068112861762227854773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45053514967631365940946061 16895068112861762227854773)
      ·
        refine ⟨1583912635580790208861385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16895068112861762227854773 1583912635580790208861385)
        ·
          refine ⟨1187934476685592656646039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1583912635580790208861385 1187934476685592656646039)
          ·
            refine ⟨1781901715028388984969059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1187934476685592656646039 1781901715028388984969059)
            ·
              refine ⟨2672852572542583477453589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1781901715028388984969059 2672852572542583477453589)
              ·
                refine ⟨125289964337933600505637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2672852572542583477453589 125289964337933600505637)
                ·
                  rfl

theorem cell21_1647009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 6].length) (baseStart_1647009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1647009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1647009 prefixEnd_1647009 := by exact prefixLift 1647009
  have htrace : WordTrace (prefixWord ++ tailWord_1647009) baseStart_1647009 baseEnd_1647009 := by
    simpa [prefixWord, tailWord_1647009, baseEnd_1647009] using wordTrace_append hprefix tailTrace_1647009
  have hstable : (prefixWord ++ tailWord_1647009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647009).length < 2 ^ (prefixWord ++ tailWord_1647009).sum := by decide
  have hdescent : baseEnd_1647009 < baseStart_1647009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647065 : List Nat := [1, 2, 1, 2, 4, 1, 4, 1, 5]
def baseStart_1647065 : Nat := 118140960795 + 1647065 * 2 ^ 59
def prefixEnd_1647065 : Nat := 4983230072969 + 3 ^ 40 * 1647065 * 2
def baseEnd_1647065 : Nat := 375882672976757148583463

theorem tailTrace_1647065 : CollatzResearch.WordTrace tailWord_1647065 prefixEnd_1647065 375882672976757148583463 := by
  unfold tailWord_1647065
  simp only [CollatzResearch.WordTrace]
  refine ⟨60073395777972276151966649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40048930518648184101311099 60073395777972276151966649)
  ·
    refine ⟨45055046833479207113974987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60073395777972276151966649 45055046833479207113974987)
    ·
      refine ⟨67582570250218810670962481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45055046833479207113974987 67582570250218810670962481)
      ·
        refine ⟨50686927687664108003221861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67582570250218810670962481 50686927687664108003221861)
        ·
          refine ⟨9503798941437020250604099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50686927687664108003221861 9503798941437020250604099)
          ·
            refine ⟨14255698412155530375906149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9503798941437020250604099 14255698412155530375906149)
            ·
              refine ⟨2672943452279161945482403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14255698412155530375906149 2672943452279161945482403)
              ·
                refine ⟨4009415178418742918223605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2672943452279161945482403 4009415178418742918223605)
                ·
                  refine ⟨375882672976757148583463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4009415178418742918223605 375882672976757148583463)
                  ·
                    rfl

theorem cell21_1647065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 5].length) (baseStart_1647065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1647065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1647065 prefixEnd_1647065 := by exact prefixLift 1647065
  have htrace : WordTrace (prefixWord ++ tailWord_1647065) baseStart_1647065 baseEnd_1647065 := by
    simpa [prefixWord, tailWord_1647065, baseEnd_1647065] using wordTrace_append hprefix tailTrace_1647065
  have hstable : (prefixWord ++ tailWord_1647065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647065).length < 2 ^ (prefixWord ++ tailWord_1647065).sum := by decide
  have hdescent : baseEnd_1647065 < baseStart_1647065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647175 : List Nat := [1, 1, 4, 1, 4, 1, 4, 2, 3]
def baseStart_1647175 : Nat := 118140960795 + 1647175 * 2 ^ 59
def prefixEnd_1647175 : Nat := 4983230072969 + 3 ^ 40 * 1647175 * 2
def baseEnd_1647175 : Nat := 375907776475421401749905

theorem tailTrace_1647175 : CollatzResearch.WordTrace tailWord_1647175 prefixEnd_1647175 375907776475421401749905 := by
  unfold tailWord_1647175
  simp only [CollatzResearch.WordTrace]
  refine ⟨60077407807573764938470979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40051605205049176625647319 60077407807573764938470979)
  ·
    refine ⟨90116111711360647407706469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60077407807573764938470979 90116111711360647407706469)
    ·
      refine ⟨16896770945880121388944963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90116111711360647407706469 16896770945880121388944963)
      ·
        refine ⟨25345156418820182083417445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16896770945880121388944963 25345156418820182083417445)
        ·
          refine ⟨4752216828528784140640771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25345156418820182083417445 4752216828528784140640771)
          ·
            refine ⟨7128325242793176210961157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4752216828528784140640771 7128325242793176210961157)
            ·
              refine ⟨1336560983023720539555217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7128325242793176210961157 1336560983023720539555217)
              ·
                refine ⟨1002420737267790404666413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1336560983023720539555217 1002420737267790404666413)
                ·
                  refine ⟨375907776475421401749905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1002420737267790404666413 375907776475421401749905)
                  ·
                    rfl

theorem cell21_1647175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2, 3].length) (baseStart_1647175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1647175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1647175 prefixEnd_1647175 := by exact prefixLift 1647175
  have htrace : WordTrace (prefixWord ++ tailWord_1647175) baseStart_1647175 baseEnd_1647175 := by
    simpa [prefixWord, tailWord_1647175, baseEnd_1647175] using wordTrace_append hprefix tailTrace_1647175
  have hstable : (prefixWord ++ tailWord_1647175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647175).length < 2 ^ (prefixWord ++ tailWord_1647175).sum := by decide
  have hdescent : baseEnd_1647175 < baseStart_1647175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647200 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 7]
def baseStart_1647200 : Nat := 118140960795 + 1647200 * 2 ^ 59
def prefixEnd_1647200 : Nat := 4983230072969 + 3 ^ 40 * 1647200 * 2
def baseEnd_1647200 : Nat := 375913481816026913833187

theorem tailTrace_1647200 : CollatzResearch.WordTrace tailWord_1647200 prefixEnd_1647200 375913481816026913833187 := by
  unfold tailWord_1647200
  simp only [CollatzResearch.WordTrace]
  refine ⟨30039159816241597104065527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40052213088322129472087369 30039159816241597104065527)
  ·
    refine ⟨45058739724362395656098291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30039159816241597104065527 45058739724362395656098291)
    ·
      refine ⟨67588109586543593484147437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45058739724362395656098291 67588109586543593484147437)
      ·
        refine ⟨25345541094953847556555289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67588109586543593484147437 25345541094953847556555289)
        ·
          refine ⟨19009155821215385667416467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25345541094953847556555289 19009155821215385667416467)
          ·
            refine ⟨28513733731823078501124701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19009155821215385667416467 28513733731823078501124701)
            ·
              refine ⟨10692650149433654437921763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28513733731823078501124701 10692650149433654437921763)
              ·
                refine ⟨16038975224150481656882645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10692650149433654437921763 16038975224150481656882645)
                ·
                  refine ⟨375913481816026913833187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16038975224150481656882645 375913481816026913833187)
                  ·
                    rfl

theorem cell21_1647200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 7].length) (baseStart_1647200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1647200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1647200 prefixEnd_1647200 := by exact prefixLift 1647200
  have htrace : WordTrace (prefixWord ++ tailWord_1647200) baseStart_1647200 baseEnd_1647200 := by
    simpa [prefixWord, tailWord_1647200, baseEnd_1647200] using wordTrace_append hprefix tailTrace_1647200
  have hstable : (prefixWord ++ tailWord_1647200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647200).length < 2 ^ (prefixWord ++ tailWord_1647200).sum := by decide
  have hdescent : baseEnd_1647200 < baseStart_1647200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647231 : List Nat := [1, 1, 2, 2, 1, 1, 1, 8, 4]
def baseStart_1647231 : Nat := 118140960795 + 1647231 * 2 ^ 59
def prefixEnd_1647231 : Nat := 4983230072969 + 3 ^ 40 * 1647231 * 2
def baseEnd_1647231 : Nat := 375920556438377748816457

theorem tailTrace_1647231 : CollatzResearch.WordTrace tailWord_1647231 prefixEnd_1647231 375920556438377748816457 := by
  unfold tailWord_1647231
  simp only [CollatzResearch.WordTrace]
  refine ⟨60079450295370886502509547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40052966863580591001673031 60079450295370886502509547)
  ·
    refine ⟨90119175443056329753764321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60079450295370886502509547 90119175443056329753764321)
    ·
      refine ⟨67589381582292247315323241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90119175443056329753764321 67589381582292247315323241)
      ·
        refine ⟨50692036186719185486492431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67589381582292247315323241 50692036186719185486492431)
        ·
          refine ⟨76038054280078778229738647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50692036186719185486492431 76038054280078778229738647)
          ·
            refine ⟨114057081420118167344607971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76038054280078778229738647 114057081420118167344607971)
            ·
              refine ⟨171085622130177251016911957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114057081420118167344607971 171085622130177251016911957)
              ·
                refine ⟨2004909634338014660354437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 171085622130177251016911957 2004909634338014660354437)
                ·
                  refine ⟨375920556438377748816457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2004909634338014660354437 375920556438377748816457)
                  ·
                    rfl

theorem cell21_1647231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 4].length) (baseStart_1647231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1647231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1647231 prefixEnd_1647231 := by exact prefixLift 1647231
  have htrace : WordTrace (prefixWord ++ tailWord_1647231) baseStart_1647231 baseEnd_1647231 := by
    simpa [prefixWord, tailWord_1647231, baseEnd_1647231] using wordTrace_append hprefix tailTrace_1647231
  have hstable : (prefixWord ++ tailWord_1647231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647231).length < 2 ^ (prefixWord ++ tailWord_1647231).sum := by decide
  have hdescent : baseEnd_1647231 < baseStart_1647231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647293 : List Nat := [1, 4, 1, 2, 1, 3, 3, 1, 5]
def baseStart_1647293 : Nat := 118140960795 + 1647293 * 2 ^ 59
def prefixEnd_1647293 : Nat := 4983230072969 + 3 ^ 40 * 1647293 * 2
def baseEnd_1647293 : Nat := 375934705683079418782997

theorem tailTrace_1647293 : CollatzResearch.WordTrace tailWord_1647293 prefixEnd_1647293 375934705683079418782997 := by
  unfold tailWord_1647293
  simp only [CollatzResearch.WordTrace]
  refine ⟨60081711621146271091266533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40054474414097514060844355 60081711621146271091266533)
  ·
    refine ⟨11265320928964925829612475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60081711621146271091266533 11265320928964925829612475)
    ·
      refine ⟨16897981393447388744418713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11265320928964925829612475 16897981393447388744418713)
      ·
        refine ⟨12673486045085541558314035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16897981393447388744418713 12673486045085541558314035)
        ·
          refine ⟨19010229067628312337471053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12673486045085541558314035 19010229067628312337471053)
          ·
            refine ⟨7128835900360617126551645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19010229067628312337471053 7128835900360617126551645)
            ·
              refine ⟨2673313462635231422456867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7128835900360617126551645 2673313462635231422456867)
              ·
                refine ⟨4009970193952847133685301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2673313462635231422456867 4009970193952847133685301)
                ·
                  refine ⟨375934705683079418782997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4009970193952847133685301 375934705683079418782997)
                  ·
                    rfl

theorem cell21_1647293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_1647293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1647293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1647293 prefixEnd_1647293 := by exact prefixLift 1647293
  have htrace : WordTrace (prefixWord ++ tailWord_1647293) baseStart_1647293 baseEnd_1647293 := by
    simpa [prefixWord, tailWord_1647293, baseEnd_1647293] using wordTrace_append hprefix tailTrace_1647293
  have hstable : (prefixWord ++ tailWord_1647293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647293).length < 2 ^ (prefixWord ++ tailWord_1647293).sum := by decide
  have hdescent : baseEnd_1647293 < baseStart_1647293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647321 : List Nat := [1, 2, 1, 2, 3, 2, 1, 9]
def baseStart_1647321 : Nat := 118140960795 + 1647321 * 2 ^ 59
def prefixEnd_1647321 : Nat := 4983230072969 + 3 ^ 40 * 1647321 * 2
def baseEnd_1647321 : Nat := 125313698554852530772091

theorem tailTrace_1647321 : CollatzResearch.WordTrace tailWord_1647321 prefixEnd_1647321 125313698554852530772091 := by
  unfold tailWord_1647321
  simp only [CollatzResearch.WordTrace]
  refine ⟨60082732865044831873285817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40055155243363221248857211 60082732865044831873285817)
  ·
    refine ⟨45062049648783623904964363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60082732865044831873285817 45062049648783623904964363)
    ·
      refine ⟨67593074473175435857446545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45062049648783623904964363 67593074473175435857446545)
      ·
        refine ⟨50694805854881576893084909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67593074473175435857446545 50694805854881576893084909)
        ·
          refine ⟨19010552195580591334906841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50694805854881576893084909 19010552195580591334906841)
          ·
            refine ⟨14257914146685443501180131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19010552195580591334906841 14257914146685443501180131)
            ·
              refine ⟨21386871220028165251770197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14257914146685443501180131 21386871220028165251770197)
              ·
                refine ⟨125313698554852530772091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21386871220028165251770197 125313698554852530772091)
                ·
                  rfl

theorem cell21_1647321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 9].length) (baseStart_1647321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1647321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1647321 prefixEnd_1647321 := by exact prefixLift 1647321
  have htrace : WordTrace (prefixWord ++ tailWord_1647321) baseStart_1647321 baseEnd_1647321 := by
    simpa [prefixWord, tailWord_1647321, baseEnd_1647321] using wordTrace_append hprefix tailTrace_1647321
  have hstable : (prefixWord ++ tailWord_1647321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647321).length < 2 ^ (prefixWord ++ tailWord_1647321).sum := by decide
  have hdescent : baseEnd_1647321 < baseStart_1647321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647352 : List Nat := [2, 1, 2, 1, 1, 2, 4, 3, 5]
def baseStart_1647352 : Nat := 118140960795 + 1647352 * 2 ^ 59
def prefixEnd_1647352 : Nat := 4983230072969 + 3 ^ 40 * 1647352 * 2
def baseEnd_1647352 : Nat := 375948170286908427299543

theorem tailTrace_1647352 : CollatzResearch.WordTrace tailWord_1647352 prefixEnd_1647352 375948170286908427299543 := by
  unfold tailWord_1647352
  simp only [CollatzResearch.WordTrace]
  refine ⟨30041931763966262083832155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40055909018621682778442873 30041931763966262083832155)
  ·
    refine ⟨45062897645949393125748233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30041931763966262083832155 45062897645949393125748233)
    ·
      refine ⟨33797173234462044844311175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45062897645949393125748233 33797173234462044844311175)
      ·
        refine ⟨50695759851693067266466763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33797173234462044844311175 50695759851693067266466763)
        ·
          refine ⟨76043639777539600899700145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50695759851693067266466763 76043639777539600899700145)
          ·
            refine ⟨57032729833154700674775109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76043639777539600899700145 57032729833154700674775109)
            ·
              refine ⟨10693636843716506376520333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57032729833154700674775109 10693636843716506376520333)
              ·
                refine ⟨4010113816393689891195125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10693636843716506376520333 4010113816393689891195125)
                ·
                  refine ⟨375948170286908427299543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4010113816393689891195125 375948170286908427299543)
                  ·
                    rfl

theorem cell21_1647352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 5].length) (baseStart_1647352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1647352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1647352 prefixEnd_1647352 := by exact prefixLift 1647352
  have htrace : WordTrace (prefixWord ++ tailWord_1647352) baseStart_1647352 baseEnd_1647352 := by
    simpa [prefixWord, tailWord_1647352, baseEnd_1647352] using wordTrace_append hprefix tailTrace_1647352
  have hstable : (prefixWord ++ tailWord_1647352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647352).length < 2 ^ (prefixWord ++ tailWord_1647352).sum := by decide
  have hdescent : baseEnd_1647352 < baseStart_1647352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647386 : List Nat := [3, 1, 1, 3, 2, 1, 4, 3, 3]
def baseStart_1647386 : Nat := 118140960795 + 1647386 * 2 ^ 59
def prefixEnd_1647386 : Nat := 4983230072969 + 3 ^ 40 * 1647386 * 2
def baseEnd_1647386 : Nat := 375955929550131923732807

theorem tailTrace_1647386 : CollatzResearch.WordTrace tailWord_1647386 prefixEnd_1647386 375955929550131923732807 := by
  unfold tailWord_1647386
  simp only [CollatzResearch.WordTrace]
  refine ⟨15021275902452336993600503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40056735739872898649601341 15021275902452336993600503)
  ·
    refine ⟨22531913853678505490400755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15021275902452336993600503 22531913853678505490400755)
    ·
      refine ⟨33797870780517758235601133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22531913853678505490400755 33797870780517758235601133)
      ·
        refine ⟨12674201542694159338350425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33797870780517758235601133 12674201542694159338350425)
        ·
          refine ⟨9505651157020619503762819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12674201542694159338350425 9505651157020619503762819)
          ·
            refine ⟨14258476735530929255644229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9505651157020619503762819 14258476735530929255644229)
            ·
              refine ⟨2673464387912049235433293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14258476735530929255644229 2673464387912049235433293)
              ·
                refine ⟨1002549145467018463287485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2673464387912049235433293 1002549145467018463287485)
                ·
                  refine ⟨375955929550131923732807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1002549145467018463287485 375955929550131923732807)
                  ·
                    rfl

theorem cell21_1647386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3, 3].length) (baseStart_1647386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1647386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1647386 prefixEnd_1647386 := by exact prefixLift 1647386
  have htrace : WordTrace (prefixWord ++ tailWord_1647386) baseStart_1647386 baseEnd_1647386 := by
    simpa [prefixWord, tailWord_1647386, baseEnd_1647386] using wordTrace_append hprefix tailTrace_1647386
  have hstable : (prefixWord ++ tailWord_1647386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647386).length < 2 ^ (prefixWord ++ tailWord_1647386).sum := by decide
  have hdescent : baseEnd_1647386 < baseStart_1647386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647397 : List Nat := [1, 3, 1, 2, 3, 1, 10]
def baseStart_1647397 : Nat := 118140960795 + 1647397 * 2 ^ 59
def prefixEnd_1647397 : Nat := 4983230072969 + 3 ^ 40 * 1647397 * 2
def baseEnd_1647397 : Nat := 41773159988888705449939

theorem tailTrace_1647397 : CollatzResearch.WordTrace tailWord_1647397 prefixEnd_1647397 41773159988888705449939 := by
  unfold tailWord_1647397
  simp only [CollatzResearch.WordTrace]
  refine ⟨60085504812769496853052445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40057003208512997902034963 60085504812769496853052445)
  ·
    refine ⟨22532064304788561319894667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60085504812769496853052445 22532064304788561319894667)
    ·
      refine ⟨33798096457182841979842001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22532064304788561319894667 33798096457182841979842001)
      ·
        refine ⟨25348572342887131484881501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33798096457182841979842001 25348572342887131484881501)
        ·
          refine ⟨9505714628582674306830563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25348572342887131484881501 9505714628582674306830563)
          ·
            refine ⟨14258571942874011460245845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9505714628582674306830563 14258571942874011460245845)
            ·
              refine ⟨41773159988888705449939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14258571942874011460245845 41773159988888705449939)
              ·
                rfl

theorem cell21_1647397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 10].length) (baseStart_1647397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1647397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1647397 prefixEnd_1647397 := by exact prefixLift 1647397
  have htrace : WordTrace (prefixWord ++ tailWord_1647397) baseStart_1647397 baseEnd_1647397 := by
    simpa [prefixWord, tailWord_1647397, baseEnd_1647397] using wordTrace_append hprefix tailTrace_1647397
  have hstable : (prefixWord ++ tailWord_1647397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647397).length < 2 ^ (prefixWord ++ tailWord_1647397).sum := by decide
  have hdescent : baseEnd_1647397 < baseStart_1647397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647437 : List Nat := [1, 6, 1, 2, 3, 1, 1, 3, 3]
def baseStart_1647437 : Nat := 118140960795 + 1647437 * 2 ^ 59
def prefixEnd_1647437 : Nat := 4983230072969 + 3 ^ 40 * 1647437 * 2
def baseEnd_1647437 : Nat := 375967568444967168382703

theorem tailTrace_1647437 : CollatzResearch.WordTrace tailWord_1647437 prefixEnd_1647437 375967568444967168382703 := by
  unfold tailWord_1647437
  simp only [CollatzResearch.WordTrace]
  refine ⟨60086963732624583684508565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40057975821749722456339043 60086963732624583684508565)
  ·
    refine ⟨2816576424966777360211339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 60086963732624583684508565 2816576424966777360211339)
    ·
      refine ⟨4224864637450166040317009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2816576424966777360211339 4224864637450166040317009)
      ·
        refine ⟨3168648478087624530237757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4224864637450166040317009 3168648478087624530237757)
        ·
          refine ⟨1188243179282859198839159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3168648478087624530237757 1188243179282859198839159)
          ·
            refine ⟨1782364768924288798258739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1188243179282859198839159 1782364768924288798258739)
            ·
              refine ⟨2673547153386433197388109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1782364768924288798258739 2673547153386433197388109)
              ·
                refine ⟨1002580182519912449020541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2673547153386433197388109 1002580182519912449020541)
                ·
                  refine ⟨375967568444967168382703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1002580182519912449020541 375967568444967168382703)
                  ·
                    rfl

theorem cell21_1647437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_1647437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1647437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1647437 prefixEnd_1647437 := by exact prefixLift 1647437
  have htrace : WordTrace (prefixWord ++ tailWord_1647437) baseStart_1647437 baseEnd_1647437 := by
    simpa [prefixWord, tailWord_1647437, baseEnd_1647437] using wordTrace_append hprefix tailTrace_1647437
  have hstable : (prefixWord ++ tailWord_1647437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647437).length < 2 ^ (prefixWord ++ tailWord_1647437).sum := by decide
  have hdescent : baseEnd_1647437 < baseStart_1647437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647459 : List Nat := [1, 1, 1, 5, 3, 1, 2, 1, 6]
def baseStart_1647459 : Nat := 118140960795 + 1647459 * 2 ^ 59
def prefixEnd_1647459 : Nat := 4983230072969 + 3 ^ 40 * 1647459 * 2
def baseEnd_1647459 : Nat := 375972589144700019015991

theorem tailTrace_1647459 : CollatzResearch.WordTrace tailWord_1647459 prefixEnd_1647459 375972589144700019015991 := by
  unfold tailWord_1647459
  simp only [CollatzResearch.WordTrace]
  refine ⟨60087766138544881441809431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40058510759029920961206287 60087766138544881441809431)
  ·
    refine ⟨90131649207817322162714147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60087766138544881441809431 90131649207817322162714147)
    ·
      refine ⟨135197473811725983244071221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90131649207817322162714147 135197473811725983244071221)
      ·
        refine ⟨12674763169849310929131677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135197473811725983244071221 12674763169849310929131677)
        ·
          refine ⟨4753036188693491598424379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12674763169849310929131677 4753036188693491598424379)
          ·
            refine ⟨7129554283040237397636569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4753036188693491598424379 7129554283040237397636569)
            ·
              refine ⟨5347165712280178048227427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7129554283040237397636569 5347165712280178048227427)
              ·
                refine ⟨8020748568420267072341141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5347165712280178048227427 8020748568420267072341141)
                ·
                  refine ⟨375972589144700019015991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8020748568420267072341141 375972589144700019015991)
                  ·
                    rfl

theorem cell21_1647459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 6].length) (baseStart_1647459 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1647459 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1647459 prefixEnd_1647459 := by exact prefixLift 1647459
  have htrace : WordTrace (prefixWord ++ tailWord_1647459) baseStart_1647459 baseEnd_1647459 := by
    simpa [prefixWord, tailWord_1647459, baseEnd_1647459] using wordTrace_append hprefix tailTrace_1647459
  have hstable : (prefixWord ++ tailWord_1647459).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647459).length < 2 ^ (prefixWord ++ tailWord_1647459).sum := by decide
  have hdescent : baseEnd_1647459 < baseStart_1647459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647473 : List Nat := [1, 2, 2, 2, 1, 4, 1, 8]
def baseStart_1647473 : Nat := 118140960795 + 1647473 * 2 ^ 59
def prefixEnd_1647473 : Nat := 4983230072969 + 3 ^ 40 * 1647473 * 2
def baseEnd_1647473 : Nat := 125325261378479701927543

theorem tailTrace_1647473 : CollatzResearch.WordTrace tailWord_1647473 prefixEnd_1647473 125325261378479701927543 := by
  unfold tailWord_1647473
  simp only [CollatzResearch.WordTrace]
  refine ⟨60088276760494161832819073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40058851173662774555212715 60088276760494161832819073)
  ·
    refine ⟨45066207570370621374614305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60088276760494161832819073 45066207570370621374614305)
    ·
      refine ⟨33799655677777966030960729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45066207570370621374614305 33799655677777966030960729)
      ·
        refine ⟨25349741758333474523220547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33799655677777966030960729 25349741758333474523220547)
        ·
          refine ⟨38024612637500211784830821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25349741758333474523220547 38024612637500211784830821)
          ·
            refine ⟨7129614869531289709655779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38024612637500211784830821 7129614869531289709655779)
            ·
              refine ⟨10694422304296934564483669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7129614869531289709655779 10694422304296934564483669)
              ·
                refine ⟨125325261378479701927543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10694422304296934564483669 125325261378479701927543)
                ·
                  rfl

theorem cell21_1647473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 8].length) (baseStart_1647473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1647473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1647473 prefixEnd_1647473 := by exact prefixLift 1647473
  have htrace : WordTrace (prefixWord ++ tailWord_1647473) baseStart_1647473 baseEnd_1647473 := by
    simpa [prefixWord, tailWord_1647473, baseEnd_1647473] using wordTrace_append hprefix tailTrace_1647473
  have hstable : (prefixWord ++ tailWord_1647473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647473).length < 2 ^ (prefixWord ++ tailWord_1647473).sum := by decide
  have hdescent : baseEnd_1647473 < baseStart_1647473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647510 : List Nat := [5, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_1647510 : Nat := 118140960795 + 1647510 * 2 ^ 59
def prefixEnd_1647510 : Nat := 4983230072969 + 3 ^ 40 * 1647510 * 2
def baseEnd_1647510 : Nat := 375984228039535263665887

theorem tailTrace_1647510 : CollatzResearch.WordTrace tailWord_1647510 prefixEnd_1647510 375984228039535263665887 := by
  unfold tailWord_1647510
  simp only [CollatzResearch.WordTrace]
  refine ⟨3755601641335007321994749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40059750840906744767943989 3755601641335007321994749)
  ·
    refine ⟨1408350615500627745748031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3755601641335007321994749 1408350615500627745748031)
    ·
      refine ⟨2112525923250941618622047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1408350615500627745748031 2112525923250941618622047)
      ·
        refine ⟨3168788884876412427933071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2112525923250941618622047 3168788884876412427933071)
        ·
          refine ⟨4753183327314618641899607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3168788884876412427933071 4753183327314618641899607)
          ·
            refine ⟨7129774990971927962849411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4753183327314618641899607 7129774990971927962849411)
            ·
              refine ⟨10694662486457891944274117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7129774990971927962849411 10694662486457891944274117)
              ·
                refine ⟨2005249216210854739551397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10694662486457891944274117 2005249216210854739551397)
                ·
                  refine ⟨375984228039535263665887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2005249216210854739551397 375984228039535263665887)
                  ·
                    rfl

theorem cell21_1647510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_1647510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1647510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1647510 prefixEnd_1647510 := by exact prefixLift 1647510
  have htrace : WordTrace (prefixWord ++ tailWord_1647510) baseStart_1647510 baseEnd_1647510 := by
    simpa [prefixWord, tailWord_1647510, baseEnd_1647510] using wordTrace_append hprefix tailTrace_1647510
  have hstable : (prefixWord ++ tailWord_1647510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647510).length < 2 ^ (prefixWord ++ tailWord_1647510).sum := by decide
  have hdescent : baseEnd_1647510 < baseStart_1647510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647586 : List Nat := [3, 3, 3, 1, 1, 2, 3, 1, 4]
def baseStart_1647586 : Nat := 118140960795 + 1647586 * 2 ^ 59
def prefixEnd_1647586 : Nat := 4983230072969 + 3 ^ 40 * 1647586 * 2
def baseEnd_1647586 : Nat := 376001572274976020399065

theorem tailTrace_1647586 : CollatzResearch.WordTrace tailWord_1647586 prefixEnd_1647586 376001572274976020399065 := by
  unfold tailWord_1647586
  simp only [CollatzResearch.WordTrace]
  refine ⟨15023099552271195532920653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40061598806056521421121741 15023099552271195532920653)
  ·
    refine ⟨5633662332101698324845245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15023099552271195532920653 5633662332101698324845245)
    ·
      refine ⟨2112623374538136871816967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5633662332101698324845245 2112623374538136871816967)
      ·
        refine ⟨3168935061807205307725451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2112623374538136871816967 3168935061807205307725451)
        ·
          refine ⟨4753402592710807961588177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3168935061807205307725451 4753402592710807961588177)
          ·
            refine ⟨3565051944533105971191133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4753402592710807961588177 3565051944533105971191133)
            ·
              refine ⟨1336894479199914739196675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3565051944533105971191133 1336894479199914739196675)
              ·
                refine ⟨2005341718799872108795013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1336894479199914739196675 2005341718799872108795013)
                ·
                  refine ⟨376001572274976020399065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2005341718799872108795013 376001572274976020399065)
                  ·
                    rfl

theorem cell21_1647586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_1647586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1647586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1647586 prefixEnd_1647586 := by exact prefixLift 1647586
  have htrace : WordTrace (prefixWord ++ tailWord_1647586) baseStart_1647586 baseEnd_1647586 := by
    simpa [prefixWord, tailWord_1647586, baseEnd_1647586] using wordTrace_append hprefix tailTrace_1647586
  have hstable : (prefixWord ++ tailWord_1647586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647586).length < 2 ^ (prefixWord ++ tailWord_1647586).sum := by decide
  have hdescent : baseEnd_1647586 < baseStart_1647586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647687 : List Nat := [1, 1, 4, 1, 3, 2, 1, 4, 4]
def baseStart_1647687 : Nat := 118140960795 + 1647687 * 2 ^ 59
def prefixEnd_1647687 : Nat := 4983230072969 + 3 ^ 40 * 1647687 * 2
def baseEnd_1647687 : Nat := 376024621851022289215525

theorem tailTrace_1647687 : CollatzResearch.WordTrace tailWord_1647687 prefixEnd_1647687 376024621851022289215525 := by
  unfold tailWord_1647687
  simp only [CollatzResearch.WordTrace]
  refine ⟨60096081981718876381109315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40064054654479250920739543 60096081981718876381109315)
  ·
    refine ⟨90144122972578314571663973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60096081981718876381109315 90144122972578314571663973)
    ·
      refine ⟨16902023057358433982186995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90144122972578314571663973 16902023057358433982186995)
      ·
        refine ⟨25353034586037650973280493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16902023057358433982186995 25353034586037650973280493)
        ·
          refine ⟨9507387969764119114980185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25353034586037650973280493 9507387969764119114980185)
          ·
            refine ⟨7130540977323089336235139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9507387969764119114980185 7130540977323089336235139)
            ·
              refine ⟨10695811465984634004352709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7130540977323089336235139 10695811465984634004352709)
              ·
                refine ⟨2005464649872118875816133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10695811465984634004352709 2005464649872118875816133)
                ·
                  refine ⟨376024621851022289215525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2005464649872118875816133 376024621851022289215525)
                  ·
                    rfl

theorem cell21_1647687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 4].length) (baseStart_1647687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1647687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1647687 prefixEnd_1647687 := by exact prefixLift 1647687
  have htrace : WordTrace (prefixWord ++ tailWord_1647687) baseStart_1647687 baseEnd_1647687 := by
    simpa [prefixWord, tailWord_1647687, baseEnd_1647687] using wordTrace_append hprefix tailTrace_1647687
  have hstable : (prefixWord ++ tailWord_1647687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647687).length < 2 ^ (prefixWord ++ tailWord_1647687).sum := by decide
  have hdescent : baseEnd_1647687 < baseStart_1647687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647690 : List Nat := [3, 1, 2, 1, 1, 2, 6, 2, 3]
def baseStart_1647690 : Nat := 118140960795 + 1647690 * 2 ^ 59
def prefixEnd_1647690 : Nat := 4983230072969 + 3 ^ 40 * 1647690 * 2
def baseEnd_1647690 : Nat := 376025306491894950665519

theorem tailTrace_1647690 : CollatzResearch.WordTrace tailWord_1647690 prefixEnd_1647690 376025306491894950665519 := by
  unfold tailWord_1647690
  simp only [CollatzResearch.WordTrace]
  refine ⟨15024047850177001973367131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40064127600472005262312349 15024047850177001973367131)
  ·
    refine ⟨22536071775265502960050697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15024047850177001973367131 22536071775265502960050697)
    ·
      refine ⟨16902053831449127220038023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22536071775265502960050697 16902053831449127220038023)
      ·
        refine ⟨25353080747173690830057035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16902053831449127220038023 25353080747173690830057035)
        ·
          refine ⟨38029621120760536245085553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25353080747173690830057035 38029621120760536245085553)
          ·
            refine ⟨28522215840570402183814165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38029621120760536245085553 28522215840570402183814165)
            ·
              refine ⟨1336978867526737602366289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28522215840570402183814165 1336978867526737602366289)
              ·
                refine ⟨1002734150645053201774717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1336978867526737602366289 1002734150645053201774717)
                ·
                  refine ⟨376025306491894950665519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1002734150645053201774717 376025306491894950665519)
                  ·
                    rfl

theorem cell21_1647690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2, 3].length) (baseStart_1647690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1647690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1647690 prefixEnd_1647690 := by exact prefixLift 1647690
  have htrace : WordTrace (prefixWord ++ tailWord_1647690) baseStart_1647690 baseEnd_1647690 := by
    simpa [prefixWord, tailWord_1647690, baseEnd_1647690] using wordTrace_append hprefix tailTrace_1647690
  have hstable : (prefixWord ++ tailWord_1647690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647690).length < 2 ^ (prefixWord ++ tailWord_1647690).sum := by decide
  have hdescent : baseEnd_1647690 < baseStart_1647690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647749 : List Nat := [1, 3, 1, 1, 6, 1, 2, 1, 5]
def baseStart_1647749 : Nat := 118140960795 + 1647749 * 2 ^ 59
def prefixEnd_1647749 : Nat := 4983230072969 + 3 ^ 40 * 1647749 * 2
def baseEnd_1647749 : Nat := 376038771095723959182065

theorem tailTrace_1647749 : CollatzResearch.WordTrace tailWord_1647749 prefixEnd_1647749 376038771095723959182065 := by
  unfold tailWord_1647749
  simp only [CollatzResearch.WordTrace]
  refine ⟨60098343307494260969866301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40065562204996173979910867 60098343307494260969866301)
  ·
    refine ⟨22536878740310347863699863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60098343307494260969866301 22536878740310347863699863)
    ·
      refine ⟨33805318110465521795549795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22536878740310347863699863 33805318110465521795549795)
      ·
        refine ⟨50707977165698282693324693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33805318110465521795549795 50707977165698282693324693)
        ·
          refine ⟨2376936429642107001249595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50707977165698282693324693 2376936429642107001249595)
          ·
            refine ⟨3565404644463160501874393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2376936429642107001249595 3565404644463160501874393)
            ·
              refine ⟨2674053483347370376405795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3565404644463160501874393 2674053483347370376405795)
              ·
                refine ⟨4011080225021055564608693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2674053483347370376405795 4011080225021055564608693)
                ·
                  refine ⟨376038771095723959182065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4011080225021055564608693 376038771095723959182065)
                  ·
                    rfl

theorem cell21_1647749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_1647749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1647749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1647749 prefixEnd_1647749 := by exact prefixLift 1647749
  have htrace : WordTrace (prefixWord ++ tailWord_1647749) baseStart_1647749 baseEnd_1647749 := by
    simpa [prefixWord, tailWord_1647749, baseEnd_1647749] using wordTrace_append hprefix tailTrace_1647749
  have hstable : (prefixWord ++ tailWord_1647749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647749).length < 2 ^ (prefixWord ++ tailWord_1647749).sum := by decide
  have hdescent : baseEnd_1647749 < baseStart_1647749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647777 : List Nat := [1, 2, 3, 3, 1, 1, 3, 7]
def baseStart_1647777 : Nat := 118140960795 + 1647777 * 2 ^ 59
def prefixEnd_1647777 : Nat := 4983230072969 + 3 ^ 40 * 1647777 * 2
def baseEnd_1647777 : Nat := 125348387025734044238447

theorem tailTrace_1647777 : CollatzResearch.WordTrace tailWord_1647777 prefixEnd_1647777 125348387025734044238447 := by
  unfold tailWord_1647777
  simp only [CollatzResearch.WordTrace]
  refine ⟨60099364551392821751885585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40066243034261881167923723 60099364551392821751885585)
  ·
    refine ⟨45074523413544616313914189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60099364551392821751885585 45074523413544616313914189)
    ·
      refine ⟨16902946280079231117717821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45074523413544616313914189 16902946280079231117717821)
      ·
        refine ⟨6338604855029711669144183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16902946280079231117717821 6338604855029711669144183)
        ·
          refine ⟨9507907282544567503716275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6338604855029711669144183 9507907282544567503716275)
          ·
            refine ⟨14261860923816851255574413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9507907282544567503716275 14261860923816851255574413)
            ·
              refine ⟨5348197846431319220840405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14261860923816851255574413 5348197846431319220840405)
              ·
                refine ⟨125348387025734044238447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5348197846431319220840405 125348387025734044238447)
                ·
                  rfl

theorem cell21_1647777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 7].length) (baseStart_1647777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1647777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1647777 prefixEnd_1647777 := by exact prefixLift 1647777
  have htrace : WordTrace (prefixWord ++ tailWord_1647777) baseStart_1647777 baseEnd_1647777 := by
    simpa [prefixWord, tailWord_1647777, baseEnd_1647777] using wordTrace_append hprefix tailTrace_1647777
  have hstable : (prefixWord ++ tailWord_1647777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647777).length < 2 ^ (prefixWord ++ tailWord_1647777).sum := by decide
  have hdescent : baseEnd_1647777 < baseStart_1647777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647783 : List Nat := [1, 1, 6, 2, 1, 3, 1, 3, 3]
def baseStart_1647783 : Nat := 118140960795 + 1647783 * 2 ^ 59
def prefixEnd_1647783 : Nat := 4983230072969 + 3 ^ 40 * 1647783 * 2
def baseEnd_1647783 : Nat := 376046530358947455615329

theorem tailTrace_1647783 : CollatzResearch.WordTrace tailWord_1647783 prefixEnd_1647783 376046530358947455615329 := by
  unfold tailWord_1647783
  simp only [CollatzResearch.WordTrace]
  refine ⟨60099583389371084776604003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40066388926247389851069335 60099583389371084776604003)
  ·
    refine ⟨90149375084056627164906005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60099583389371084776604003 90149375084056627164906005)
    ·
      refine ⟨4225751957065154398354969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 90149375084056627164906005 4225751957065154398354969)
      ·
        refine ⟨3169313967798865798766227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4225751957065154398354969 3169313967798865798766227)
        ·
          refine ⟨4753970951698298698149341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3169313967798865798766227 4753970951698298698149341)
          ·
            refine ⟨1782739106886862011806003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4753970951698298698149341 1782739106886862011806003)
            ·
              refine ⟨2674108660330293017709005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1782739106886862011806003 2674108660330293017709005)
              ·
                refine ⟨1002790747623859881640877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2674108660330293017709005 1002790747623859881640877)
                ·
                  refine ⟨376046530358947455615329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1002790747623859881640877 376046530358947455615329)
                  ·
                    rfl

theorem cell21_1647783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3, 3].length) (baseStart_1647783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1647783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1647783 prefixEnd_1647783 := by exact prefixLift 1647783
  have htrace : WordTrace (prefixWord ++ tailWord_1647783) baseStart_1647783 baseEnd_1647783 := by
    simpa [prefixWord, tailWord_1647783, baseEnd_1647783] using wordTrace_append hprefix tailTrace_1647783
  have hstable : (prefixWord ++ tailWord_1647783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647783).length < 2 ^ (prefixWord ++ tailWord_1647783).sum := by decide
  have hdescent : baseEnd_1647783 < baseStart_1647783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647791 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 7]
def baseStart_1647791 : Nat := 118140960795 + 1647791 * 2 ^ 59
def prefixEnd_1647791 : Nat := 4983230072969 + 3 ^ 40 * 1647791 * 2
def baseEnd_1647791 : Nat := 376048356067941219481979

theorem tailTrace_1647791 : CollatzResearch.WordTrace tailWord_1647791 prefixEnd_1647791 376048356067941219481979 := by
  unfold tailWord_1647791
  simp only [CollatzResearch.WordTrace]
  refine ⟨60099875173342102142895227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40066583448894734761930151 60099875173342102142895227)
  ·
    refine ⟨90149812760013153214342841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60099875173342102142895227 90149812760013153214342841)
    ·
      refine ⟨67612359570009864910757131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90149812760013153214342841 67612359570009864910757131)
      ·
        refine ⟨101418539355014797366135697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67612359570009864910757131 101418539355014797366135697)
        ·
          refine ⟨76063904516261098024601773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101418539355014797366135697 76063904516261098024601773)
          ·
            refine ⟨28523964193597911759225665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76063904516261098024601773 28523964193597911759225665)
            ·
              refine ⟨21392973145198433819419249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28523964193597911759225665 21392973145198433819419249)
              ·
                refine ⟨16044729858898825364564437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21392973145198433819419249 16044729858898825364564437)
                ·
                  refine ⟨376048356067941219481979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16044729858898825364564437 376048356067941219481979)
                  ·
                    rfl

theorem cell21_1647791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 7].length) (baseStart_1647791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1647791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1647791 prefixEnd_1647791 := by exact prefixLift 1647791
  have htrace : WordTrace (prefixWord ++ tailWord_1647791) baseStart_1647791 baseEnd_1647791 := by
    simpa [prefixWord, tailWord_1647791, baseEnd_1647791] using wordTrace_append hprefix tailTrace_1647791
  have hstable : (prefixWord ++ tailWord_1647791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647791).length < 2 ^ (prefixWord ++ tailWord_1647791).sum := by decide
  have hdescent : baseEnd_1647791 < baseStart_1647791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647853 : List Nat := [1, 5, 1, 2, 2, 10]
def baseStart_1647853 : Nat := 118140960795 + 1647853 * 2 ^ 59
def prefixEnd_1647853 : Nat := 4983230072969 + 3 ^ 40 * 1647853 * 2
def baseEnd_1647853 : Nat := 13928240937505292201797

theorem tailTrace_1647853 : CollatzResearch.WordTrace tailWord_1647853 prefixEnd_1647853 13928240937505292201797 := by
  unfold tailWord_1647853
  simp only [CollatzResearch.WordTrace]
  refine ⟨60102136499117486731652213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40068090999411657821101475 60102136499117486731652213)
  ·
    refine ⟨5634575296792264381092395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60102136499117486731652213 5634575296792264381092395)
    ·
      refine ⟨8451862945188396571638593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5634575296792264381092395 8451862945188396571638593)
      ·
        refine ⟨6338897208891297428728945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8451862945188396571638593 6338897208891297428728945)
        ·
          refine ⟨4754172906668473071546709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6338897208891297428728945 4754172906668473071546709)
          ·
            refine ⟨13928240937505292201797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4754172906668473071546709 13928240937505292201797)
            ·
              rfl

theorem cell21_1647853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 10].length) (baseStart_1647853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1647853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1647853 prefixEnd_1647853 := by exact prefixLift 1647853
  have htrace : WordTrace (prefixWord ++ tailWord_1647853) baseStart_1647853 baseEnd_1647853 := by
    simpa [prefixWord, tailWord_1647853, baseEnd_1647853] using wordTrace_append hprefix tailTrace_1647853
  have hstable : (prefixWord ++ tailWord_1647853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647853).length < 2 ^ (prefixWord ++ tailWord_1647853).sum := by decide
  have hdescent : baseEnd_1647853 < baseStart_1647853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647870 : List Nat := [4, 2, 2, 1, 1, 2, 3, 6]
def baseStart_1647870 : Nat := 118140960795 + 1647870 * 2 ^ 59
def prefixEnd_1647870 : Nat := 4983230072969 + 3 ^ 40 * 1647870 * 2
def baseEnd_1647870 : Nat := 125355461648084879221717

theorem tailTrace_1647870 : CollatzResearch.WordTrace tailWord_1647870 prefixEnd_1647870 125355461648084879221717 := by
  unfold tailWord_1647870
  simp only [CollatzResearch.WordTrace]
  refine ⟨7512844567506987329377633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40068504360037265756680709 7512844567506987329377633)
  ·
    refine ⟨5634633425630240497033225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7512844567506987329377633 5634633425630240497033225)
    ·
      refine ⟨4225975069222680372774919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5634633425630240497033225 4225975069222680372774919)
      ·
        refine ⟨6338962603834020559162379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4225975069222680372774919 6338962603834020559162379)
        ·
          refine ⟨9508443905751030838743569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6338962603834020559162379 9508443905751030838743569)
          ·
            refine ⟨7131332929313273129057677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9508443905751030838743569 7131332929313273129057677)
            ·
              refine ⟨2674249848492477423396629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7131332929313273129057677 2674249848492477423396629)
              ·
                refine ⟨125355461648084879221717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2674249848492477423396629 125355461648084879221717)
                ·
                  rfl

theorem cell21_1647870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_1647870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1647870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1647870 prefixEnd_1647870 := by exact prefixLift 1647870
  have htrace : WordTrace (prefixWord ++ tailWord_1647870) baseStart_1647870 baseEnd_1647870 := by
    simpa [prefixWord, tailWord_1647870, baseEnd_1647870] using wordTrace_append hprefix tailTrace_1647870
  have hstable : (prefixWord ++ tailWord_1647870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647870).length < 2 ^ (prefixWord ++ tailWord_1647870).sum := by decide
  have hdescent : baseEnd_1647870 < baseStart_1647870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647884 : List Nat := [2, 2, 1, 2, 2, 4, 1, 2, 5]
def baseStart_1647884 : Nat := 118140960795 + 1647884 * 2 ^ 59
def prefixEnd_1647884 : Nat := 4983230072969 + 3 ^ 40 * 1647884 * 2
def baseEnd_1647884 : Nat := 376069579934993724431789

theorem tailTrace_1647884 : CollatzResearch.WordTrace tailWord_1647884 prefixEnd_1647884 376069579934993724431789 := by
  unfold tailWord_1647884
  simp only [CollatzResearch.WordTrace]
  refine ⟨30051633581002589513015353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40068844774670119350687137 30051633581002589513015353)
  ·
    refine ⟨22538725185751942134761515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30051633581002589513015353 22538725185751942134761515)
    ·
      refine ⟨33808087778627913202142273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22538725185751942134761515 33808087778627913202142273)
      ·
        refine ⟨25356065833970934901606705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33808087778627913202142273 25356065833970934901606705)
        ·
          refine ⟨19017049375478201176205029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25356065833970934901606705 19017049375478201176205029)
          ·
            refine ⟨3565696757902162720538443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19017049375478201176205029 3565696757902162720538443)
            ·
              refine ⟨5348545136853244080807665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3565696757902162720538443 5348545136853244080807665)
              ·
                refine ⟨4011408852639933060605749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5348545136853244080807665 4011408852639933060605749)
                ·
                  refine ⟨376069579934993724431789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4011408852639933060605749 376069579934993724431789)
                  ·
                    rfl

theorem cell21_1647884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_1647884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1647884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1647884 prefixEnd_1647884 := by exact prefixLift 1647884
  have htrace : WordTrace (prefixWord ++ tailWord_1647884) baseStart_1647884 baseEnd_1647884 := by
    simpa [prefixWord, tailWord_1647884, baseEnd_1647884] using wordTrace_append hprefix tailTrace_1647884
  have hstable : (prefixWord ++ tailWord_1647884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647884).length < 2 ^ (prefixWord ++ tailWord_1647884).sum := by decide
  have hdescent : baseEnd_1647884 < baseStart_1647884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647932 : List Nat := [2, 2, 2, 2, 1, 4, 3, 1, 4]
def baseStart_1647932 : Nat := 118140960795 + 1647932 * 2 ^ 59
def prefixEnd_1647932 : Nat := 4983230072969 + 3 ^ 40 * 1647932 * 2
def baseEnd_1647932 : Nat := 376080534188956307631691

theorem tailTrace_1647932 : CollatzResearch.WordTrace tailWord_1647932 prefixEnd_1647932 376080534188956307631691 := by
  unfold tailWord_1647932
  simp only [CollatzResearch.WordTrace]
  refine ⟨30052508932915641611889025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40070011910554188815852033 30052508932915641611889025)
  ·
    refine ⟨22539381699686731208916769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30052508932915641611889025 22539381699686731208916769)
    ·
      refine ⟨16904536274765048406687577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22539381699686731208916769 16904536274765048406687577)
      ·
        refine ⟨12678402206073786305015683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16904536274765048406687577 12678402206073786305015683)
        ·
          refine ⟨19017603309110679457523525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12678402206073786305015683 19017603309110679457523525)
          ·
            refine ⟨3565800620458252398285661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19017603309110679457523525 3565800620458252398285661)
            ·
              refine ⟨1337175232671844649357123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3565800620458252398285661 1337175232671844649357123)
              ·
                refine ⟨2005762849007766974035685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1337175232671844649357123 2005762849007766974035685)
                ·
                  refine ⟨376080534188956307631691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2005762849007766974035685 376080534188956307631691)
                  ·
                    rfl

theorem cell21_1647932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_1647932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1647932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1647932 prefixEnd_1647932 := by exact prefixLift 1647932
  have htrace : WordTrace (prefixWord ++ tailWord_1647932) baseStart_1647932 baseEnd_1647932 := by
    simpa [prefixWord, tailWord_1647932, baseEnd_1647932] using wordTrace_append hprefix tailTrace_1647932
  have hstable : (prefixWord ++ tailWord_1647932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647932).length < 2 ^ (prefixWord ++ tailWord_1647932).sum := by decide
  have hdescent : baseEnd_1647932 < baseStart_1647932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648022 : List Nat := [5, 3, 1, 12]
def baseStart_1648022 : Nat := 118140960795 + 1648022 * 2 ^ 59
def prefixEnd_1648022 : Nat := 4983230072969 + 3 ^ 40 * 1648022 * 2
def baseEnd_1648022 : Nat := 1547741042860642597249

theorem tailTrace_1648022 : CollatzResearch.WordTrace tailWord_1648022 prefixEnd_1648022 1547741042860642597249 := by
  unfold tailWord_1648022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3756768777219076787159645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40072200290336819063036213 3756768777219076787159645)
  ·
    refine ⟨1408788291457153795184867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3756768777219076787159645 1408788291457153795184867)
    ·
      refine ⟨2113182437185730692777301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1408788291457153795184867 2113182437185730692777301)
      ·
        refine ⟨1547741042860642597249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 2113182437185730692777301 1547741042860642597249)
        ·
          rfl

theorem cell21_1648022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 12].length) (baseStart_1648022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1648022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1648022 prefixEnd_1648022 := by exact prefixLift 1648022
  have htrace : WordTrace (prefixWord ++ tailWord_1648022) baseStart_1648022 baseEnd_1648022 := by
    simpa [prefixWord, tailWord_1648022, baseEnd_1648022] using wordTrace_append hprefix tailTrace_1648022
  have hstable : (prefixWord ++ tailWord_1648022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648022).length < 2 ^ (prefixWord ++ tailWord_1648022).sum := by decide
  have hdescent : baseEnd_1648022 < baseStart_1648022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648028 : List Nat := [2, 2, 3, 4, 1, 2, 2, 2, 3]
def baseStart_1648028 : Nat := 118140960795 + 1648028 * 2 ^ 59
def prefixEnd_1648028 : Nat := 4983230072969 + 3 ^ 40 * 1648028 * 2
def baseEnd_1648028 : Nat := 376102442696881474031495

theorem tailTrace_1648028 : CollatzResearch.WordTrace tailWord_1648028 prefixEnd_1648028 376102442696881474031495 := by
  unfold tailWord_1648028
  simp only [CollatzResearch.WordTrace]
  refine ⟨30054259636741745809636369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40072346182322327746181825 30054259636741745809636369)
  ·
    refine ⟨22540694727556309357227277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30054259636741745809636369 22540694727556309357227277)
    ·
      refine ⟨8452760522833616008960229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22540694727556309357227277 8452760522833616008960229)
      ·
        refine ⟨1584892598031303001680043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8452760522833616008960229 1584892598031303001680043)
        ·
          refine ⟨2377338897046954502520065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1584892598031303001680043 2377338897046954502520065)
          ·
            refine ⟨1783004172785215876890049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2377338897046954502520065 1783004172785215876890049)
            ·
              refine ⟨1337253129588911907667537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1783004172785215876890049 1337253129588911907667537)
              ·
                refine ⟨1002939847191683930750653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1337253129588911907667537 1002939847191683930750653)
                ·
                  refine ⟨376102442696881474031495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1002939847191683930750653 376102442696881474031495)
                  ·
                    rfl

theorem cell21_1648028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 3].length) (baseStart_1648028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1648028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1648028 prefixEnd_1648028 := by exact prefixLift 1648028
  have htrace : WordTrace (prefixWord ++ tailWord_1648028) baseStart_1648028 baseEnd_1648028 := by
    simpa [prefixWord, tailWord_1648028, baseEnd_1648028] using wordTrace_append hprefix tailTrace_1648028
  have hstable : (prefixWord ++ tailWord_1648028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648028).length < 2 ^ (prefixWord ++ tailWord_1648028).sum := by decide
  have hdescent : baseEnd_1648028 < baseStart_1648028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648064 : List Nat := [2, 1, 1, 2, 3, 1, 2, 9]
def baseStart_1648064 : Nat := 118140960795 + 1648064 * 2 ^ 59
def prefixEnd_1648064 : Nat := 4983230072969 + 3 ^ 40 * 1648064 * 2
def baseEnd_1648064 : Nat := 125370219462451137143807

theorem tailTrace_1648064 : CollatzResearch.WordTrace tailWord_1648064 prefixEnd_1648064 125370219462451137143807 := by
  unfold tailWord_1648064
  simp only [CollatzResearch.WordTrace]
  refine ⟨30054916150676534883791623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40073221534235379845055497 30054916150676534883791623)
  ·
    refine ⟨45082374226014802325687435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30054916150676534883791623 45082374226014802325687435)
    ·
      refine ⟨67623561339022203488531153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45082374226014802325687435 67623561339022203488531153)
      ·
        refine ⟨50717671004266652616398365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67623561339022203488531153 50717671004266652616398365)
        ·
          refine ⟨19019126626599994731149387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50717671004266652616398365 19019126626599994731149387)
          ·
            refine ⟨28528689939899992096724081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19019126626599994731149387 28528689939899992096724081)
            ·
              refine ⟨21396517454924994072543061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28528689939899992096724081 21396517454924994072543061)
              ·
                refine ⟨125370219462451137143807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21396517454924994072543061 125370219462451137143807)
                ·
                  rfl

theorem cell21_1648064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 9].length) (baseStart_1648064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1648064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1648064 prefixEnd_1648064 := by exact prefixLift 1648064
  have htrace : WordTrace (prefixWord ++ tailWord_1648064) baseStart_1648064 baseEnd_1648064 := by
    simpa [prefixWord, tailWord_1648064, baseEnd_1648064] using wordTrace_append hprefix tailTrace_1648064
  have hstable : (prefixWord ++ tailWord_1648064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648064).length < 2 ^ (prefixWord ++ tailWord_1648064).sum := by decide
  have hdescent : baseEnd_1648064 < baseStart_1648064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648157 : List Nat := [1, 4, 2, 2, 1, 1, 4, 6]
def baseStart_1648157 : Nat := 118140960795 + 1648157 * 2 ^ 59
def prefixEnd_1648157 : Nat := 4983230072969 + 3 ^ 40 * 1648157 * 2
def baseEnd_1648157 : Nat := 125377294084801972127077

theorem tailTrace_1648157 : CollatzResearch.WordTrace tailWord_1648157 prefixEnd_1648157 125377294084801972127077 := by
  unfold tailWord_1648157
  simp only [CollatzResearch.WordTrace]
  refine ⟨60113224290016146650718725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40075482860010764433812483 60113224290016146650718725)
  ·
    refine ⟨11271229554378027497009761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60113224290016146650718725 11271229554378027497009761)
    ·
      refine ⟨8453422165783520622757321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11271229554378027497009761 8453422165783520622757321)
      ·
        refine ⟨6340066624337640467067991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8453422165783520622757321 6340066624337640467067991)
        ·
          refine ⟨9510099936506460700601987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6340066624337640467067991 9510099936506460700601987)
          ·
            refine ⟨14265149904759691050902981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9510099936506460700601987 14265149904759691050902981)
            ·
              refine ⟨2674715607142442072044309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14265149904759691050902981 2674715607142442072044309)
              ·
                refine ⟨125377294084801972127077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2674715607142442072044309 125377294084801972127077)
                ·
                  rfl

theorem cell21_1648157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 6].length) (baseStart_1648157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1648157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1648157 prefixEnd_1648157 := by exact prefixLift 1648157
  have htrace : WordTrace (prefixWord ++ tailWord_1648157) baseStart_1648157 baseEnd_1648157 := by
    simpa [prefixWord, tailWord_1648157, baseEnd_1648157] using wordTrace_append hprefix tailTrace_1648157
  have hstable : (prefixWord ++ tailWord_1648157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648157).length < 2 ^ (prefixWord ++ tailWord_1648157).sum := by decide
  have hdescent : baseEnd_1648157 < baseStart_1648157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648160 : List Nat := [2, 1, 1, 6, 1, 1, 4, 1, 4]
def baseStart_1648160 : Nat := 118140960795 + 1648160 * 2 ^ 59
def prefixEnd_1648160 : Nat := 4983230072969 + 3 ^ 40 * 1648160 * 2
def baseEnd_1648160 : Nat := 376132566895278577831225

theorem tailTrace_1648160 : CollatzResearch.WordTrace tailWord_1648160 prefixEnd_1648160 376132566895278577831225 := by
  unfold tailWord_1648160
  simp only [CollatzResearch.WordTrace]
  refine ⟨30056666854502639081538967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40075555806003518775385289 30056666854502639081538967)
  ·
    refine ⟨45085000281753958622308451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30056666854502639081538967 45085000281753958622308451)
    ·
      refine ⟨67627500422630937933462677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45085000281753958622308451 67627500422630937933462677)
      ·
        refine ⟨3170039082310825215631063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67627500422630937933462677 3170039082310825215631063)
        ·
          refine ⟨4755058623466237823446595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3170039082310825215631063 4755058623466237823446595)
          ·
            refine ⟨7132587935199356735169893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4755058623466237823446595 7132587935199356735169893)
            ·
              refine ⟨1337360237849879387844355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7132587935199356735169893 1337360237849879387844355)
              ·
                refine ⟨2006040356774819081766533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1337360237849879387844355 2006040356774819081766533)
                ·
                  refine ⟨376132566895278577831225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2006040356774819081766533 376132566895278577831225)
                  ·
                    rfl

theorem cell21_1648160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 4].length) (baseStart_1648160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1648160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1648160 prefixEnd_1648160 := by exact prefixLift 1648160
  have htrace : WordTrace (prefixWord ++ tailWord_1648160) baseStart_1648160 baseEnd_1648160 := by
    simpa [prefixWord, tailWord_1648160, baseEnd_1648160] using wordTrace_append hprefix tailTrace_1648160
  have hstable : (prefixWord ++ tailWord_1648160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648160).length < 2 ^ (prefixWord ++ tailWord_1648160).sum := by decide
  have hdescent : baseEnd_1648160 < baseStart_1648160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648374 : List Nat := [5, 1, 1, 1, 1, 3, 4, 2, 3]
def baseStart_1648374 : Nat := 118140960795 + 1648374 * 2 ^ 59
def prefixEnd_1648374 : Nat := 4983230072969 + 3 ^ 40 * 1648374 * 2
def baseEnd_1648374 : Nat := 376181404610861761264121

theorem tailTrace_1648374 : CollatzResearch.WordTrace tailWord_1648374 prefixEnd_1648374 376181404610861761264121 := by
  unfold tailWord_1648374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3757571183139374544460511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40080759286819995140912117 3757571183139374544460511)
  ·
    refine ⟨5636356774709061816690767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3757571183139374544460511 5636356774709061816690767)
    ·
      refine ⟨8454535162063592725036151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5636356774709061816690767 8454535162063592725036151)
      ·
        refine ⟨12681802743095389087554227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8454535162063592725036151 12681802743095389087554227)
        ·
          refine ⟨19022704114643083631331341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12681802743095389087554227 19022704114643083631331341)
          ·
            refine ⟨7133514042991156361749253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19022704114643083631331341 7133514042991156361749253)
            ·
              refine ⟨1337533883060841817827985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7133514042991156361749253 1337533883060841817827985)
              ·
                refine ⟨1003150412295631363370989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1337533883060841817827985 1003150412295631363370989)
                ·
                  refine ⟨376181404610861761264121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1003150412295631363370989 376181404610861761264121)
                  ·
                    rfl

theorem cell21_1648374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_1648374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1648374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1648374 prefixEnd_1648374 := by exact prefixLift 1648374
  have htrace : WordTrace (prefixWord ++ tailWord_1648374) baseStart_1648374 baseEnd_1648374 := by
    simpa [prefixWord, tailWord_1648374, baseEnd_1648374] using wordTrace_append hprefix tailTrace_1648374
  have hstable : (prefixWord ++ tailWord_1648374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648374).length < 2 ^ (prefixWord ++ tailWord_1648374).sum := by decide
  have hdescent : baseEnd_1648374 < baseStart_1648374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648492 : List Nat := [2, 2, 1, 1, 4, 4, 1, 1, 5]
def baseStart_1648492 : Nat := 118140960795 + 1648492 * 2 ^ 59
def prefixEnd_1648492 : Nat := 4983230072969 + 3 ^ 40 * 1648492 * 2
def baseEnd_1648492 : Nat := 376208333818519778297213

theorem tailTrace_1648492 : CollatzResearch.WordTrace tailWord_1648492 prefixEnd_1648492 376208333818519778297213 := by
  unfold tailWord_1648492
  simp only [CollatzResearch.WordTrace]
  refine ⟨30062721371901249432081865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40083628495868332576109153 30062721371901249432081865)
  ·
    refine ⟨22547041028925937074061399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30062721371901249432081865 22547041028925937074061399)
    ·
      refine ⟨33820561543388905611092099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22547041028925937074061399 33820561543388905611092099)
      ·
        refine ⟨50730842315083358416638149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33820561543388905611092099 50730842315083358416638149)
        ·
          refine ⟨9512032934078129703119653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50730842315083358416638149 9512032934078129703119653)
          ·
            refine ⟨1783506175139649319334935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9512032934078129703119653 1783506175139649319334935)
            ·
              refine ⟨2675259262709473979002403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1783506175139649319334935 2675259262709473979002403)
              ·
                refine ⟨4012888894064210968503605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2675259262709473979002403 4012888894064210968503605)
                ·
                  refine ⟨376208333818519778297213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4012888894064210968503605 376208333818519778297213)
                  ·
                    rfl

theorem cell21_1648492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_1648492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1648492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1648492 prefixEnd_1648492 := by exact prefixLift 1648492
  have htrace : WordTrace (prefixWord ++ tailWord_1648492) baseStart_1648492 baseEnd_1648492 := by
    simpa [prefixWord, tailWord_1648492, baseEnd_1648492] using wordTrace_append hprefix tailTrace_1648492
  have hstable : (prefixWord ++ tailWord_1648492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648492).length < 2 ^ (prefixWord ++ tailWord_1648492).sum := by decide
  have hdescent : baseEnd_1648492 < baseStart_1648492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648543 : List Nat := [1, 1, 2, 5, 4, 1, 2, 2, 3]
def baseStart_1648543 : Nat := 118140960795 + 1648543 * 2 ^ 59
def prefixEnd_1648543 : Nat := 4983230072969 + 3 ^ 40 * 1648543 * 2
def baseEnd_1648543 : Nat := 376219972713355022947109

theorem tailTrace_1648543 : CollatzResearch.WordTrace tailWord_1648543 prefixEnd_1648543 376219972713355022947109 := by
  unfold tailWord_1648543
  simp only [CollatzResearch.WordTrace]
  refine ⟨60127302866617734574270283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40084868577745156382846855 60127302866617734574270283)
  ·
    refine ⟨90190954299926601861405425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60127302866617734574270283 90190954299926601861405425)
    ·
      refine ⟨67643215724944951396054069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90190954299926601861405425 67643215724944951396054069)
      ·
        refine ⟨6341551474213589193380069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67643215724944951396054069 6341551474213589193380069)
        ·
          refine ⟨1189040901415047973758763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6341551474213589193380069 1189040901415047973758763)
          ·
            refine ⟨1783561352122571960638145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1189040901415047973758763 1783561352122571960638145)
            ·
              refine ⟨1337671014091928970478609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1783561352122571960638145 1337671014091928970478609)
              ·
                refine ⟨1003253260568946727858957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1337671014091928970478609 1003253260568946727858957)
                ·
                  refine ⟨376219972713355022947109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1003253260568946727858957 376219972713355022947109)
                  ·
                    rfl

theorem cell21_1648543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2, 3].length) (baseStart_1648543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1648543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1648543 prefixEnd_1648543 := by exact prefixLift 1648543
  have htrace : WordTrace (prefixWord ++ tailWord_1648543) baseStart_1648543 baseEnd_1648543 := by
    simpa [prefixWord, tailWord_1648543, baseEnd_1648543] using wordTrace_append hprefix tailTrace_1648543
  have hstable : (prefixWord ++ tailWord_1648543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648543).length < 2 ^ (prefixWord ++ tailWord_1648543).sum := by decide
  have hdescent : baseEnd_1648543 < baseStart_1648543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648596 : List Nat := [2, 4, 1, 2, 1, 1, 10]
def baseStart_1648596 : Nat := 118140960795 + 1648596 * 2 ^ 59
def prefixEnd_1648596 : Nat := 4983230072969 + 3 ^ 40 * 1648596 * 2
def baseEnd_1648596 : Nat := 41803563115048745395963

theorem tailTrace_1648596 : CollatzResearch.WordTrace tailWord_1648596 prefixEnd_1648596 41803563115048745395963 := by
  unfold tailWord_1648596
  simp only [CollatzResearch.WordTrace]
  refine ⟨30064617967712862312974821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40086157290283816417299761 30064617967712862312974821)
  ·
    refine ⟨5637115868946161683682779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30064617967712862312974821 5637115868946161683682779)
    ·
      refine ⟨8455673803419242525524169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5637115868946161683682779 8455673803419242525524169)
      ·
        refine ⟨6341755352564431894143127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8455673803419242525524169 6341755352564431894143127)
        ·
          refine ⟨9512633028846647841214691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6341755352564431894143127 9512633028846647841214691)
          ·
            refine ⟨14268949543269971761822037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9512633028846647841214691 14268949543269971761822037)
            ·
              refine ⟨41803563115048745395963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14268949543269971761822037 41803563115048745395963)
              ·
                rfl

theorem cell21_1648596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 10].length) (baseStart_1648596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1648596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1648596 prefixEnd_1648596 := by exact prefixLift 1648596
  have htrace : WordTrace (prefixWord ++ tailWord_1648596) baseStart_1648596 baseEnd_1648596 := by
    simpa [prefixWord, tailWord_1648596, baseEnd_1648596] using wordTrace_append hprefix tailTrace_1648596
  have hstable : (prefixWord ++ tailWord_1648596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648596).length < 2 ^ (prefixWord ++ tailWord_1648596).sum := by decide
  have hdescent : baseEnd_1648596 < baseStart_1648596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648641 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 8]
def baseStart_1648641 : Nat := 118140960795 + 1648641 * 2 ^ 59
def prefixEnd_1648641 : Nat := 4983230072969 + 3 ^ 40 * 1648641 * 2
def baseEnd_1648641 : Nat := 376242337648528630313575

theorem tailTrace_1648641 : CollatzResearch.WordTrace tailWord_1648641 prefixEnd_1648641 376242337648528630313575 := by
  unfold tailWord_1648641
  simp only [CollatzResearch.WordTrace]
  refine ⟨60130877220262697311337777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40087251480175131540891851 60130877220262697311337777)
  ·
    refine ⟨45098157915197022983503333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60130877220262697311337777 45098157915197022983503333)
    ·
      refine ⟨8455904609099441809406875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45098157915197022983503333 8455904609099441809406875)
      ·
        refine ⟨12683856913649162714110313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8455904609099441809406875 12683856913649162714110313)
        ·
          refine ⟨9512892685236872035582735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12683856913649162714110313 9512892685236872035582735)
          ·
            refine ⟨14269339027855308053374103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9512892685236872035582735 14269339027855308053374103)
            ·
              refine ⟨21404008541782962080061155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14269339027855308053374103 21404008541782962080061155)
              ·
                refine ⟨32106012812674443120091733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21404008541782962080061155 32106012812674443120091733)
                ·
                  refine ⟨376242337648528630313575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32106012812674443120091733 376242337648528630313575)
                  ·
                    rfl

theorem cell21_1648641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 8].length) (baseStart_1648641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1648641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1648641 prefixEnd_1648641 := by exact prefixLift 1648641
  have htrace : WordTrace (prefixWord ++ tailWord_1648641) baseStart_1648641 baseEnd_1648641 := by
    simpa [prefixWord, tailWord_1648641, baseEnd_1648641] using wordTrace_append hprefix tailTrace_1648641
  have hstable : (prefixWord ++ tailWord_1648641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648641).length < 2 ^ (prefixWord ++ tailWord_1648641).sum := by decide
  have hdescent : baseEnd_1648641 < baseStart_1648641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648661 : List Nat := [1, 3, 2, 1, 6, 1, 1, 1, 5]
def baseStart_1648661 : Nat := 118140960795 + 1648661 * 2 ^ 59
def prefixEnd_1648661 : Nat := 4983230072969 + 3 ^ 40 * 1648661 * 2
def baseEnd_1648661 : Nat := 376246901921013039980201

theorem tailTrace_1648661 : CollatzResearch.WordTrace tailWord_1648661 prefixEnd_1648661 376246901921013039980201 := by
  unfold tailWord_1648661
  simp only [CollatzResearch.WordTrace]
  refine ⟨60131606680190240727065837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40087737786793493818043891 60131606680190240727065837)
  ·
    refine ⟨22549352505071340272649689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60131606680190240727065837 22549352505071340272649689)
    ·
      refine ⟨16912014378803505204487267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22549352505071340272649689 16912014378803505204487267)
      ·
        refine ⟨25368021568205257806730901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16912014378803505204487267 25368021568205257806730901)
        ·
          refine ⟨1189126011009621459690511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25368021568205257806730901 1189126011009621459690511)
          ·
            refine ⟨1783689016514432189535767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1189126011009621459690511 1783689016514432189535767)
            ·
              refine ⟨2675533524771648284303651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1783689016514432189535767 2675533524771648284303651)
              ·
                refine ⟨4013300287157472426455477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2675533524771648284303651 4013300287157472426455477)
                ·
                  refine ⟨376246901921013039980201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4013300287157472426455477 376246901921013039980201)
                  ·
                    rfl

theorem cell21_1648661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 5].length) (baseStart_1648661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1648661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1648661 prefixEnd_1648661 := by exact prefixLift 1648661
  have htrace : WordTrace (prefixWord ++ tailWord_1648661) baseStart_1648661 baseEnd_1648661 := by
    simpa [prefixWord, tailWord_1648661, baseEnd_1648661] using wordTrace_append hprefix tailTrace_1648661
  have hstable : (prefixWord ++ tailWord_1648661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648661).length < 2 ^ (prefixWord ++ tailWord_1648661).sum := by decide
  have hdescent : baseEnd_1648661 < baseStart_1648661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648793 : List Nat := [1, 2, 1, 2, 1, 2, 1, 7, 4]
def baseStart_1648793 : Nat := 118140960795 + 1648793 * 2 ^ 59
def prefixEnd_1648793 : Nat := 4983230072969 + 3 ^ 40 * 1648793 * 2
def baseEnd_1648793 : Nat := 376277026119410143779931

theorem tailTrace_1648793 : CollatzResearch.WordTrace tailWord_1648793 prefixEnd_1648793 376277026119410143779931 := by
  unfold tailWord_1648793
  simp only [CollatzResearch.WordTrace]
  refine ⟨60136421115712027270871033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40090947410474684847247355 60136421115712027270871033)
  ·
    refine ⟨45102315836784020453153275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60136421115712027270871033 45102315836784020453153275)
    ·
      refine ⟨67653473755176030679729913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45102315836784020453153275 67653473755176030679729913)
      ·
        refine ⟨50740105316382023009797435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67653473755176030679729913 50740105316382023009797435)
        ·
          refine ⟨76110157974573034514696153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50740105316382023009797435 76110157974573034514696153)
          ·
            refine ⟨57082618480929775886022115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76110157974573034514696153 57082618480929775886022115)
            ·
              refine ⟨85623927721394663829033173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57082618480929775886022115 85623927721394663829033173)
              ·
                refine ⟨2006810805970187433492965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 85623927721394663829033173 2006810805970187433492965)
                ·
                  refine ⟨376277026119410143779931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2006810805970187433492965 376277026119410143779931)
                  ·
                    rfl

theorem cell21_1648793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 4].length) (baseStart_1648793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1648793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1648793 prefixEnd_1648793 := by exact prefixLift 1648793
  have htrace : WordTrace (prefixWord ++ tailWord_1648793) baseStart_1648793 baseEnd_1648793 := by
    simpa [prefixWord, tailWord_1648793, baseEnd_1648793] using wordTrace_append hprefix tailTrace_1648793
  have hstable : (prefixWord ++ tailWord_1648793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648793).length < 2 ^ (prefixWord ++ tailWord_1648793).sum := by decide
  have hdescent : baseEnd_1648793 < baseStart_1648793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648813 : List Nat := [1, 5, 2, 1, 2, 1, 3, 3, 3]
def baseStart_1648813 : Nat := 118140960795 + 1648813 * 2 ^ 59
def prefixEnd_1648813 : Nat := 4983230072969 + 3 ^ 40 * 1648813 * 2
def baseEnd_1648813 : Nat := 376281590391894553446557

theorem tailTrace_1648813 : CollatzResearch.WordTrace tailWord_1648813 prefixEnd_1648813 376281590391894553446557 := by
  unfold tailWord_1648813
  simp only [CollatzResearch.WordTrace]
  refine ⟨60137150575639570686599093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40091433717093047124399395 60137150575639570686599093)
  ·
    refine ⟨5637857866466209751868665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60137150575639570686599093 5637857866466209751868665)
    ·
      refine ⟨4228393399849657313901499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5637857866466209751868665 4228393399849657313901499)
      ·
        refine ⟨6342590099774485970852249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4228393399849657313901499 6342590099774485970852249)
        ·
          refine ⟨4756942574830864478139187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6342590099774485970852249 4756942574830864478139187)
          ·
            refine ⟨7135413862246296717208781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4756942574830864478139187 7135413862246296717208781)
            ·
              refine ⟨2675780198342361268953293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7135413862246296717208781 2675780198342361268953293)
              ·
                refine ⟨1003417574378385475857485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2675780198342361268953293 1003417574378385475857485)
                ·
                  refine ⟨376281590391894553446557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1003417574378385475857485 376281590391894553446557)
                  ·
                    rfl

theorem cell21_1648813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_1648813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1648813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1648813 prefixEnd_1648813 := by exact prefixLift 1648813
  have htrace : WordTrace (prefixWord ++ tailWord_1648813) baseStart_1648813 baseEnd_1648813 := by
    simpa [prefixWord, tailWord_1648813, baseEnd_1648813] using wordTrace_append hprefix tailTrace_1648813
  have hstable : (prefixWord ++ tailWord_1648813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648813).length < 2 ^ (prefixWord ++ tailWord_1648813).sum := by decide
  have hdescent : baseEnd_1648813 < baseStart_1648813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648830 : List Nat := [4, 2, 1, 1, 4, 1, 3, 2, 3]
def baseStart_1648830 : Nat := 118140960795 + 1648830 * 2 ^ 59
def prefixEnd_1648830 : Nat := 4983230072969 + 3 ^ 40 * 1648830 * 2
def baseEnd_1648830 : Nat := 376285470023506301663189

theorem tailTrace_1648830 : CollatzResearch.WordTrace tailWord_1648830 prefixEnd_1648830 376285470023506301663189 := by
  unfold tailWord_1648830
  simp only [CollatzResearch.WordTrace]
  refine ⟨7517221327072247823745993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40091847077718655059978629 7517221327072247823745993)
  ·
    refine ⟨5637915995304185867809495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7517221327072247823745993 5637915995304185867809495)
    ·
      refine ⟨8456873992956278801714243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5637915995304185867809495 8456873992956278801714243)
      ·
        refine ⟨12685310989434418202571365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8456873992956278801714243 12685310989434418202571365)
        ·
          refine ⟨2378495810518953412982131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12685310989434418202571365 2378495810518953412982131)
          ·
            refine ⟨3567743715778430119473197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2378495810518953412982131 3567743715778430119473197)
            ·
              refine ⟨1337903893416911294802449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3567743715778430119473197 1337903893416911294802449)
              ·
                refine ⟨1003427920062683471101837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1337903893416911294802449 1003427920062683471101837)
                ·
                  refine ⟨376285470023506301663189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1003427920062683471101837 376285470023506301663189)
                  ·
                    rfl

theorem cell21_1648830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_1648830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1648830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1648830 prefixEnd_1648830 := by exact prefixLift 1648830
  have htrace : WordTrace (prefixWord ++ tailWord_1648830) baseStart_1648830 baseEnd_1648830 := by
    simpa [prefixWord, tailWord_1648830, baseEnd_1648830] using wordTrace_append hprefix tailTrace_1648830
  have hstable : (prefixWord ++ tailWord_1648830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648830).length < 2 ^ (prefixWord ++ tailWord_1648830).sum := by decide
  have hdescent : baseEnd_1648830 < baseStart_1648830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648886 : List Nat := [5, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_1648886 : Nat := 118140960795 + 1648886 * 2 ^ 59
def prefixEnd_1648886 : Nat := 4983230072969 + 3 ^ 40 * 1648886 * 2
def baseEnd_1648886 : Nat := 376298249986462648729741

theorem tailTrace_1648886 : CollatzResearch.WordTrace tailWord_1648886 prefixEnd_1648886 376298249986462648729741 := by
  unfold tailWord_1648886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3758738319023444009625407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40093208736250069436004341 3758738319023444009625407)
  ·
    refine ⟨5638107478535166014438111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3758738319023444009625407 5638107478535166014438111)
    ·
      refine ⟨8457161217802749021657167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5638107478535166014438111 8457161217802749021657167)
      ·
        refine ⟨12685741826704123532485751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8457161217802749021657167 12685741826704123532485751)
        ·
          refine ⟨19028612740056185298728627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12685741826704123532485751 19028612740056185298728627)
          ·
            refine ⟨28542919110084277948092941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19028612740056185298728627 28542919110084277948092941)
            ·
              refine ⟨10703594666281604230534853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28542919110084277948092941 10703594666281604230534853)
              ·
                refine ⟨2006923999927800793225285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10703594666281604230534853 2006923999927800793225285)
                ·
                  refine ⟨376298249986462648729741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2006923999927800793225285 376298249986462648729741)
                  ·
                    rfl

theorem cell21_1648886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_1648886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1648886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1648886 prefixEnd_1648886 := by exact prefixLift 1648886
  have htrace : WordTrace (prefixWord ++ tailWord_1648886) baseStart_1648886 baseEnd_1648886 := by
    simpa [prefixWord, tailWord_1648886, baseEnd_1648886] using wordTrace_append hprefix tailTrace_1648886
  have hstable : (prefixWord ++ tailWord_1648886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648886).length < 2 ^ (prefixWord ++ tailWord_1648886).sum := by decide
  have hdescent : baseEnd_1648886 < baseStart_1648886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648948 : List Nat := [2, 5, 1, 1, 1, 3, 2, 1, 5]
def baseStart_1648948 : Nat := 118140960795 + 1648948 * 2 ^ 59
def prefixEnd_1648948 : Nat := 4983230072969 + 3 ^ 40 * 1648948 * 2
def baseEnd_1648948 : Nat := 376312399231164318696281

theorem tailTrace_1648948 : CollatzResearch.WordTrace tailWord_1648948 prefixEnd_1648948 376312399231164318696281 := by
  unfold tailWord_1648948
  simp only [CollatzResearch.WordTrace]
  refine ⟨30071037215075244371381749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40094716286766992495175665 30071037215075244371381749)
  ·
    refine ⟨2819159738913304159817039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30071037215075244371381749 2819159738913304159817039)
    ·
      refine ⟨4228739608369956239725559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2819159738913304159817039 4228739608369956239725559)
      ·
        refine ⟨6343109412554934359588339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4228739608369956239725559 6343109412554934359588339)
        ·
          refine ⟨9514664118832401539382509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6343109412554934359588339 9514664118832401539382509)
          ·
            refine ⟨3567999044562150577268441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9514664118832401539382509 3567999044562150577268441)
            ·
              refine ⟨2675999283421612932951331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3567999044562150577268441 2675999283421612932951331)
              ·
                refine ⟨4013998925132419399426997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2675999283421612932951331 4013998925132419399426997)
                ·
                  refine ⟨376312399231164318696281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4013998925132419399426997 376312399231164318696281)
                  ·
                    rfl

theorem cell21_1648948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_1648948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1648948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1648948 prefixEnd_1648948 := by exact prefixLift 1648948
  have htrace : WordTrace (prefixWord ++ tailWord_1648948) baseStart_1648948 baseEnd_1648948 := by
    simpa [prefixWord, tailWord_1648948, baseEnd_1648948] using wordTrace_append hprefix tailTrace_1648948
  have hstable : (prefixWord ++ tailWord_1648948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648948).length < 2 ^ (prefixWord ++ tailWord_1648948).sum := by decide
  have hdescent : baseEnd_1648948 < baseStart_1648948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648959 : List Nat := [1, 1, 2, 2, 4, 1, 2, 8]
def baseStart_1648959 : Nat := 118140960795 + 1648959 * 2 ^ 59
def prefixEnd_1648959 : Nat := 4983230072969 + 3 ^ 40 * 1648959 * 2
def baseEnd_1648959 : Nat := 125438303193676914670975

theorem tailTrace_1648959 : CollatzResearch.WordTrace tailWord_1648959 prefixEnd_1648959 125438303193676914670975 := by
  unfold tailWord_1648959
  simp only [CollatzResearch.WordTrace]
  refine ⟨60142475633110637621413931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40094983755407091747609287 60142475633110637621413931)
  ·
    refine ⟨90213713449665956432120897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60142475633110637621413931 90213713449665956432120897)
    ·
      refine ⟨67660285087249467324090673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90213713449665956432120897 67660285087249467324090673)
      ·
        refine ⟨50745213815437100493068005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67660285087249467324090673 50745213815437100493068005)
        ·
          refine ⟨9514727590394456342450251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50745213815437100493068005 9514727590394456342450251)
          ·
            refine ⟨14272091385591684513675377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9514727590394456342450251 14272091385591684513675377)
            ·
              refine ⟨10704068539193763385256533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14272091385591684513675377 10704068539193763385256533)
              ·
                refine ⟨125438303193676914670975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10704068539193763385256533 125438303193676914670975)
                ·
                  rfl

theorem cell21_1648959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 8].length) (baseStart_1648959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1648959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1648959 prefixEnd_1648959 := by exact prefixLift 1648959
  have htrace : WordTrace (prefixWord ++ tailWord_1648959) baseStart_1648959 baseEnd_1648959 := by
    simpa [prefixWord, tailWord_1648959, baseEnd_1648959] using wordTrace_append hprefix tailTrace_1648959
  have hstable : (prefixWord ++ tailWord_1648959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648959).length < 2 ^ (prefixWord ++ tailWord_1648959).sum := by decide
  have hdescent : baseEnd_1648959 < baseStart_1648959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648976 : List Nat := [2, 1, 1, 1, 1, 6, 4, 5]
def baseStart_1648976 : Nat := 118140960795 + 1648976 * 2 ^ 59
def prefixEnd_1648976 : Nat := 4983230072969 + 3 ^ 40 * 1648976 * 2
def baseEnd_1648976 : Nat := 125439596404214164076519

theorem tailTrace_1648976 : CollatzResearch.WordTrace tailWord_1648976 prefixEnd_1648976 125439596404214164076519 := by
  unfold tailWord_1648976
  simp only [CollatzResearch.WordTrace]
  refine ⟨30071547837024524762391391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40095397116032699683188521 30071547837024524762391391)
  ·
    refine ⟨45107321755536787143587087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30071547837024524762391391 45107321755536787143587087)
    ·
      refine ⟨67660982633305180715380631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45107321755536787143587087 67660982633305180715380631)
      ·
        refine ⟨101491473949957771073070947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67660982633305180715380631 101491473949957771073070947)
        ·
          refine ⟨152237210924936656609606421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101491473949957771073070947 152237210924936656609606421)
          ·
            refine ⟨7136119262106405778575301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 152237210924936656609606421 7136119262106405778575301)
            ·
              refine ⟨1338022361644951083482869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7136119262106405778575301 1338022361644951083482869)
              ·
                refine ⟨125439596404214164076519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1338022361644951083482869 125439596404214164076519)
                ·
                  rfl

theorem cell21_1648976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 5].length) (baseStart_1648976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1648976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1648976 prefixEnd_1648976 := by exact prefixLift 1648976
  have htrace : WordTrace (prefixWord ++ tailWord_1648976) baseStart_1648976 baseEnd_1648976 := by
    simpa [prefixWord, tailWord_1648976, baseEnd_1648976] using wordTrace_append hprefix tailTrace_1648976
  have hstable : (prefixWord ++ tailWord_1648976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648976).length < 2 ^ (prefixWord ++ tailWord_1648976).sum := by decide
  have hdescent : baseEnd_1648976 < baseStart_1648976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649035 : List Nat := [1, 1, 1, 1, 4, 4, 2, 7]
def baseStart_1649035 : Nat := 118140960795 + 1649035 * 2 ^ 59
def prefixEnd_1649035 : Nat := 4983230072969 + 3 ^ 40 * 1649035 * 2
def baseEnd_1649035 : Nat := 125444084605490500248701

theorem tailTrace_1649035 : CollatzResearch.WordTrace tailWord_1649035 prefixEnd_1649035 125444084605490500248701 := by
  unfold tailWord_1649035
  simp only [CollatzResearch.WordTrace]
  refine ⟨60145247580835302601180559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40096831720556868400787039 60145247580835302601180559)
  ·
    refine ⟨90217871371252953901770839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60145247580835302601180559 90217871371252953901770839)
    ·
      refine ⟨135326807056879430852656259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90217871371252953901770839 135326807056879430852656259)
      ·
        refine ⟨202990210585319146278984389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135326807056879430852656259 202990210585319146278984389)
        ·
          refine ⟨38060664484747339927309573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202990210585319146278984389 38060664484747339927309573)
          ·
            refine ⟨7136374590890126236370545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38060664484747339927309573 7136374590890126236370545)
            ·
              refine ⟨5352280943167594677277909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7136374590890126236370545 5352280943167594677277909)
              ·
                refine ⟨125444084605490500248701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5352280943167594677277909 125444084605490500248701)
                ·
                  rfl

theorem cell21_1649035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 7].length) (baseStart_1649035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649035 prefixEnd_1649035 := by exact prefixLift 1649035
  have htrace : WordTrace (prefixWord ++ tailWord_1649035) baseStart_1649035 baseEnd_1649035 := by
    simpa [prefixWord, tailWord_1649035, baseEnd_1649035] using wordTrace_append hprefix tailTrace_1649035
  have hstable : (prefixWord ++ tailWord_1649035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649035).length < 2 ^ (prefixWord ++ tailWord_1649035).sum := by decide
  have hdescent : baseEnd_1649035 < baseStart_1649035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649080 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 8]
def baseStart_1649080 : Nat := 118140960795 + 1649080 * 2 ^ 59
def prefixEnd_1649080 : Nat := 4983230072969 + 3 ^ 40 * 1649080 * 2
def baseEnd_1649080 : Nat := 376342523429561422496011

theorem tailTrace_1649080 : CollatzResearch.WordTrace tailWord_1649080 prefixEnd_1649080 376342523429561422496011 := by
  unfold tailWord_1649080
  simp only [CollatzResearch.WordTrace]
  refine ⟨30073444432836137643284347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40097925910448183524379129 30073444432836137643284347)
  ·
    refine ⟨45110166649254206464926521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30073444432836137643284347 45110166649254206464926521)
    ·
      refine ⟨33832624986940654848694891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45110166649254206464926521 33832624986940654848694891)
      ·
        refine ⟨50748937480410982273042337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33832624986940654848694891 50748937480410982273042337)
        ·
          refine ⟨38061703110308236704781753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50748937480410982273042337 38061703110308236704781753)
          ·
            refine ⟨28546277332731177528586315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38061703110308236704781753 28546277332731177528586315)
            ·
              refine ⟨42819415999096766292879473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28546277332731177528586315 42819415999096766292879473)
              ·
                refine ⟨32114561999322574719659605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42819415999096766292879473 32114561999322574719659605)
                ·
                  refine ⟨376342523429561422496011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32114561999322574719659605 376342523429561422496011)
                  ·
                    rfl

theorem cell21_1649080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_1649080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649080 prefixEnd_1649080 := by exact prefixLift 1649080
  have htrace : WordTrace (prefixWord ++ tailWord_1649080) baseStart_1649080 baseEnd_1649080 := by
    simpa [prefixWord, tailWord_1649080, baseEnd_1649080] using wordTrace_append hprefix tailTrace_1649080
  have hstable : (prefixWord ++ tailWord_1649080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649080).length < 2 ^ (prefixWord ++ tailWord_1649080).sum := by decide
  have hdescent : baseEnd_1649080 < baseStart_1649080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649173 : List Nat := [1, 3, 2, 1, 3, 1, 2, 4, 4]
def baseStart_1649173 : Nat := 118140960795 + 1649173 * 2 ^ 59
def prefixEnd_1649173 : Nat := 4983230072969 + 3 ^ 40 * 1649173 * 2
def baseEnd_1649173 : Nat := 376363747296613927445821

theorem tailTrace_1649173 : CollatzResearch.WordTrace tailWord_1649173 prefixEnd_1649173 376363747296613927445821 := by
  unfold tailWord_1649173
  simp only [CollatzResearch.WordTrace]
  refine ⟨60150280854335352169704173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40100187236223568113136115 60150280854335352169704173)
  ·
    refine ⟨22556355320375757063639065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60150280854335352169704173 22556355320375757063639065)
    ·
      refine ⟨16917266490281817797729299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22556355320375757063639065 16917266490281817797729299)
      ·
        refine ⟨25375899735422726696593949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16917266490281817797729299 25375899735422726696593949)
        ·
          refine ⟨9515962400783522511222731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25375899735422726696593949 9515962400783522511222731)
          ·
            refine ⟨14273943601175283766834097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9515962400783522511222731 14273943601175283766834097)
            ·
              refine ⟨10705457700881462825125573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14273943601175283766834097 10705457700881462825125573)
              ·
                refine ⟨2007273318915274279711045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10705457700881462825125573 2007273318915274279711045)
                ·
                  refine ⟨376363747296613927445821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2007273318915274279711045 376363747296613927445821)
                  ·
                    rfl

theorem cell21_1649173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_1649173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649173 prefixEnd_1649173 := by exact prefixLift 1649173
  have htrace : WordTrace (prefixWord ++ tailWord_1649173) baseStart_1649173 baseEnd_1649173 := by
    simpa [prefixWord, tailWord_1649173, baseEnd_1649173] using wordTrace_append hprefix tailTrace_1649173
  have hstable : (prefixWord ++ tailWord_1649173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649173).length < 2 ^ (prefixWord ++ tailWord_1649173).sum := by decide
  have hdescent : baseEnd_1649173 < baseStart_1649173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649187 : List Nat := [1, 1, 1, 4, 4, 1, 1, 8]
def baseStart_1649187 : Nat := 118140960795 + 1649187 * 2 ^ 59
def prefixEnd_1649187 : Nat := 4983230072969 + 3 ^ 40 * 1649187 * 2
def baseEnd_1649187 : Nat := 125455647429117671404153

theorem tailTrace_1649187 : CollatzResearch.WordTrace tailWord_1649187 prefixEnd_1649187 125455647429117671404153 := by
  unfold tailWord_1649187
  simp only [CollatzResearch.WordTrace]
  refine ⟨60150791476284632560713815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40100527650856421707142543 60150791476284632560713815)
  ·
    refine ⟨90226187214426948841070723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60150791476284632560713815 90226187214426948841070723)
    ·
      refine ⟨135339280821640423261606085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90226187214426948841070723 135339280821640423261606085)
      ·
        refine ⟨25376115154057579361551141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135339280821640423261606085 25376115154057579361551141)
        ·
          refine ⟨4758021591385796130290839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25376115154057579361551141 4758021591385796130290839)
          ·
            refine ⟨7137032387078694195436259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4758021591385796130290839 7137032387078694195436259)
            ·
              refine ⟨10705548580618041293154389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7137032387078694195436259 10705548580618041293154389)
              ·
                refine ⟨125455647429117671404153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10705548580618041293154389 125455647429117671404153)
                ·
                  rfl

theorem cell21_1649187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 8].length) (baseStart_1649187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649187 prefixEnd_1649187 := by exact prefixLift 1649187
  have htrace : WordTrace (prefixWord ++ tailWord_1649187) baseStart_1649187 baseEnd_1649187 := by
    simpa [prefixWord, tailWord_1649187, baseEnd_1649187] using wordTrace_append hprefix tailTrace_1649187
  have hstable : (prefixWord ++ tailWord_1649187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649187).length < 2 ^ (prefixWord ++ tailWord_1649187).sum := by decide
  have hdescent : baseEnd_1649187 < baseStart_1649187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649249 : List Nat := [1, 2, 3, 1, 1, 4, 2, 3, 4]
def baseStart_1649249 : Nat := 118140960795 + 1649249 * 2 ^ 59
def prefixEnd_1649249 : Nat := 4983230072969 + 3 ^ 40 * 1649249 * 2
def baseEnd_1649249 : Nat := 376381091532054684178999

theorem tailTrace_1649249 : CollatzResearch.WordTrace tailWord_1649249 prefixEnd_1649249 376381091532054684178999 := by
  unfold tailWord_1649249
  simp only [CollatzResearch.WordTrace]
  refine ⟨60153052802060017149470801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40102035201373344766313867 60153052802060017149470801)
  ·
    refine ⟨45114789601545012862103101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60153052802060017149470801 45114789601545012862103101)
    ·
      refine ⟨16918046100579379823288663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45114789601545012862103101 16918046100579379823288663)
      ·
        refine ⟨25377069150869069734932995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16918046100579379823288663 25377069150869069734932995)
        ·
          refine ⟨38065603726303604602399493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25377069150869069734932995 38065603726303604602399493)
          ·
            refine ⟨7137300698681925862949905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38065603726303604602399493 7137300698681925862949905)
            ·
              refine ⟨5352975524011444397212429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7137300698681925862949905 5352975524011444397212429)
              ·
                refine ⟨2007365821504291648954661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5352975524011444397212429 2007365821504291648954661)
                ·
                  refine ⟨376381091532054684178999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2007365821504291648954661 376381091532054684178999)
                  ·
                    rfl

theorem cell21_1649249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 4].length) (baseStart_1649249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649249 prefixEnd_1649249 := by exact prefixLift 1649249
  have htrace : WordTrace (prefixWord ++ tailWord_1649249) baseStart_1649249 baseEnd_1649249 := by
    simpa [prefixWord, tailWord_1649249, baseEnd_1649249] using wordTrace_append hprefix tailTrace_1649249
  have hstable : (prefixWord ++ tailWord_1649249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649249).length < 2 ^ (prefixWord ++ tailWord_1649249).sum := by decide
  have hdescent : baseEnd_1649249 < baseStart_1649249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649269 : List Nat := [1, 3, 4, 2, 2, 1, 2, 3, 3]
def baseStart_1649269 : Nat := 118140960795 + 1649269 * 2 ^ 59
def prefixEnd_1649269 : Nat := 4983230072969 + 3 ^ 40 * 1649269 * 2
def baseEnd_1649269 : Nat := 376385655804539093845625

theorem tailTrace_1649269 : CollatzResearch.WordTrace tailWord_1649269 prefixEnd_1649269 376385655804539093845625 := by
  unfold tailWord_1649269
  simp only [CollatzResearch.WordTrace]
  refine ⟨60153782261987560565198861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40102521507991707043465907 60153782261987560565198861)
  ·
    refine ⟨22557668348245335211949573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60153782261987560565198861 22557668348245335211949573)
    ·
      refine ⟨4229562815296000352240545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22557668348245335211949573 4229562815296000352240545)
      ·
        refine ⟨3172172111472000264180409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4229562815296000352240545 3172172111472000264180409)
        ·
          refine ⟨2379129083604000198135307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3172172111472000264180409 2379129083604000198135307)
          ·
            refine ⟨3568693625406000297202961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2379129083604000198135307 3568693625406000297202961)
            ·
              refine ⟨2676520219054500222902221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3568693625406000297202961 2676520219054500222902221)
              ·
                refine ⟨1003695082145437583588333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2676520219054500222902221 1003695082145437583588333)
                ·
                  refine ⟨376385655804539093845625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1003695082145437583588333 376385655804539093845625)
                  ·
                    rfl

theorem cell21_1649269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3, 3].length) (baseStart_1649269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649269 prefixEnd_1649269 := by exact prefixLift 1649269
  have htrace : WordTrace (prefixWord ++ tailWord_1649269) baseStart_1649269 baseEnd_1649269 := by
    simpa [prefixWord, tailWord_1649269, baseEnd_1649269] using wordTrace_append hprefix tailTrace_1649269
  have hstable : (prefixWord ++ tailWord_1649269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649269).length < 2 ^ (prefixWord ++ tailWord_1649269).sum := by decide
  have hdescent : baseEnd_1649269 < baseStart_1649269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649325 : List Nat := [1, 5, 2, 1, 1, 2, 1, 2, 6]
def baseStart_1649325 : Nat := 118140960795 + 1649325 * 2 ^ 59
def prefixEnd_1649325 : Nat := 4983230072969 + 3 ^ 40 * 1649325 * 2
def baseEnd_1649325 : Nat := 376398435767495440912177

theorem tailTrace_1649325 : CollatzResearch.WordTrace tailWord_1649325 prefixEnd_1649325 376398435767495440912177 := by
  unfold tailWord_1649325
  simp only [CollatzResearch.WordTrace]
  refine ⟨60155824749784682129237429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40103883166523121419491619 60155824749784682129237429)
  ·
    refine ⟨5639608570292313949616009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60155824749784682129237429 5639608570292313949616009)
    ·
      refine ⟨4229706427719235462212007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5639608570292313949616009 4229706427719235462212007)
      ·
        refine ⟨6344559641578853193318011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4229706427719235462212007 6344559641578853193318011)
        ·
          refine ⟨9516839462368279789977017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6344559641578853193318011 9516839462368279789977017)
          ·
            refine ⟨7137629596776209842482763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9516839462368279789977017 7137629596776209842482763)
            ·
              refine ⟨10706444395164314763724145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7137629596776209842482763 10706444395164314763724145)
              ·
                refine ⟨8029833296373236072793109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10706444395164314763724145 8029833296373236072793109)
                ·
                  refine ⟨376398435767495440912177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8029833296373236072793109 376398435767495440912177)
                  ·
                    rfl

theorem cell21_1649325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_1649325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649325 prefixEnd_1649325 := by exact prefixLift 1649325
  have htrace : WordTrace (prefixWord ++ tailWord_1649325) baseStart_1649325 baseEnd_1649325 := by
    simpa [prefixWord, tailWord_1649325, baseEnd_1649325] using wordTrace_append hprefix tailTrace_1649325
  have hstable : (prefixWord ++ tailWord_1649325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649325).length < 2 ^ (prefixWord ++ tailWord_1649325).sum := by decide
  have hdescent : baseEnd_1649325 < baseStart_1649325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649345 : List Nat := [1, 2, 6, 2, 1, 2, 1, 1, 5]
def baseStart_1649345 : Nat := 118140960795 + 1649345 * 2 ^ 59
def prefixEnd_1649345 : Nat := 4983230072969 + 3 ^ 40 * 1649345 * 2
def baseEnd_1649345 : Nat := 376403000039979850578803

theorem tailTrace_1649345 : CollatzResearch.WordTrace tailWord_1649345 prefixEnd_1649345 376403000039979850578803 := by
  unfold tailWord_1649345
  simp only [CollatzResearch.WordTrace]
  refine ⟨60156554209712225544965489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40104369473141483696643659 60156554209712225544965489)
  ·
    refine ⟨45117415657284169158724117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60156554209712225544965489 45117415657284169158724117)
    ·
      refine ⟨2114878858935195429315193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45117415657284169158724117 2114878858935195429315193)
      ·
        refine ⟨1586159144201396571986395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2114878858935195429315193 1586159144201396571986395)
        ·
          refine ⟨2379238716302094857979593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1586159144201396571986395 2379238716302094857979593)
          ·
            refine ⟨1784429037226571143484695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2379238716302094857979593 1784429037226571143484695)
            ·
              refine ⟨2676643555839856715227043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1784429037226571143484695 2676643555839856715227043)
              ·
                refine ⟨4014965333759785072840565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2676643555839856715227043 4014965333759785072840565)
                ·
                  refine ⟨376403000039979850578803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4014965333759785072840565 376403000039979850578803)
                  ·
                    rfl

theorem cell21_1649345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 5].length) (baseStart_1649345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649345 prefixEnd_1649345 := by exact prefixLift 1649345
  have htrace : WordTrace (prefixWord ++ tailWord_1649345) baseStart_1649345 baseEnd_1649345 := by
    simpa [prefixWord, tailWord_1649345, baseEnd_1649345] using wordTrace_append hprefix tailTrace_1649345
  have hstable : (prefixWord ++ tailWord_1649345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649345).length < 2 ^ (prefixWord ++ tailWord_1649345).sum := by decide
  have hdescent : baseEnd_1649345 < baseStart_1649345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649356 : List Nat := [2, 2, 1, 5, 1, 2, 2, 6]
def baseStart_1649356 : Nat := 118140960795 + 1649356 * 2 ^ 59
def prefixEnd_1649356 : Nat := 4983230072969 + 3 ^ 40 * 1649356 * 2
def baseEnd_1649356 : Nat := 125468503463282091965149

theorem tailTrace_1649356 : CollatzResearch.WordTrace tailWord_1649356 prefixEnd_1649356 125468503463282091965149 := by
  unfold tailWord_1649356
  simp only [CollatzResearch.WordTrace]
  refine ⟨30078477706336187211807961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40104636941781582949077281 30078477706336187211807961)
  ·
    refine ⟨22558858279752140408855971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30078477706336187211807961 22558858279752140408855971)
    ·
      refine ⟨33838287419628210613283957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22558858279752140408855971 33838287419628210613283957)
      ·
        refine ⟨3172339445590144744995371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33838287419628210613283957 3172339445590144744995371)
        ·
          refine ⟨4758509168385217117493057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3172339445590144744995371 4758509168385217117493057)
          ·
            refine ⟨3568881876288912838119793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4758509168385217117493057 3568881876288912838119793)
            ·
              refine ⟨2676661407216684628589845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3568881876288912838119793 2676661407216684628589845)
              ·
                refine ⟨125468503463282091965149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2676661407216684628589845 125468503463282091965149)
                ·
                  rfl

theorem cell21_1649356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 6].length) (baseStart_1649356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649356 prefixEnd_1649356 := by exact prefixLift 1649356
  have htrace : WordTrace (prefixWord ++ tailWord_1649356) baseStart_1649356 baseEnd_1649356 := by
    simpa [prefixWord, tailWord_1649356, baseEnd_1649356] using wordTrace_append hprefix tailTrace_1649356
  have hstable : (prefixWord ++ tailWord_1649356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649356).length < 2 ^ (prefixWord ++ tailWord_1649356).sum := by decide
  have hdescent : baseEnd_1649356 < baseStart_1649356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649396 : List Nat := [2, 6, 1, 1, 3, 1, 2, 2, 3]
def baseStart_1649396 : Nat := 118140960795 + 1649396 * 2 ^ 59
def prefixEnd_1649396 : Nat := 4983230072969 + 3 ^ 40 * 1649396 * 2
def baseEnd_1649396 : Nat := 376414638934815095228699

theorem tailTrace_1649396 : CollatzResearch.WordTrace tailWord_1649396 prefixEnd_1649396 376414638934815095228699 := by
  unfold tailWord_1649396
  simp only [CollatzResearch.WordTrace]
  refine ⟨30079207166263730627536021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40105609555018307503381361 30079207166263730627536021)
  ·
    refine ⟨1409962835918612373165751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30079207166263730627536021 1409962835918612373165751)
    ·
      refine ⟨2114944253877918559748627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1409962835918612373165751 2114944253877918559748627)
      ·
        refine ⟨3172416380816877839622941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2114944253877918559748627 3172416380816877839622941)
        ·
          refine ⟨1189656142806329189858603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3172416380816877839622941 1189656142806329189858603)
          ·
            refine ⟨1784484214209493784787905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1189656142806329189858603 1784484214209493784787905)
            ·
              refine ⟨1338363160657120338590929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1784484214209493784787905 1338363160657120338590929)
              ·
                refine ⟨1003772370492840253943197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1338363160657120338590929 1003772370492840253943197)
                ·
                  refine ⟨376414638934815095228699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1003772370492840253943197 376414638934815095228699)
                  ·
                    rfl

theorem cell21_1649396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_1649396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649396 prefixEnd_1649396 := by exact prefixLift 1649396
  have htrace : WordTrace (prefixWord ++ tailWord_1649396) baseStart_1649396 baseEnd_1649396 := by
    simpa [prefixWord, tailWord_1649396, baseEnd_1649396] using wordTrace_append hprefix tailTrace_1649396
  have hstable : (prefixWord ++ tailWord_1649396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649396).length < 2 ^ (prefixWord ++ tailWord_1649396).sum := by decide
  have hdescent : baseEnd_1649396 < baseStart_1649396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649404 : List Nat := [2, 2, 2, 1, 3, 2, 4, 2, 3]
def baseStart_1649404 : Nat := 118140960795 + 1649404 * 2 ^ 59
def prefixEnd_1649404 : Nat := 4983230072969 + 3 ^ 40 * 1649404 * 2
def baseEnd_1649404 : Nat := 376416464643808859095349

theorem tailTrace_1649404 : CollatzResearch.WordTrace tailWord_1649404 prefixEnd_1649404 376416464643808859095349 := by
  unfold tailWord_1649404
  simp only [CollatzResearch.WordTrace]
  refine ⟨30079353058249239310681633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40105804077665652414242177 30079353058249239310681633)
  ·
    refine ⟨22559514793686929483011225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30079353058249239310681633 22559514793686929483011225)
    ·
      refine ⟨16919636095265197112258419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22559514793686929483011225 16919636095265197112258419)
      ·
        refine ⟨25379454142897795668387629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16919636095265197112258419 25379454142897795668387629)
        ·
          refine ⟨9517295303586673375645361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25379454142897795668387629 9517295303586673375645361)
          ·
            refine ⟨7137971477690005031734021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9517295303586673375645361 7137971477690005031734021)
            ·
              refine ⟨1338369652066875943450129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7137971477690005031734021 1338369652066875943450129)
              ·
                refine ⟨1003777239050156957587597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1338369652066875943450129 1003777239050156957587597)
                ·
                  refine ⟨376416464643808859095349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1003777239050156957587597 376416464643808859095349)
                  ·
                    rfl

theorem cell21_1649404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2, 3].length) (baseStart_1649404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649404 prefixEnd_1649404 := by exact prefixLift 1649404
  have htrace : WordTrace (prefixWord ++ tailWord_1649404) baseStart_1649404 baseEnd_1649404 := by
    simpa [prefixWord, tailWord_1649404, baseEnd_1649404] using wordTrace_append hprefix tailTrace_1649404
  have hstable : (prefixWord ++ tailWord_1649404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649404).length < 2 ^ (prefixWord ++ tailWord_1649404).sum := by decide
  have hdescent : baseEnd_1649404 < baseStart_1649404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649522 : List Nat := [3, 2, 1, 2, 1, 1, 5, 1, 5]
def baseStart_1649522 : Nat := 118140960795 + 1649522 * 2 ^ 59
def prefixEnd_1649522 : Nat := 4983230072969 + 3 ^ 40 * 1649522 * 2
def baseEnd_1649522 : Nat := 376443393851466876128441

theorem tailTrace_1649522 : CollatzResearch.WordTrace tailWord_1649522 prefixEnd_1649522 376443393851466876128441 := by
  unfold tailWord_1649522
  simp only [CollatzResearch.WordTrace]
  refine ⟨15040752482517746193539705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40108673286713989849439213 15040752482517746193539705)
  ·
    refine ⟨11280564361888309645154779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15040752482517746193539705 11280564361888309645154779)
    ·
      refine ⟨16920846542832464467732169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11280564361888309645154779 16920846542832464467732169)
      ·
        refine ⟨12690634907124348350799127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16920846542832464467732169 12690634907124348350799127)
        ·
          refine ⟨19035952360686522526198691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12690634907124348350799127 19035952360686522526198691)
          ·
            refine ⟨28553928541029783789298037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19035952360686522526198691 28553928541029783789298037)
            ·
              refine ⟨2676930800721542230246691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28553928541029783789298037 2676930800721542230246691)
              ·
                refine ⟨4015396201082313345370037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2676930800721542230246691 4015396201082313345370037)
                ·
                  refine ⟨376443393851466876128441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4015396201082313345370037 376443393851466876128441)
                  ·
                    rfl

theorem cell21_1649522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_1649522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649522 prefixEnd_1649522 := by exact prefixLift 1649522
  have htrace : WordTrace (prefixWord ++ tailWord_1649522) baseStart_1649522 baseEnd_1649522 := by
    simpa [prefixWord, tailWord_1649522, baseEnd_1649522] using wordTrace_append hprefix tailTrace_1649522
  have hstable : (prefixWord ++ tailWord_1649522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649522).length < 2 ^ (prefixWord ++ tailWord_1649522).sum := by decide
  have hdescent : baseEnd_1649522 < baseStart_1649522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649570 : List Nat := [3, 3, 1, 2, 2, 2, 2, 2, 4]
def baseStart_1649570 : Nat := 118140960795 + 1649570 * 2 ^ 59
def prefixEnd_1649570 : Nat := 4983230072969 + 3 ^ 40 * 1649570 * 2
def baseEnd_1649570 : Nat := 376454348105429459328343

theorem tailTrace_1649570 : CollatzResearch.WordTrace tailWord_1649570 prefixEnd_1649570 376454348105429459328343 := by
  unfold tailWord_1649570
  simp only [CollatzResearch.WordTrace]
  refine ⟨15041190158474272242976541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40109840422598059314604109 15041190158474272242976541)
  ·
    refine ⟨5640446309427852091116203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15041190158474272242976541 5640446309427852091116203)
    ·
      refine ⟨8460669464141778136674305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5640446309427852091116203 8460669464141778136674305)
      ·
        refine ⟨6345502098106333602505729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8460669464141778136674305 6345502098106333602505729)
        ·
          refine ⟨4759126573579750201879297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6345502098106333602505729 4759126573579750201879297)
          ·
            refine ⟨3569344930184812651409473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4759126573579750201879297 3569344930184812651409473)
            ·
              refine ⟨2677008697638609488557105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3569344930184812651409473 2677008697638609488557105)
              ·
                refine ⟨2007756523228957116417829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2677008697638609488557105 2007756523228957116417829)
                ·
                  refine ⟨376454348105429459328343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2007756523228957116417829 376454348105429459328343)
                  ·
                    rfl

theorem cell21_1649570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_1649570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649570 prefixEnd_1649570 := by exact prefixLift 1649570
  have htrace : WordTrace (prefixWord ++ tailWord_1649570) baseStart_1649570 baseEnd_1649570 := by
    simpa [prefixWord, tailWord_1649570, baseEnd_1649570] using wordTrace_append hprefix tailTrace_1649570
  have hstable : (prefixWord ++ tailWord_1649570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649570).length < 2 ^ (prefixWord ++ tailWord_1649570).sum := by decide
  have hdescent : baseEnd_1649570 < baseStart_1649570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649598 : List Nat := [4, 2, 1, 1, 1, 2, 3, 2, 5]
def baseStart_1649598 : Nat := 118140960795 + 1649598 * 2 ^ 59
def prefixEnd_1649598 : Nat := 4983230072969 + 3 ^ 40 * 1649598 * 2
def baseEnd_1649598 : Nat := 376460738086907632861619

theorem tailTrace_1649598 : CollatzResearch.WordTrace tailWord_1649598 prefixEnd_1649598 376460738086907632861619 := by
  unfold tailWord_1649598
  simp only [CollatzResearch.WordTrace]
  refine ⟨7520722734724456219240681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40110521251863766502616965 7520722734724456219240681)
  ·
    refine ⟨5640542051043342164430511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7520722734724456219240681 5640542051043342164430511)
    ·
      refine ⟨8460813076565013246645767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5640542051043342164430511 8460813076565013246645767)
      ·
        refine ⟨12691219614847519869968651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8460813076565013246645767 12691219614847519869968651)
        ·
          refine ⟨19036829422271279804952977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12691219614847519869968651 19036829422271279804952977)
          ·
            refine ⟨14277622066703459853714733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19036829422271279804952977 14277622066703459853714733)
            ·
              refine ⟨5354108275013797445143025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14277622066703459853714733 5354108275013797445143025)
              ·
                refine ⟨4015581206260348083857269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5354108275013797445143025 4015581206260348083857269)
                ·
                  refine ⟨376460738086907632861619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4015581206260348083857269 376460738086907632861619)
                  ·
                    rfl

theorem cell21_1649598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_1649598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649598 prefixEnd_1649598 := by exact prefixLift 1649598
  have htrace : WordTrace (prefixWord ++ tailWord_1649598) baseStart_1649598 baseEnd_1649598 := by
    simpa [prefixWord, tailWord_1649598, baseEnd_1649598] using wordTrace_append hprefix tailTrace_1649598
  have hstable : (prefixWord ++ tailWord_1649598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649598).length < 2 ^ (prefixWord ++ tailWord_1649598).sum := by decide
  have hdescent : baseEnd_1649598 < baseStart_1649598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649612 : List Nat := [2, 2, 1, 4, 1, 1, 2, 2, 6]
def baseStart_1649612 : Nat := 118140960795 + 1649612 * 2 ^ 59
def prefixEnd_1649612 : Nat := 4983230072969 + 3 ^ 40 * 1649612 * 2
def baseEnd_1649612 : Nat := 376463933077646719628257

theorem tailTrace_1649612 : CollatzResearch.WordTrace tailWord_1649612 prefixEnd_1649612 376463933077646719628257 := by
  unfold tailWord_1649612
  simp only [CollatzResearch.WordTrace]
  refine ⟨30083146249872465072467545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40110861666496620096623393 30083146249872465072467545)
  ·
    refine ⟨22562359687404348804350659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30083146249872465072467545 22562359687404348804350659)
    ·
      refine ⟨33843539531106523206525989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22562359687404348804350659 33843539531106523206525989)
      ·
        refine ⟨6345663662082473101223623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33843539531106523206525989 6345663662082473101223623)
        ·
          refine ⟨9518495493123709651835435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6345663662082473101223623 9518495493123709651835435)
          ·
            refine ⟨14277743239685564477753153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9518495493123709651835435 14277743239685564477753153)
            ·
              refine ⟨10708307429764173358314865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14277743239685564477753153 10708307429764173358314865)
              ·
                refine ⟨8031230572323130018736149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10708307429764173358314865 8031230572323130018736149)
                ·
                  refine ⟨376463933077646719628257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8031230572323130018736149 376463933077646719628257)
                  ·
                    rfl

theorem cell21_1649612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_1649612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649612 prefixEnd_1649612 := by exact prefixLift 1649612
  have htrace : WordTrace (prefixWord ++ tailWord_1649612) baseStart_1649612 baseEnd_1649612 := by
    simpa [prefixWord, tailWord_1649612, baseEnd_1649612] using wordTrace_append hprefix tailTrace_1649612
  have hstable : (prefixWord ++ tailWord_1649612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649612).length < 2 ^ (prefixWord ++ tailWord_1649612).sum := by decide
  have hdescent : baseEnd_1649612 < baseStart_1649612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649615 : List Nat := [1, 1, 2, 1, 1, 7, 2, 3, 3]
def baseStart_1649615 : Nat := 118140960795 + 1649615 * 2 ^ 59
def prefixEnd_1649615 : Nat := 4983230072969 + 3 ^ 40 * 1649615 * 2
def baseEnd_1649615 : Nat := 376464617718519381078251

theorem tailTrace_1649615 : CollatzResearch.WordTrace tailWord_1649615 prefixEnd_1649615 376464617718519381078251 := by
  unfold tailWord_1649615
  simp only [CollatzResearch.WordTrace]
  refine ⟨60166401918734061657294299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40110934612489374438196199 60166401918734061657294299)
  ·
    refine ⟨90249602878101092485941449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60166401918734061657294299 90249602878101092485941449)
    ·
      refine ⟨67687202158575819364456087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90249602878101092485941449 67687202158575819364456087)
      ·
        refine ⟨101530803237863729046684131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67687202158575819364456087 101530803237863729046684131)
        ·
          refine ⟨152296204856795593570026197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101530803237863729046684131 152296204856795593570026197)
          ·
            refine ⟨3569442301331146724297489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 152296204856795593570026197 3569442301331146724297489)
            ·
              refine ⟨2677081725998360043223117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3569442301331146724297489 2677081725998360043223117)
              ·
                refine ⟨1003905647249385016208669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2677081725998360043223117 1003905647249385016208669)
                ·
                  refine ⟨376464617718519381078251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1003905647249385016208669 376464617718519381078251)
                  ·
                    rfl

theorem cell21_1649615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3, 3].length) (baseStart_1649615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649615 prefixEnd_1649615 := by exact prefixLift 1649615
  have htrace : WordTrace (prefixWord ++ tailWord_1649615) baseStart_1649615 baseEnd_1649615 := by
    simpa [prefixWord, tailWord_1649615, baseEnd_1649615] using wordTrace_append hprefix tailTrace_1649615
  have hstable : (prefixWord ++ tailWord_1649615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649615).length < 2 ^ (prefixWord ++ tailWord_1649615).sum := by decide
  have hdescent : baseEnd_1649615 < baseStart_1649615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649629 : List Nat := [1, 4, 3, 1, 2, 2, 1, 1, 6]
def baseStart_1649629 : Nat := 118140960795 + 1649629 * 2 ^ 59
def prefixEnd_1649629 : Nat := 4983230072969 + 3 ^ 40 * 1649629 * 2
def baseEnd_1649629 : Nat := 376467812709258467844889

theorem tailTrace_1649629 : CollatzResearch.WordTrace tailWord_1649629 prefixEnd_1649629 376467812709258467844889 := by
  unfold tailWord_1649629
  simp only [CollatzResearch.WordTrace]
  refine ⟨60166912540683342048303941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40111275027122228032202627 60166912540683342048303941)
  ·
    refine ⟨11281296101378126634056989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60166912540683342048303941 11281296101378126634056989)
    ·
      refine ⟨4230486038016797487771371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11281296101378126634056989 4230486038016797487771371)
      ·
        refine ⟨6345729057025196231657057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4230486038016797487771371 6345729057025196231657057)
        ·
          refine ⟨4759296792768897173742793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6345729057025196231657057 4759296792768897173742793)
          ·
            refine ⟨3569472594576672880307095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4759296792768897173742793 3569472594576672880307095)
            ·
              refine ⟨5354208891865009320460643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3569472594576672880307095 5354208891865009320460643)
              ·
                refine ⟨8031313337797513980690965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5354208891865009320460643 8031313337797513980690965)
                ·
                  refine ⟨376467812709258467844889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8031313337797513980690965 376467812709258467844889)
                  ·
                    rfl

theorem cell21_1649629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_1649629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649629 prefixEnd_1649629 := by exact prefixLift 1649629
  have htrace : WordTrace (prefixWord ++ tailWord_1649629) baseStart_1649629 baseEnd_1649629 := by
    simpa [prefixWord, tailWord_1649629, baseEnd_1649629] using wordTrace_append hprefix tailTrace_1649629
  have hstable : (prefixWord ++ tailWord_1649629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649629).length < 2 ^ (prefixWord ++ tailWord_1649629).sum := by decide
  have hdescent : baseEnd_1649629 < baseStart_1649629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649652 : List Nat := [2, 6, 2, 1, 1, 2, 2, 5]
def baseStart_1649652 : Nat := 118140960795 + 1649652 * 2 ^ 59
def prefixEnd_1649652 : Nat := 4983230072969 + 3 ^ 40 * 1649652 * 2
def baseEnd_1649652 : Nat := 125491020540871846320503

theorem tailTrace_1649652 : CollatzResearch.WordTrace tailWord_1649652 prefixEnd_1649652 125491020540871846320503 := by
  unfold tailWord_1649652
  simp only [CollatzResearch.WordTrace]
  refine ⟨30083875709800008488195605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40111834279733344650927473 30083875709800008488195605)
  ·
    refine ⟨1410181673896875397884169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30083875709800008488195605 1410181673896875397884169)
    ·
      refine ⟨1057636255422656548413127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1410181673896875397884169 1057636255422656548413127)
      ·
        refine ⟨1586454383133984822619691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1057636255422656548413127 1586454383133984822619691)
        ·
          refine ⟨2379681574700977233929537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1586454383133984822619691 2379681574700977233929537)
          ·
            refine ⟨1784761181025732925447153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2379681574700977233929537 1784761181025732925447153)
            ·
              refine ⟨1338570885769299694085365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1784761181025732925447153 1338570885769299694085365)
              ·
                refine ⟨125491020540871846320503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1338570885769299694085365 125491020540871846320503)
                ·
                  rfl

theorem cell21_1649652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 5].length) (baseStart_1649652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649652 prefixEnd_1649652 := by exact prefixLift 1649652
  have htrace : WordTrace (prefixWord ++ tailWord_1649652) baseStart_1649652 baseEnd_1649652 := by
    simpa [prefixWord, tailWord_1649652, baseEnd_1649652] using wordTrace_append hprefix tailTrace_1649652
  have hstable : (prefixWord ++ tailWord_1649652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649652).length < 2 ^ (prefixWord ++ tailWord_1649652).sum := by decide
  have hdescent : baseEnd_1649652 < baseStart_1649652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649657 : List Nat := [1, 2, 1, 3, 1, 3, 1, 4, 5]
def baseStart_1649657 : Nat := 118140960795 + 1649657 * 2 ^ 59
def prefixEnd_1649657 : Nat := 4983230072969 + 3 ^ 40 * 1649657 * 2
def baseEnd_1649657 : Nat := 376474202690736641378165

theorem tailTrace_1649657 : CollatzResearch.WordTrace tailWord_1649657 prefixEnd_1649657 376474202690736641378165 := by
  unfold tailWord_1649657
  simp only [CollatzResearch.WordTrace]
  refine ⟨60167933784581902830323225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40111955856387935220215483 60167933784581902830323225)
  ·
    refine ⟨45125950338436427122742419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60167933784581902830323225 45125950338436427122742419)
    ·
      refine ⟨67688925507654640684113629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45125950338436427122742419 67688925507654640684113629)
      ·
        refine ⟨25383347065370490256542611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67688925507654640684113629 25383347065370490256542611)
        ·
          refine ⟨38075020598055735384813917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25383347065370490256542611 38075020598055735384813917)
          ·
            refine ⟨14278132724270900769305219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38075020598055735384813917 14278132724270900769305219)
            ·
              refine ⟨21417199086406351153957829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14278132724270900769305219 21417199086406351153957829)
              ·
                refine ⟨4015724828701190841367093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21417199086406351153957829 4015724828701190841367093)
                ·
                  refine ⟨376474202690736641378165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4015724828701190841367093 376474202690736641378165)
                  ·
                    rfl

theorem cell21_1649657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 5].length) (baseStart_1649657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649657 prefixEnd_1649657 := by exact prefixLift 1649657
  have htrace : WordTrace (prefixWord ++ tailWord_1649657) baseStart_1649657 baseEnd_1649657 := by
    simpa [prefixWord, tailWord_1649657, baseEnd_1649657] using wordTrace_append hprefix tailTrace_1649657
  have hstable : (prefixWord ++ tailWord_1649657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649657).length < 2 ^ (prefixWord ++ tailWord_1649657).sum := by decide
  have hdescent : baseEnd_1649657 < baseStart_1649657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649660 : List Nat := [2, 2, 2, 1, 2, 5, 2, 5]
def baseStart_1649660 : Nat := 118140960795 + 1649660 * 2 ^ 59
def prefixEnd_1649660 : Nat := 4983230072969 + 3 ^ 40 * 1649660 * 2
def baseEnd_1649660 : Nat := 125491629110536434276053

theorem tailTrace_1649660 : CollatzResearch.WordTrace tailWord_1649660 prefixEnd_1649660 125491629110536434276053 := by
  unfold tailWord_1649660
  simp only [CollatzResearch.WordTrace]
  refine ⟨30084021601785517171341217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40112028802380689561788289 30084021601785517171341217)
  ·
    refine ⟨22563016201339137878505913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30084021601785517171341217 22563016201339137878505913)
    ·
      refine ⟨16922262151004353408879435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22563016201339137878505913 16922262151004353408879435)
      ·
        refine ⟨25383393226506530113319153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16922262151004353408879435 25383393226506530113319153)
        ·
          refine ⟨19037544919879897584989365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25383393226506530113319153 19037544919879897584989365)
          ·
            refine ⟨1784769836238740398592753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19037544919879897584989365 1784769836238740398592753)
            ·
              refine ⟨1338577377179055298944565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1784769836238740398592753 1338577377179055298944565)
              ·
                refine ⟨125491629110536434276053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1338577377179055298944565 125491629110536434276053)
                ·
                  rfl

theorem cell21_1649660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 5].length) (baseStart_1649660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649660 prefixEnd_1649660 := by exact prefixLift 1649660
  have htrace : WordTrace (prefixWord ++ tailWord_1649660) baseStart_1649660 baseEnd_1649660 := by
    simpa [prefixWord, tailWord_1649660, baseEnd_1649660] using wordTrace_append hprefix tailTrace_1649660
  have hstable : (prefixWord ++ tailWord_1649660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649660).length < 2 ^ (prefixWord ++ tailWord_1649660).sum := by decide
  have hdescent : baseEnd_1649660 < baseStart_1649660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649666 : List Nat := [3, 4, 1, 3, 1, 2, 1, 3, 3]
def baseStart_1649666 : Nat := 118140960795 + 1649666 * 2 ^ 59
def prefixEnd_1649666 : Nat := 4983230072969 + 3 ^ 40 * 1649666 * 2
def baseEnd_1649666 : Nat := 376476256613354625728147

theorem tailTrace_1649666 : CollatzResearch.WordTrace tailWord_1649666 prefixEnd_1649666 376476256613354625728147 := by
  unfold tailWord_1649666
  simp only [CollatzResearch.WordTrace]
  refine ⟨15042065510387324341850213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40112174694366198244933901 15042065510387324341850213)
  ·
    refine ⟨2820387283197623314096915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15042065510387324341850213 2820387283197623314096915)
    ·
      refine ⟨4230580924796434971145373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2820387283197623314096915 4230580924796434971145373)
      ·
        refine ⟨1586467846798663114179515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4230580924796434971145373 1586467846798663114179515)
        ·
          refine ⟨2379701770197994671269273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1586467846798663114179515 2379701770197994671269273)
          ·
            refine ⟨1784776327648496003451955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2379701770197994671269273 1784776327648496003451955)
            ·
              refine ⟨2677164491472744005177933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1784776327648496003451955 2677164491472744005177933)
              ·
                refine ⟨1003936684302279001941725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2677164491472744005177933 1003936684302279001941725)
                ·
                  refine ⟨376476256613354625728147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1003936684302279001941725 376476256613354625728147)
                  ·
                    rfl

theorem cell21_1649666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_1649666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649666 prefixEnd_1649666 := by exact prefixLift 1649666
  have htrace : WordTrace (prefixWord ++ tailWord_1649666) baseStart_1649666 baseEnd_1649666 := by
    simpa [prefixWord, tailWord_1649666, baseEnd_1649666] using wordTrace_append hprefix tailTrace_1649666
  have hstable : (prefixWord ++ tailWord_1649666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649666).length < 2 ^ (prefixWord ++ tailWord_1649666).sum := by decide
  have hdescent : baseEnd_1649666 < baseStart_1649666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649688 : List Nat := [2, 1, 2, 3, 2, 2, 2, 1, 6]
def baseStart_1649688 : Nat := 118140960795 + 1649688 * 2 ^ 59
def prefixEnd_1649688 : Nat := 4983230072969 + 3 ^ 40 * 1649688 * 2
def baseEnd_1649688 : Nat := 376481277313087476361435

theorem tailTrace_1649688 : CollatzResearch.WordTrace tailWord_1649688 prefixEnd_1649688 376481277313087476361435 := by
  unfold tailWord_1649688
  simp only [CollatzResearch.WordTrace]
  refine ⟨30084532223734797562350859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40112709631646396749801145 30084532223734797562350859)
  ·
    refine ⟨45126798335602196343526289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30084532223734797562350859 45126798335602196343526289)
    ·
      refine ⟨33845098751701647257644717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45126798335602196343526289 33845098751701647257644717)
      ·
        refine ⟨12691912031888117721616769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33845098751701647257644717 12691912031888117721616769)
        ·
          refine ⟨9518934023916088291212577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12691912031888117721616769 9518934023916088291212577)
          ·
            refine ⟨7139200517937066218409433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9518934023916088291212577 7139200517937066218409433)
            ·
              refine ⟨5354400388452799663807075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7139200517937066218409433 5354400388452799663807075)
              ·
                refine ⟨8031600582679199495710613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5354400388452799663807075 8031600582679199495710613)
                ·
                  refine ⟨376481277313087476361435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8031600582679199495710613 376481277313087476361435)
                  ·
                    rfl

theorem cell21_1649688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 6].length) (baseStart_1649688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649688 prefixEnd_1649688 := by exact prefixLift 1649688
  have htrace : WordTrace (prefixWord ++ tailWord_1649688) baseStart_1649688 baseEnd_1649688 := by
    simpa [prefixWord, tailWord_1649688, baseEnd_1649688] using wordTrace_append hprefix tailTrace_1649688
  have hstable : (prefixWord ++ tailWord_1649688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649688).length < 2 ^ (prefixWord ++ tailWord_1649688).sum := by decide
  have hdescent : baseEnd_1649688 < baseStart_1649688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649846 : List Nat := [5, 1, 3, 2, 2, 1, 7]
def baseStart_1649846 : Nat := 118140960795 + 1649846 * 2 ^ 59
def prefixEnd_1649846 : Nat := 4983230072969 + 3 ^ 40 * 1649846 * 2
def baseEnd_1649846 : Nat := 41835259451746034747531

theorem tailTrace_1649846 : CollatzResearch.WordTrace tailWord_1649846 prefixEnd_1649846 41835259451746034747531 := by
  unfold tailWord_1649846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3760926698806074256809587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40116551453931458739302261 3760926698806074256809587)
  ·
    refine ⟨5641390048209111385214381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3760926698806074256809587 5641390048209111385214381)
    ·
      refine ⟨2115521268078416769455393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5641390048209111385214381 2115521268078416769455393)
      ·
        refine ⟨1586640951058812577091545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2115521268078416769455393 1586640951058812577091545)
        ·
          refine ⟨1189980713294109432818659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1586640951058812577091545 1189980713294109432818659)
          ·
            refine ⟨1784971069941164149227989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1189980713294109432818659 1784971069941164149227989)
            ·
              refine ⟨41835259451746034747531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1784971069941164149227989 41835259451746034747531)
              ·
                rfl

theorem cell21_1649846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 7].length) (baseStart_1649846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649846 prefixEnd_1649846 := by exact prefixLift 1649846
  have htrace : WordTrace (prefixWord ++ tailWord_1649846) baseStart_1649846 baseEnd_1649846 := by
    simpa [prefixWord, tailWord_1649846, baseEnd_1649846] using wordTrace_append hprefix tailTrace_1649846
  have hstable : (prefixWord ++ tailWord_1649846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649846).length < 2 ^ (prefixWord ++ tailWord_1649846).sum := by decide
  have hdescent : baseEnd_1649846 < baseStart_1649846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649857 : List Nat := [1, 2, 6, 1, 1, 1, 2, 1, 6]
def baseStart_1649857 : Nat := 118140960795 + 1649857 * 2 ^ 59
def prefixEnd_1649857 : Nat := 4983230072969 + 3 ^ 40 * 1649857 * 2
def baseEnd_1649857 : Nat := 376519845415580738044423

theorem tailTrace_1649857 : CollatzResearch.WordTrace tailWord_1649857 prefixEnd_1649857 376519845415580738044423 := by
  unfold tailWord_1649857
  simp only [CollatzResearch.WordTrace]
  refine ⟨60175228383857336987603825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40116818922571557991735883 60175228383857336987603825)
  ·
    refine ⟨45131421287893002740702869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60175228383857336987603825 45131421287893002740702869)
    ·
      refine ⟨2115535372869984503470447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45131421287893002740702869 2115535372869984503470447)
      ·
        refine ⟨3173303059304976755205671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2115535372869984503470447 3173303059304976755205671)
        ·
          refine ⟨4759954588957465132808507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3173303059304976755205671 4759954588957465132808507)
          ·
            refine ⟨7139931883436197699212761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4759954588957465132808507 7139931883436197699212761)
            ·
              refine ⟨5354948912577148274409571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7139931883436197699212761 5354948912577148274409571)
              ·
                refine ⟨8032423368865722411614357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5354948912577148274409571 8032423368865722411614357)
                ·
                  refine ⟨376519845415580738044423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8032423368865722411614357 376519845415580738044423)
                  ·
                    rfl

theorem cell21_1649857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 6].length) (baseStart_1649857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649857 prefixEnd_1649857 := by exact prefixLift 1649857
  have htrace : WordTrace (prefixWord ++ tailWord_1649857) baseStart_1649857 baseEnd_1649857 := by
    simpa [prefixWord, tailWord_1649857, baseEnd_1649857] using wordTrace_append hprefix tailTrace_1649857
  have hstable : (prefixWord ++ tailWord_1649857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649857).length < 2 ^ (prefixWord ++ tailWord_1649857).sum := by decide
  have hdescent : baseEnd_1649857 < baseStart_1649857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649860 : List Nat := [2, 3, 3, 1, 4, 1, 1, 1, 5]
def baseStart_1649860 : Nat := 118140960795 + 1649860 * 2 ^ 59
def prefixEnd_1649860 : Nat := 4983230072969 + 3 ^ 40 * 1649860 * 2
def baseEnd_1649860 : Nat := 376520530056453399494417

theorem tailTrace_1649860 : CollatzResearch.WordTrace tailWord_1649860 prefixEnd_1649860 376520530056453399494417 := by
  unfold tailWord_1649860
  simp only [CollatzResearch.WordTrace]
  refine ⟨30087668901423234249981517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40116891868564312333308689 30087668901423234249981517)
  ·
    refine ⟨11282875838033712843743069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30087668901423234249981517 11282875838033712843743069)
    ·
      refine ⟨4231078439262642316403651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11282875838033712843743069 4231078439262642316403651)
      ·
        refine ⟨6346617658893963474605477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4231078439262642316403651 6346617658893963474605477)
        ·
          refine ⟨1189990811042618151488527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6346617658893963474605477 1189990811042618151488527)
          ·
            refine ⟨1784986216563927227232791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1189990811042618151488527 1784986216563927227232791)
            ·
              refine ⟨2677479324845890840849187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1784986216563927227232791 2677479324845890840849187)
              ·
                refine ⟨4016218987268836261273781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2677479324845890840849187 4016218987268836261273781)
                ·
                  refine ⟨376520530056453399494417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4016218987268836261273781 376520530056453399494417)
                  ·
                    rfl

theorem cell21_1649860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_1649860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649860 prefixEnd_1649860 := by exact prefixLift 1649860
  have htrace : WordTrace (prefixWord ++ tailWord_1649860) baseStart_1649860 baseEnd_1649860 := by
    simpa [prefixWord, tailWord_1649860, baseEnd_1649860] using wordTrace_append hprefix tailTrace_1649860
  have hstable : (prefixWord ++ tailWord_1649860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649860).length < 2 ^ (prefixWord ++ tailWord_1649860).sum := by decide
  have hdescent : baseEnd_1649860 < baseStart_1649860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649908 : List Nat := [2, 6, 1, 2, 1, 1, 2, 2, 4]
def baseStart_1649908 : Nat := 118140960795 + 1649908 * 2 ^ 59
def prefixEnd_1649908 : Nat := 4983230072969 + 3 ^ 40 * 1649908 * 2
def baseEnd_1649908 : Nat := 376531484310415982694319

theorem tailTrace_1649908 : CollatzResearch.WordTrace tailWord_1649908 prefixEnd_1649908 376531484310415982694319 := by
  unfold tailWord_1649908
  simp only [CollatzResearch.WordTrace]
  refine ⟨30088544253336286348855189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40118059004448381798473585 30088544253336286348855189)
  ·
    refine ⟨1410400511875138422602587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30088544253336286348855189 1410400511875138422602587)
    ·
      refine ⟨2115600767812707633903881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1410400511875138422602587 2115600767812707633903881)
      ·
        refine ⟨1586700575859530725427911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2115600767812707633903881 1586700575859530725427911)
        ·
          refine ⟨2380050863789296088141867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1586700575859530725427911 2380050863789296088141867)
          ·
            refine ⟨3570076295683944132212801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2380050863789296088141867 3570076295683944132212801)
            ·
              refine ⟨2677557221762958099159601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3570076295683944132212801 2677557221762958099159601)
              ·
                refine ⟨2008167916322218574369701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2677557221762958099159601 2008167916322218574369701)
                ·
                  refine ⟨376531484310415982694319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2008167916322218574369701 376531484310415982694319)
                  ·
                    rfl

theorem cell21_1649908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_1649908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649908 prefixEnd_1649908 := by exact prefixLift 1649908
  have htrace : WordTrace (prefixWord ++ tailWord_1649908) baseStart_1649908 baseEnd_1649908 := by
    simpa [prefixWord, tailWord_1649908, baseEnd_1649908] using wordTrace_append hprefix tailTrace_1649908
  have hstable : (prefixWord ++ tailWord_1649908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649908).length < 2 ^ (prefixWord ++ tailWord_1649908).sum := by decide
  have hdescent : baseEnd_1649908 < baseStart_1649908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649919 : List Nat := [1, 1, 2, 2, 1, 5, 4, 2, 3]
def baseStart_1649919 : Nat := 118140960795 + 1649919 * 2 ^ 59
def prefixEnd_1649919 : Nat := 4983230072969 + 3 ^ 40 * 1649919 * 2
def baseEnd_1649919 : Nat := 376533994660282408010963

theorem tailTrace_1649919 : CollatzResearch.WordTrace tailWord_1649919 prefixEnd_1649919 376533994660282408010963 := by
  unfold tailWord_1649919
  simp only [CollatzResearch.WordTrace]
  refine ⟨60177489709632721576360811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40118326473088481050907207 60177489709632721576360811)
  ·
    refine ⟨90266234564449082364541217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60177489709632721576360811 90266234564449082364541217)
    ·
      refine ⟨67699675923336811773405913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90266234564449082364541217 67699675923336811773405913)
      ·
        refine ⟨50774756942502608830054435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67699675923336811773405913 50774756942502608830054435)
        ·
          refine ⟨76162135413753913245081653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50774756942502608830054435 76162135413753913245081653)
          ·
            refine ⟨7140200195039429366726405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76162135413753913245081653 7140200195039429366726405)
            ·
              refine ⟨1338787536569893006261201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7140200195039429366726405 1338787536569893006261201)
              ·
                refine ⟨1004090652427419754695901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1338787536569893006261201 1004090652427419754695901)
                ·
                  refine ⟨376533994660282408010963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1004090652427419754695901 376533994660282408010963)
                  ·
                    rfl

theorem cell21_1649919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2, 3].length) (baseStart_1649919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649919 prefixEnd_1649919 := by exact prefixLift 1649919
  have htrace : WordTrace (prefixWord ++ tailWord_1649919) baseStart_1649919 baseEnd_1649919 := by
    simpa [prefixWord, tailWord_1649919, baseEnd_1649919] using wordTrace_append hprefix tailTrace_1649919
  have hstable : (prefixWord ++ tailWord_1649919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649919).length < 2 ^ (prefixWord ++ tailWord_1649919).sum := by decide
  have hdescent : baseEnd_1649919 < baseStart_1649919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649978 : List Nat := [3, 1, 1, 1, 4, 1, 1, 6, 3]
def baseStart_1649978 : Nat := 118140960795 + 1649978 * 2 ^ 59
def prefixEnd_1649978 : Nat := 4983230072969 + 3 ^ 40 * 1649978 * 2
def baseEnd_1649978 : Nat := 376547459264111416527509

theorem tailTrace_1649978 : CollatzResearch.WordTrace tailWord_1649978 prefixEnd_1649978 376547459264111416527509 := by
  unfold tailWord_1649978
  simp only [CollatzResearch.WordTrace]
  refine ⟨15044910404104743663189647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40119761077612649768505725 15044910404104743663189647)
  ·
    refine ⟨22567365606157115494784471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15044910404104743663189647 22567365606157115494784471)
    ·
      refine ⟨33851048409235673242176707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22567365606157115494784471 33851048409235673242176707)
      ·
        refine ⟨50776572613853509863265061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33851048409235673242176707 50776572613853509863265061)
        ·
          refine ⟨9520607365097533099362199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50776572613853509863265061 9520607365097533099362199)
          ·
            refine ⟨14280911047646299649043299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9520607365097533099362199 14280911047646299649043299)
            ·
              refine ⟨21421366571469449473564949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14280911047646299649043299 21421366571469449473564949)
              ·
                refine ⟨1004126558037630444073357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21421366571469449473564949 1004126558037630444073357)
                ·
                  refine ⟨376547459264111416527509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1004126558037630444073357 376547459264111416527509)
                  ·
                    rfl

theorem cell21_1649978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6, 3].length) (baseStart_1649978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1649978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1649978 prefixEnd_1649978 := by exact prefixLift 1649978
  have htrace : WordTrace (prefixWord ++ tailWord_1649978) baseStart_1649978 baseEnd_1649978 := by
    simpa [prefixWord, tailWord_1649978, baseEnd_1649978] using wordTrace_append hprefix tailTrace_1649978
  have hstable : (prefixWord ++ tailWord_1649978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649978).length < 2 ^ (prefixWord ++ tailWord_1649978).sum := by decide
  have hdescent : baseEnd_1649978 < baseStart_1649978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650023 : List Nat := [1, 1, 5, 1, 4, 2, 7]
def baseStart_1650023 : Nat := 118140960795 + 1650023 * 2 ^ 59
def prefixEnd_1650023 : Nat := 4983230072969 + 3 ^ 40 * 1650023 * 2
def baseEnd_1650023 : Nat := 41839747653022370919713

theorem tailTrace_1650023 : CollatzResearch.WordTrace tailWord_1650023 prefixEnd_1650023 41839747653022370919713 := by
  unfold tailWord_1650023
  simp only [CollatzResearch.WordTrace]
  refine ⟨60181282901255947338146723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40120855267503964892097815 60181282901255947338146723)
  ·
    refine ⟨90271924351883921007220085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60181282901255947338146723 90271924351883921007220085)
    ·
      refine ⟨8462992907989117594426883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90271924351883921007220085 8462992907989117594426883)
      ·
        refine ⟨12694489361983676391640325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8462992907989117594426883 12694489361983676391640325)
        ·
          refine ⟨2380216755371939323432561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12694489361983676391640325 2380216755371939323432561)
          ·
            refine ⟨1785162566528954492574421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2380216755371939323432561 1785162566528954492574421)
            ·
              refine ⟨41839747653022370919713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1785162566528954492574421 41839747653022370919713)
              ·
                rfl

theorem cell21_1650023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 7].length) (baseStart_1650023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1650023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1650023 prefixEnd_1650023 := by exact prefixLift 1650023
  have htrace : WordTrace (prefixWord ++ tailWord_1650023) baseStart_1650023 baseEnd_1650023 := by
    simpa [prefixWord, tailWord_1650023, baseEnd_1650023] using wordTrace_append hprefix tailTrace_1650023
  have hstable : (prefixWord ++ tailWord_1650023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650023).length < 2 ^ (prefixWord ++ tailWord_1650023).sum := by decide
  have hdescent : baseEnd_1650023 < baseStart_1650023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650082 : List Nat := [3, 3, 1, 2, 1, 11]
def baseStart_1650082 : Nat := 118140960795 + 1650082 * 2 ^ 59
def prefixEnd_1650082 : Nat := 4983230072969 + 3 ^ 40 * 1650082 * 2
def baseEnd_1650082 : Nat := 13947081240038160992369

theorem tailTrace_1650082 : CollatzResearch.WordTrace tailWord_1650082 prefixEnd_1650082 13947081240038160992369 := by
  unfold tailWord_1650082
  simp only [CollatzResearch.WordTrace]
  refine ⟨15045858702010550103636125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40122289872028133609696333 15045858702010550103636125)
  ·
    refine ⟨5642197013253956288863547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15045858702010550103636125 5642197013253956288863547)
    ·
      refine ⟨8463295519880934433295321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5642197013253956288863547 8463295519880934433295321)
      ·
        refine ⟨6347471639910700824971491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8463295519880934433295321 6347471639910700824971491)
        ·
          refine ⟨9521207459866051237457237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6347471639910700824971491 9521207459866051237457237)
          ·
            refine ⟨13947081240038160992369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9521207459866051237457237 13947081240038160992369)
            ·
              rfl

theorem cell21_1650082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 11].length) (baseStart_1650082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1650082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1650082 prefixEnd_1650082 := by exact prefixLift 1650082
  have htrace : WordTrace (prefixWord ++ tailWord_1650082) baseStart_1650082 baseEnd_1650082 := by
    simpa [prefixWord, tailWord_1650082, baseEnd_1650082] using wordTrace_append hprefix tailTrace_1650082
  have hstable : (prefixWord ++ tailWord_1650082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650082).length < 2 ^ (prefixWord ++ tailWord_1650082).sum := by decide
  have hdescent : baseEnd_1650082 < baseStart_1650082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650088 : List Nat := [2, 1, 6, 1, 2, 1, 1, 4, 3]
def baseStart_1650088 : Nat := 118140960795 + 1650088 * 2 ^ 59
def prefixEnd_1650088 : Nat := 4983230072969 + 3 ^ 40 * 1650088 * 2
def baseEnd_1650088 : Nat := 376572562762775669693951

theorem tailTrace_1650088 : CollatzResearch.WordTrace tailWord_1650088 prefixEnd_1650088 376572562762775669693951 := by
  unfold tailWord_1650088
  simp only [CollatzResearch.WordTrace]
  refine ⟨30091826823010231719631459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40122435764013642292841945 30091826823010231719631459)
  ·
    refine ⟨45137740234515347579447189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30091826823010231719631459 45137740234515347579447189)
    ·
      refine ⟨2115831573492906917786587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45137740234515347579447189 2115831573492906917786587)
      ·
        refine ⟨3173747360239360376679881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2115831573492906917786587 3173747360239360376679881)
        ·
          refine ⟨2380310520179520282509911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3173747360239360376679881 2380310520179520282509911)
          ·
            refine ⟨3570465780269280423764867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2380310520179520282509911 3570465780269280423764867)
            ·
              refine ⟨5355698670403920635647301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3570465780269280423764867 5355698670403920635647301)
              ·
                refine ⟨1004193500700735119183869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5355698670403920635647301 1004193500700735119183869)
                ·
                  refine ⟨376572562762775669693951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1004193500700735119183869 376572562762775669693951)
                  ·
                    rfl

theorem cell21_1650088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4, 3].length) (baseStart_1650088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1650088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1650088 prefixEnd_1650088 := by exact prefixLift 1650088
  have htrace : WordTrace (prefixWord ++ tailWord_1650088) baseStart_1650088 baseEnd_1650088 := by
    simpa [prefixWord, tailWord_1650088, baseEnd_1650088] using wordTrace_append hprefix tailTrace_1650088
  have hstable : (prefixWord ++ tailWord_1650088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650088).length < 2 ^ (prefixWord ++ tailWord_1650088).sum := by decide
  have hdescent : baseEnd_1650088 < baseStart_1650088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650116 : List Nat := [2, 3, 3, 2, 1, 2, 3, 5]
def baseStart_1650116 : Nat := 118140960795 + 1650116 * 2 ^ 59
def prefixEnd_1650116 : Nat := 4983230072969 + 3 ^ 40 * 1650116 * 2
def baseEnd_1650116 : Nat := 125526317581417947742409

theorem tailTrace_1650116 : CollatzResearch.WordTrace tailWord_1650116 prefixEnd_1650116 125526317581417947742409 := by
  unfold tailWord_1650116
  simp only [CollatzResearch.WordTrace]
  refine ⟨30092337444959512110641101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40123116593279349480854801 30092337444959512110641101)
  ·
    refine ⟨11284626541859817041490413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30092337444959512110641101 11284626541859817041490413)
    ·
      refine ⟨4231734953197431390558905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11284626541859817041490413 4231734953197431390558905)
      ·
        refine ⟨3173801214898073542919179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4231734953197431390558905 3173801214898073542919179)
        ·
          refine ⟨4760701822347110314378769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3173801214898073542919179 4760701822347110314378769)
          ·
            refine ⟨3570526366760332735784077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4760701822347110314378769 3570526366760332735784077)
            ·
              refine ⟨1338947387535124775919029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3570526366760332735784077 1338947387535124775919029)
              ·
                refine ⟨125526317581417947742409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1338947387535124775919029 125526317581417947742409)
                ·
                  rfl

theorem cell21_1650116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 5].length) (baseStart_1650116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1650116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1650116 prefixEnd_1650116 := by exact prefixLift 1650116
  have htrace : WordTrace (prefixWord ++ tailWord_1650116) baseStart_1650116 baseEnd_1650116 := by
    simpa [prefixWord, tailWord_1650116, baseEnd_1650116] using wordTrace_append hprefix tailTrace_1650116
  have hstable : (prefixWord ++ tailWord_1650116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650116).length < 2 ^ (prefixWord ++ tailWord_1650116).sum := by decide
  have hdescent : baseEnd_1650116 < baseStart_1650116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650158 : List Nat := [4, 1, 2, 1, 2, 1, 2, 8]
def baseStart_1650158 : Nat := 118140960795 + 1650158 * 2 ^ 59
def prefixEnd_1650158 : Nat := 4983230072969 + 3 ^ 40 * 1650158 * 2
def baseEnd_1650158 : Nat := 125529512572157034509047

theorem tailTrace_1650158 : CollatzResearch.WordTrace tailWord_1650158 prefixEnd_1650158 125529512572157034509047 := by
  unfold tailWord_1650158
  simp only [CollatzResearch.WordTrace]
  refine ⟨7523275844470858174288891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40124137837177910262874085 7523275844470858174288891)
  ·
    refine ⟨11284913766706287261433337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7523275844470858174288891 11284913766706287261433337)
    ·
      refine ⟨8463685325029715446075003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11284913766706287261433337 8463685325029715446075003)
      ·
        refine ⟨12695527987544573169112505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8463685325029715446075003 12695527987544573169112505)
        ·
          refine ⟨9521645990658429876834379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12695527987544573169112505 9521645990658429876834379)
          ·
            refine ⟨14282468985987644815251569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9521645990658429876834379 14282468985987644815251569)
            ·
              refine ⟨10711851739490733611438677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14282468985987644815251569 10711851739490733611438677)
              ·
                refine ⟨125529512572157034509047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10711851739490733611438677 125529512572157034509047)
                ·
                  rfl

theorem cell21_1650158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_1650158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1650158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1650158 prefixEnd_1650158 := by exact prefixLift 1650158
  have htrace : WordTrace (prefixWord ++ tailWord_1650158) baseStart_1650158 baseEnd_1650158 := by
    simpa [prefixWord, tailWord_1650158, baseEnd_1650158] using wordTrace_append hprefix tailTrace_1650158
  have hstable : (prefixWord ++ tailWord_1650158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650158).length < 2 ^ (prefixWord ++ tailWord_1650158).sum := by decide
  have hdescent : baseEnd_1650158 < baseStart_1650158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650161 : List Nat := [1, 2, 2, 2, 3, 3, 3, 1, 4]
def baseStart_1650161 : Nat := 118140960795 + 1650161 * 2 ^ 59
def prefixEnd_1650161 : Nat := 4983230072969 + 3 ^ 40 * 1650161 * 2
def baseEnd_1650161 : Nat := 376589222357343764977135

theorem tailTrace_1650161 : CollatzResearch.WordTrace tailWord_1650161 prefixEnd_1650161 376589222357343764977135 := by
  unfold tailWord_1650161
  simp only [CollatzResearch.WordTrace]
  refine ⟨60186316174755996906670337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40124210783170664604446891 60186316174755996906670337)
  ·
    refine ⟨45139737131066997680002753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60186316174755996906670337 45139737131066997680002753)
    ·
      refine ⟨33854802848300248260002065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45139737131066997680002753 33854802848300248260002065)
      ·
        refine ⟨25391102136225186195001549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33854802848300248260002065 25391102136225186195001549)
        ·
          refine ⟨9521663301084444823125581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25391102136225186195001549 9521663301084444823125581)
          ·
            refine ⟨3570623737906666808672093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9521663301084444823125581 3570623737906666808672093)
            ·
              refine ⟨1338983901715000053252035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3570623737906666808672093 1338983901715000053252035)
              ·
                refine ⟨2008475852572500079878053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1338983901715000053252035 2008475852572500079878053)
                ·
                  refine ⟨376589222357343764977135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2008475852572500079878053 376589222357343764977135)
                  ·
                    rfl

theorem cell21_1650161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 4].length) (baseStart_1650161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1650161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1650161 prefixEnd_1650161 := by exact prefixLift 1650161
  have htrace : WordTrace (prefixWord ++ tailWord_1650161) baseStart_1650161 baseEnd_1650161 := by
    simpa [prefixWord, tailWord_1650161, baseEnd_1650161] using wordTrace_append hprefix tailTrace_1650161
  have hstable : (prefixWord ++ tailWord_1650161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650161).length < 2 ^ (prefixWord ++ tailWord_1650161).sum := by decide
  have hdescent : baseEnd_1650161 < baseStart_1650161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650372 : List Nat := [2, 3, 3, 1, 1, 1, 2, 4, 4]
def baseStart_1650372 : Nat := 118140960795 + 1650372 * 2 ^ 59
def prefixEnd_1650372 : Nat := 4983230072969 + 3 ^ 40 * 1650372 * 2
def baseEnd_1650372 : Nat := 376637375432054286960037

theorem tailTrace_1650372 : CollatzResearch.WordTrace tailWord_1650372 prefixEnd_1650372 376637375432054286960037 := by
  unfold tailWord_1650372
  simp only [CollatzResearch.WordTrace]
  refine ⟨30097005988495789971300685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40129341317994386628400913 30097005988495789971300685)
  ·
    refine ⟨11286377245685921239237757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30097005988495789971300685 11286377245685921239237757)
    ·
      refine ⟨4232391467132220464714159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11286377245685921239237757 4232391467132220464714159)
      ·
        refine ⟨6348587200698330697071239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4232391467132220464714159 6348587200698330697071239)
        ·
          refine ⟨9522880801047496045606859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6348587200698330697071239 9522880801047496045606859)
          ·
            refine ⟨14284321201571244068410289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9522880801047496045606859 14284321201571244068410289)
            ·
              refine ⟨10713240901178433051307717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14284321201571244068410289 10713240901178433051307717)
              ·
                refine ⟨2008732668970956197120197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10713240901178433051307717 2008732668970956197120197)
                ·
                  refine ⟨376637375432054286960037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2008732668970956197120197 376637375432054286960037)
                  ·
                    rfl

theorem cell21_1650372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_1650372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1650372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1650372 prefixEnd_1650372 := by exact prefixLift 1650372
  have htrace : WordTrace (prefixWord ++ tailWord_1650372) baseStart_1650372 baseEnd_1650372 := by
    simpa [prefixWord, tailWord_1650372, baseEnd_1650372] using wordTrace_append hprefix tailTrace_1650372
  have hstable : (prefixWord ++ tailWord_1650372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650372).length < 2 ^ (prefixWord ++ tailWord_1650372).sum := by decide
  have hdescent : baseEnd_1650372 < baseStart_1650372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650386 : List Nat := [3, 2, 2, 2, 2, 1, 1, 8]
def baseStart_1650386 : Nat := 118140960795 + 1650386 * 2 ^ 59
def prefixEnd_1650386 : Nat := 4983230072969 + 3 ^ 40 * 1650386 * 2
def baseEnd_1650386 : Nat := 125546856807597791242225

theorem tailTrace_1650386 : CollatzResearch.WordTrace tailWord_1650386 prefixEnd_1650386 125546856807597791242225 := by
  unfold tailWord_1650386
  simp only [CollatzResearch.WordTrace]
  refine ⟨15048630649735215083402753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40129681732627240222407341 15048630649735215083402753)
  ·
    refine ⟨11286472987301411312552065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15048630649735215083402753 11286472987301411312552065)
    ·
      refine ⟨8464854740476058484414049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11286472987301411312552065 8464854740476058484414049)
      ·
        refine ⟨6348641055357043863310537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8464854740476058484414049 6348641055357043863310537)
        ·
          refine ⟨4761480791517782897482903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6348641055357043863310537 4761480791517782897482903)
          ·
            refine ⟨7142221187276674346224355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4761480791517782897482903 7142221187276674346224355)
            ·
              refine ⟨10713331780915011519336533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7142221187276674346224355 10713331780915011519336533)
              ·
                refine ⟨125546856807597791242225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10713331780915011519336533 125546856807597791242225)
                ·
                  rfl

theorem cell21_1650386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_1650386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1650386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1650386 prefixEnd_1650386 := by exact prefixLift 1650386
  have htrace : WordTrace (prefixWord ++ tailWord_1650386) baseStart_1650386 baseEnd_1650386 := by
    simpa [prefixWord, tailWord_1650386, baseEnd_1650386] using wordTrace_append hprefix tailTrace_1650386
  have hstable : (prefixWord ++ tailWord_1650386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650386).length < 2 ^ (prefixWord ++ tailWord_1650386).sum := by decide
  have hdescent : baseEnd_1650386 < baseStart_1650386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650400 : List Nat := [2, 1, 1, 3, 1, 2, 2, 4, 5]
def baseStart_1650400 : Nat := 118140960795 + 1650400 * 2 ^ 59
def prefixEnd_1650400 : Nat := 4983230072969 + 3 ^ 40 * 1650400 * 2
def baseEnd_1650400 : Nat := 376643765413532460493313

theorem tailTrace_1650400 : CollatzResearch.WordTrace tailWord_1650400 prefixEnd_1650400 376643765413532460493313 := by
  unfold tailWord_1650400
  simp only [CollatzResearch.WordTrace]
  refine ⟨30097516610445070362310327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40130022147260093816413769 30097516610445070362310327)
  ·
    refine ⟨45146274915667605543465491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30097516610445070362310327 45146274915667605543465491)
    ·
      refine ⟨67719412373501408315198237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45146274915667605543465491 67719412373501408315198237)
      ·
        refine ⟨25394779640063028118199339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67719412373501408315198237 25394779640063028118199339)
        ·
          refine ⟨38092169460094542177299009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25394779640063028118199339 38092169460094542177299009)
          ·
            refine ⟨28569127095070906632974257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38092169460094542177299009 28569127095070906632974257)
            ·
              refine ⟨21426845321303179974730693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28569127095070906632974257 21426845321303179974730693)
              ·
                refine ⟨4017533497744346245262005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21426845321303179974730693 4017533497744346245262005)
                ·
                  refine ⟨376643765413532460493313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4017533497744346245262005 376643765413532460493313)
                  ·
                    rfl

theorem cell21_1650400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 5].length) (baseStart_1650400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1650400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1650400 prefixEnd_1650400 := by exact prefixLift 1650400
  have htrace : WordTrace (prefixWord ++ tailWord_1650400) baseStart_1650400 baseEnd_1650400 := by
    simpa [prefixWord, tailWord_1650400, baseEnd_1650400] using wordTrace_append hprefix tailTrace_1650400
  have hstable : (prefixWord ++ tailWord_1650400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650400).length < 2 ^ (prefixWord ++ tailWord_1650400).sum := by decide
  have hdescent : baseEnd_1650400 < baseStart_1650400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650431 : List Nat := [1, 1, 2, 2, 1, 3, 3, 4, 4]
def baseStart_1650431 : Nat := 118140960795 + 1650431 * 2 ^ 59
def prefixEnd_1650431 : Nat := 4983230072969 + 3 ^ 40 * 1650431 * 2
def baseEnd_1650431 : Nat := 376650840035883295476583

theorem tailTrace_1650431 : CollatzResearch.WordTrace tailWord_1650431 prefixEnd_1650431 376650840035883295476583 := by
  unfold tailWord_1650431
  simp only [CollatzResearch.WordTrace]
  refine ⟨60196163883777833018999147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40130775922518555345999431 60196163883777833018999147)
  ·
    refine ⟨90294245825666749528498721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60196163883777833018999147 90294245825666749528498721)
    ·
      refine ⟨67720684369250062146374041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90294245825666749528498721 67720684369250062146374041)
      ·
        refine ⟨50790513276937546609780531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67720684369250062146374041 50790513276937546609780531)
        ·
          refine ⟨76185769915406319914670797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50790513276937546609780531 76185769915406319914670797)
          ·
            refine ⟨28569663718277369968001549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76185769915406319914670797 28569663718277369968001549)
            ·
              refine ⟨10713623894354013738000581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28569663718277369968001549 10713623894354013738000581)
              ·
                refine ⟨2008804480191377575875109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10713623894354013738000581 2008804480191377575875109)
                ·
                  refine ⟨376650840035883295476583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2008804480191377575875109 376650840035883295476583)
                  ·
                    rfl

theorem cell21_1650431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 4].length) (baseStart_1650431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1650431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1650431 prefixEnd_1650431 := by exact prefixLift 1650431
  have htrace : WordTrace (prefixWord ++ tailWord_1650431) baseStart_1650431 baseEnd_1650431 := by
    simpa [prefixWord, tailWord_1650431, baseEnd_1650431] using wordTrace_append hprefix tailTrace_1650431
  have hstable : (prefixWord ++ tailWord_1650431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650431).length < 2 ^ (prefixWord ++ tailWord_1650431).sum := by decide
  have hdescent : baseEnd_1650431 < baseStart_1650431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650493 : List Nat := [1, 4, 1, 4, 1, 1, 1, 3, 5]
def baseStart_1650493 : Nat := 118140960795 + 1650493 * 2 ^ 59
def prefixEnd_1650493 : Nat := 4983230072969 + 3 ^ 40 * 1650493 * 2
def baseEnd_1650493 : Nat := 376664989280584965443123

theorem tailTrace_1650493 : CollatzResearch.WordTrace tailWord_1650493 prefixEnd_1650493 376664989280584965443123 := by
  unfold tailWord_1650493
  simp only [CollatzResearch.WordTrace]
  refine ⟨60198425209553217607756133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40132283473035478405170755 60198425209553217607756133)
  ·
    refine ⟨11287204726791228301454275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60198425209553217607756133 11287204726791228301454275)
    ·
      refine ⟨16930807090186842452181413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11287204726791228301454275 16930807090186842452181413)
      ·
        refine ⟨3174526329410032959784015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16930807090186842452181413 3174526329410032959784015)
        ·
          refine ⟨4761789494115049439676023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3174526329410032959784015 4761789494115049439676023)
          ·
            refine ⟨7142684241172574159514035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4761789494115049439676023 7142684241172574159514035)
            ·
              refine ⟨10714026361758861239271053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7142684241172574159514035 10714026361758861239271053)
              ·
                refine ⟨4017759885659572964726645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10714026361758861239271053 4017759885659572964726645)
                ·
                  refine ⟨376664989280584965443123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4017759885659572964726645 376664989280584965443123)
                  ·
                    rfl

theorem cell21_1650493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_1650493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1650493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1650493 prefixEnd_1650493 := by exact prefixLift 1650493
  have htrace : WordTrace (prefixWord ++ tailWord_1650493) baseStart_1650493 baseEnd_1650493 := by
    simpa [prefixWord, tailWord_1650493, baseEnd_1650493] using wordTrace_append hprefix tailTrace_1650493
  have hstable : (prefixWord ++ tailWord_1650493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650493).length < 2 ^ (prefixWord ++ tailWord_1650493).sum := by decide
  have hdescent : baseEnd_1650493 < baseStart_1650493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650521 : List Nat := [1, 2, 1, 2, 2, 3, 3, 7]
def baseStart_1650521 : Nat := 118140960795 + 1650521 * 2 ^ 59
def prefixEnd_1650521 : Nat := 4983230072969 + 3 ^ 40 * 1650521 * 2
def baseEnd_1650521 : Nat := 125557126420687712992133

theorem tailTrace_1650521 : CollatzResearch.WordTrace tailWord_1650521 prefixEnd_1650521 125557126420687712992133 := by
  unfold tailWord_1650521
  simp only [CollatzResearch.WordTrace]
  refine ⟨60199446453451778389775417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40132964302301185593183611 60199446453451778389775417)
  ·
    refine ⟨45149584840088833792331563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60199446453451778389775417 45149584840088833792331563)
    ·
      refine ⟨67724377260133250688497345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45149584840088833792331563 67724377260133250688497345)
      ·
        refine ⟨50793282945099938016373009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67724377260133250688497345 50793282945099938016373009)
        ·
          refine ⟨38094962208824953512279757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50793282945099938016373009 38094962208824953512279757)
          ·
            refine ⟨14285610828309357567104909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38094962208824953512279757 14285610828309357567104909)
            ·
              refine ⟨5357104060616009087664341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14285610828309357567104909 5357104060616009087664341)
              ·
                refine ⟨125557126420687712992133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5357104060616009087664341 125557126420687712992133)
                ·
                  rfl

theorem cell21_1650521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 7].length) (baseStart_1650521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1650521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1650521 prefixEnd_1650521 := by exact prefixLift 1650521
  have htrace : WordTrace (prefixWord ++ tailWord_1650521) baseStart_1650521 baseEnd_1650521 := by
    simpa [prefixWord, tailWord_1650521, baseEnd_1650521] using wordTrace_append hprefix tailTrace_1650521
  have hstable : (prefixWord ++ tailWord_1650521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650521).length < 2 ^ (prefixWord ++ tailWord_1650521).sum := by decide
  have hdescent : baseEnd_1650521 < baseStart_1650521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650558 : List Nat := [4, 2, 3, 1, 1, 1, 4, 1, 4]
def baseStart_1650558 : Nat := 118140960795 + 1650558 * 2 ^ 59
def prefixEnd_1650558 : Nat := 4983230072969 + 3 ^ 40 * 1650558 * 2
def baseEnd_1650558 : Nat := 376679823166159296859657

theorem tailTrace_1650558 : CollatzResearch.WordTrace tailWord_1650558 prefixEnd_1650558 376679823166159296859657 := by
  unfold tailWord_1650558
  simp only [CollatzResearch.WordTrace]
  refine ⟨7525099494289716713609041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40133863969545155805914885 7525099494289716713609041)
  ·
    refine ⟨5643824620717287535206781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7525099494289716713609041 5643824620717287535206781)
    ·
      refine ⟨2116434232768982825702543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5643824620717287535206781 2116434232768982825702543)
      ·
        refine ⟨3174651349153474238553815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2116434232768982825702543 3174651349153474238553815)
        ·
          refine ⟨4761977023730211357830723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3174651349153474238553815 4761977023730211357830723)
          ·
            refine ⟨7142965535595317036746085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4761977023730211357830723 7142965535595317036746085)
            ·
              refine ⟨1339306037924121944389891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7142965535595317036746085 1339306037924121944389891)
              ·
                refine ⟨2008959056886182916584837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339306037924121944389891 2008959056886182916584837)
                ·
                  refine ⟨376679823166159296859657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2008959056886182916584837 376679823166159296859657)
                  ·
                    rfl

theorem cell21_1650558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_1650558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1650558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1650558 prefixEnd_1650558 := by exact prefixLift 1650558
  have htrace : WordTrace (prefixWord ++ tailWord_1650558) baseStart_1650558 baseEnd_1650558 := by
    simpa [prefixWord, tailWord_1650558, baseEnd_1650558] using wordTrace_append hprefix tailTrace_1650558
  have hstable : (prefixWord ++ tailWord_1650558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650558).length < 2 ^ (prefixWord ++ tailWord_1650558).sum := by decide
  have hdescent : baseEnd_1650558 < baseStart_1650558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650606 : List Nat := [4, 1, 5, 1, 2, 1, 1, 6]
def baseStart_1650606 : Nat := 118140960795 + 1650606 * 2 ^ 59
def prefixEnd_1650606 : Nat := 4983230072969 + 3 ^ 40 * 1650606 * 2
def baseEnd_1650606 : Nat := 125563592473373960019853

theorem tailTrace_1650606 : CollatzResearch.WordTrace tailWord_1650606 prefixEnd_1650606 125563592473373960019853 := by
  unfold tailWord_1650606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7525318332267979738327459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40135031105429225271079781 7525318332267979738327459)
  ·
    refine ⟨11287977498401969607491189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7525318332267979738327459 11287977498401969607491189)
    ·
      refine ⟨1058247890475184650702299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11287977498401969607491189 1058247890475184650702299)
      ·
        refine ⟨1587371835712776976053449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1058247890475184650702299 1587371835712776976053449)
        ·
          refine ⟨1190528876784582732040087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1587371835712776976053449 1190528876784582732040087)
          ·
            refine ⟨1785793315176874098060131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190528876784582732040087 1785793315176874098060131)
            ·
              refine ⟨2678689972765311147090197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1785793315176874098060131 2678689972765311147090197)
              ·
                refine ⟨125563592473373960019853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2678689972765311147090197 125563592473373960019853)
                ·
                  rfl

theorem cell21_1650606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_1650606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1650606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1650606 prefixEnd_1650606 := by exact prefixLift 1650606
  have htrace : WordTrace (prefixWord ++ tailWord_1650606) baseStart_1650606 baseEnd_1650606 := by
    simpa [prefixWord, tailWord_1650606, baseEnd_1650606] using wordTrace_append hprefix tailTrace_1650606
  have hstable : (prefixWord ++ tailWord_1650606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650606).length < 2 ^ (prefixWord ++ tailWord_1650606).sum := by decide
  have hdescent : baseEnd_1650606 < baseStart_1650606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650659 : List Nat := [1, 1, 1, 6, 1, 3, 1, 1, 6]
def baseStart_1650659 : Nat := 118140960795 + 1650659 * 2 ^ 59
def prefixEnd_1650659 : Nat := 4983230072969 + 3 ^ 40 * 1650659 * 2
def baseEnd_1650659 : Nat := 376702872742205565676117

theorem tailTrace_1650659 : CollatzResearch.WordTrace tailWord_1650659 prefixEnd_1650659 376702872742205565676117 := by
  unfold tailWord_1650659
  simp only [CollatzResearch.WordTrace]
  refine ⟨60204479726951827958299031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40136319817967885305532687 60204479726951827958299031)
  ·
    refine ⟨90306719590427741937448547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60204479726951827958299031 90306719590427741937448547)
    ·
      refine ⟨135460079385641612906172821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90306719590427741937448547 135460079385641612906172821)
      ·
        refine ⟨6349691221201950604976851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 135460079385641612906172821 6349691221201950604976851)
        ·
          refine ⟨9524536831802925907465277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6349691221201950604976851 9524536831802925907465277)
          ·
            refine ⟨3571701311926097215299479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9524536831802925907465277 3571701311926097215299479)
            ·
              refine ⟨5357551967889145822949219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3571701311926097215299479 5357551967889145822949219)
              ·
                refine ⟨8036327951833718734423829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5357551967889145822949219 8036327951833718734423829)
                ·
                  refine ⟨376702872742205565676117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8036327951833718734423829 376702872742205565676117)
                  ·
                    rfl

theorem cell21_1650659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 6].length) (baseStart_1650659 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1650659 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1650659 prefixEnd_1650659 := by exact prefixLift 1650659
  have htrace : WordTrace (prefixWord ++ tailWord_1650659) baseStart_1650659 baseEnd_1650659 := by
    simpa [prefixWord, tailWord_1650659, baseEnd_1650659] using wordTrace_append hprefix tailTrace_1650659
  have hstable : (prefixWord ++ tailWord_1650659).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650659).length < 2 ^ (prefixWord ++ tailWord_1650659).sum := by decide
  have hdescent : baseEnd_1650659 < baseStart_1650659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650727 : List Nat := [1, 1, 7, 1, 3, 1, 2, 1, 4]
def baseStart_1650727 : Nat := 118140960795 + 1650727 * 2 ^ 59
def prefixEnd_1650727 : Nat := 4983230072969 + 3 ^ 40 * 1650727 * 2
def baseEnd_1650727 : Nat := 376718391268652558542645

theorem tailTrace_1650727 : CollatzResearch.WordTrace tailWord_1650727 prefixEnd_1650727 376718391268652558542645 := by
  unfold tailWord_1650727
  simp only [CollatzResearch.WordTrace]
  refine ⟨60206959890705475571774435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40137973260470317047849623 60206959890705475571774435)
  ·
    refine ⟨90310439836058213357661653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60206959890705475571774435 90310439836058213357661653)
    ·
      refine ⟨2116650933657614375570195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 90310439836058213357661653 2116650933657614375570195)
      ·
        refine ⟨3174976400486421563355293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2116650933657614375570195 3174976400486421563355293)
        ·
          refine ⟨1190616150182408086258235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3174976400486421563355293 1190616150182408086258235)
          ·
            refine ⟨1785924225273612129387353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190616150182408086258235 1785924225273612129387353)
            ·
              refine ⟨1339443168955209097040515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1785924225273612129387353 1339443168955209097040515)
              ·
                refine ⟨2009164753432813645560773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339443168955209097040515 2009164753432813645560773)
                ·
                  refine ⟨376718391268652558542645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2009164753432813645560773 376718391268652558542645)
                  ·
                    rfl

theorem cell21_1650727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 4].length) (baseStart_1650727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1650727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1650727 prefixEnd_1650727 := by exact prefixLift 1650727
  have htrace : WordTrace (prefixWord ++ tailWord_1650727) baseStart_1650727 baseEnd_1650727 := by
    simpa [prefixWord, tailWord_1650727, baseEnd_1650727] using wordTrace_append hprefix tailTrace_1650727
  have hstable : (prefixWord ++ tailWord_1650727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650727).length < 2 ^ (prefixWord ++ tailWord_1650727).sum := by decide
  have hdescent : baseEnd_1650727 < baseStart_1650727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650749 : List Nat := [1, 4, 1, 3, 1, 1, 1, 9]
def baseStart_1650749 : Nat := 118140960795 + 1650749 * 2 ^ 59
def prefixEnd_1650749 : Nat := 4983230072969 + 3 ^ 40 * 1650749 * 2
def baseEnd_1650749 : Nat := 125574470656128469725311

theorem tailTrace_1650749 : CollatzResearch.WordTrace tailWord_1650749 prefixEnd_1650749 125574470656128469725311 := by
  unfold tailWord_1650749
  simp only [CollatzResearch.WordTrace]
  refine ⟨60207762296625773329075301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40138508197750515552716867 60207762296625773329075301)
  ·
    refine ⟨11288955430617332499201619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60207762296625773329075301 11288955430617332499201619)
    ·
      refine ⟨16933433145925998748802429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11288955430617332499201619 16933433145925998748802429)
      ·
        refine ⟨6350037429722249530800911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16933433145925998748802429 6350037429722249530800911)
        ·
          refine ⟨9525056144583374296201367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6350037429722249530800911 9525056144583374296201367)
          ·
            refine ⟨14287584216875061444302051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9525056144583374296201367 14287584216875061444302051)
            ·
              refine ⟨21431376325312592166453077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14287584216875061444302051 21431376325312592166453077)
              ·
                refine ⟨125574470656128469725311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21431376325312592166453077 125574470656128469725311)
                ·
                  rfl

theorem cell21_1650749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 9].length) (baseStart_1650749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1650749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1650749 prefixEnd_1650749 := by exact prefixLift 1650749
  have htrace : WordTrace (prefixWord ++ tailWord_1650749) baseStart_1650749 baseEnd_1650749 := by
    simpa [prefixWord, tailWord_1650749, baseEnd_1650749] using wordTrace_append hprefix tailTrace_1650749
  have hstable : (prefixWord ++ tailWord_1650749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650749).length < 2 ^ (prefixWord ++ tailWord_1650749).sum := by decide
  have hdescent : baseEnd_1650749 < baseStart_1650749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650763 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 7]
def baseStart_1650763 : Nat := 118140960795 + 1650763 * 2 ^ 59
def prefixEnd_1650763 : Nat := 4983230072969 + 3 ^ 40 * 1650763 * 2
def baseEnd_1650763 : Nat := 376726606959124495942571

theorem tailTrace_1650763 : CollatzResearch.WordTrace tailWord_1650763 prefixEnd_1650763 376726606959124495942571 := by
  unfold tailWord_1650763
  simp only [CollatzResearch.WordTrace]
  refine ⟨60208272918575053720084943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40138848612383369146723295 60208272918575053720084943)
  ·
    refine ⟨90312409377862580580127415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60208272918575053720084943 90312409377862580580127415)
    ·
      refine ⟨135468614066793870870191123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90312409377862580580127415 135468614066793870870191123)
      ·
        refine ⟨203202921100190806305286685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135468614066793870870191123 203202921100190806305286685)
        ·
          refine ⟨76201095412571552364482507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203202921100190806305286685 76201095412571552364482507)
          ·
            refine ⟨114301643118857328546723761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76201095412571552364482507 114301643118857328546723761)
            ·
              refine ⟨85726232339142996410042821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114301643118857328546723761 85726232339142996410042821)
              ·
                refine ⟨16073668563589311826883029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85726232339142996410042821 16073668563589311826883029)
                ·
                  refine ⟨376726606959124495942571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16073668563589311826883029 376726606959124495942571)
                  ·
                    rfl

theorem cell21_1650763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 7].length) (baseStart_1650763 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1650763 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1650763 prefixEnd_1650763 := by exact prefixLift 1650763
  have htrace : WordTrace (prefixWord ++ tailWord_1650763) baseStart_1650763 baseEnd_1650763 := by
    simpa [prefixWord, tailWord_1650763, baseEnd_1650763] using wordTrace_append hprefix tailTrace_1650763
  have hstable : (prefixWord ++ tailWord_1650763).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650763).length < 2 ^ (prefixWord ++ tailWord_1650763).sum := by decide
  have hdescent : baseEnd_1650763 < baseStart_1650763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650890 : List Nat := [3, 1, 2, 1, 3, 1, 5, 2, 3]
def baseStart_1650890 : Nat := 118140960795 + 1650890 * 2 ^ 59
def prefixEnd_1650890 : Nat := 4983230072969 + 3 ^ 40 * 1650890 * 2
def baseEnd_1650890 : Nat := 376755590089400497325645

theorem tailTrace_1650890 : CollatzResearch.WordTrace tailWord_1650890 prefixEnd_1650890 376755590089400497325645 := by
  unfold tailWord_1650890
  simp only [CollatzResearch.WordTrace]
  refine ⟨15053226247278738602489531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40141936659409969606638749 15053226247278738602489531)
  ·
    refine ⟨22579839370918107903734297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15053226247278738602489531 22579839370918107903734297)
    ·
      refine ⟨16934879528188580927800723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22579839370918107903734297 16934879528188580927800723)
      ·
        refine ⟨25402319292282871391701085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16934879528188580927800723 25402319292282871391701085)
        ·
          refine ⟨9525869734606076771887907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25402319292282871391701085 9525869734606076771887907)
          ·
            refine ⟨14288804601909115157831861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9525869734606076771887907 14288804601909115157831861)
            ·
              refine ⟨1339575431428979546046737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14288804601909115157831861 1339575431428979546046737)
              ·
                refine ⟨1004681573571734659535053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1339575431428979546046737 1004681573571734659535053)
                ·
                  refine ⟨376755590089400497325645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1004681573571734659535053 376755590089400497325645)
                  ·
                    rfl

theorem cell21_1650890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2, 3].length) (baseStart_1650890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1650890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1650890 prefixEnd_1650890 := by exact prefixLift 1650890
  have htrace : WordTrace (prefixWord ++ tailWord_1650890) baseStart_1650890 baseEnd_1650890 := by
    simpa [prefixWord, tailWord_1650890, baseEnd_1650890] using wordTrace_append hprefix tailTrace_1650890
  have hstable : (prefixWord ++ tailWord_1650890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650890).length < 2 ^ (prefixWord ++ tailWord_1650890).sum := by decide
  have hdescent : baseEnd_1650890 < baseStart_1650890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650904 : List Nat := [2, 1, 2, 2, 4, 1, 4, 1, 4]
def baseStart_1650904 : Nat := 118140960795 + 1650904 * 2 ^ 59
def prefixEnd_1650904 : Nat := 4983230072969 + 3 ^ 40 * 1650904 * 2
def baseEnd_1650904 : Nat := 376758785080139584092283

theorem tailTrace_1650904 : CollatzResearch.WordTrace tailWord_1650904 prefixEnd_1650904 376758785080139584092283 := by
  unfold tailWord_1650904
  simp only [CollatzResearch.WordTrace]
  refine ⟨30106707805532117400483883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40142277074042823200645177 30106707805532117400483883)
  ·
    refine ⟨45160061708298176100725825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30106707805532117400483883 45160061708298176100725825)
    ·
      refine ⟨33870046281223632075544369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45160061708298176100725825 33870046281223632075544369)
      ·
        refine ⟨25402534710917724056658277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33870046281223632075544369 25402534710917724056658277)
        ·
          refine ⟨4762975258297073260623427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25402534710917724056658277 4762975258297073260623427)
          ·
            refine ⟨7144462887445609890935141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4762975258297073260623427 7144462887445609890935141)
            ·
              refine ⟨1339586791396051854550339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7144462887445609890935141 1339586791396051854550339)
              ·
                refine ⟨2009380187094077781825509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339586791396051854550339 2009380187094077781825509)
                ·
                  refine ⟨376758785080139584092283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2009380187094077781825509 376758785080139584092283)
                  ·
                    rfl

theorem cell21_1650904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 4].length) (baseStart_1650904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1650904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1650904 prefixEnd_1650904 := by exact prefixLift 1650904
  have htrace : WordTrace (prefixWord ++ tailWord_1650904) baseStart_1650904 baseEnd_1650904 := by
    simpa [prefixWord, tailWord_1650904, baseEnd_1650904] using wordTrace_append hprefix tailTrace_1650904
  have hstable : (prefixWord ++ tailWord_1650904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650904).length < 2 ^ (prefixWord ++ tailWord_1650904).sum := by decide
  have hdescent : baseEnd_1650904 < baseStart_1650904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651042 : List Nat := [3, 3, 2, 1, 1, 2, 3, 3, 3]
def baseStart_1651042 : Nat := 118140960795 + 1651042 * 2 ^ 59
def prefixEnd_1651042 : Nat := 4983230072969 + 3 ^ 40 * 1651042 * 2
def baseEnd_1651042 : Nat := 376790278560282010792001

theorem tailTrace_1651042 : CollatzResearch.WordTrace tailWord_1651042 prefixEnd_1651042 376790278560282010792001 := by
  unfold tailWord_1651042
  simp only [CollatzResearch.WordTrace]
  refine ⟨15054612221141071092372845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40145632589709522912994253 15054612221141071092372845)
  ·
    refine ⟨5645479582927901659639817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15054612221141071092372845 5645479582927901659639817)
    ·
      refine ⟨4234109687195926244729863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5645479582927901659639817 4234109687195926244729863)
      ·
        refine ⟨6351164530793889367094795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4234109687195926244729863 6351164530793889367094795)
        ·
          refine ⟨9526746796190834050642193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6351164530793889367094795 9526746796190834050642193)
          ·
            refine ⟨7145060097143125537981645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9526746796190834050642193 7145060097143125537981645)
            ·
              refine ⟨2679397536428672076743117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7145060097143125537981645 2679397536428672076743117)
              ·
                refine ⟨1004774076160752028778669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2679397536428672076743117 1004774076160752028778669)
                ·
                  refine ⟨376790278560282010792001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1004774076160752028778669 376790278560282010792001)
                  ·
                    rfl

theorem cell21_1651042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_1651042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1651042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1651042 prefixEnd_1651042 := by exact prefixLift 1651042
  have htrace : WordTrace (prefixWord ++ tailWord_1651042) baseStart_1651042 baseEnd_1651042 := by
    simpa [prefixWord, tailWord_1651042, baseEnd_1651042] using wordTrace_append hprefix tailTrace_1651042
  have hstable : (prefixWord ++ tailWord_1651042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651042).length < 2 ^ (prefixWord ++ tailWord_1651042).sum := by decide
  have hdescent : baseEnd_1651042 < baseStart_1651042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651073 : List Nat := [1, 2, 4, 3, 1, 3, 2, 1, 4]
def baseStart_1651073 : Nat := 118140960795 + 1651073 * 2 ^ 59
def prefixEnd_1651073 : Nat := 4983230072969 + 3 ^ 40 * 1651073 * 2
def baseEnd_1651073 : Nat := 376797353182632845775271

theorem tailTrace_1651073 : CollatzResearch.WordTrace tailWord_1651073 prefixEnd_1651073 376797353182632845775271 := by
  unfold tailWord_1651073
  simp only [CollatzResearch.WordTrace]
  refine ⟨60219579547451976663869873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40146386364967984442579915 60219579547451976663869873)
  ·
    refine ⟨45164684660588982497902405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60219579547451976663869873 45164684660588982497902405)
    ·
      refine ⟨8468378373860434218356701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45164684660588982497902405 8468378373860434218356701)
      ·
        refine ⟨3175641890197662831883763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8468378373860434218356701 3175641890197662831883763)
        ·
          refine ⟨4763462835296494247825645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3175641890197662831883763 4763462835296494247825645)
          ·
            refine ⟨1786298563236185342934617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4763462835296494247825645 1786298563236185342934617)
            ·
              refine ⟨1339723922427139007200963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1786298563236185342934617 1339723922427139007200963)
              ·
                refine ⟨2009585883640708510801445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339723922427139007200963 2009585883640708510801445)
                ·
                  refine ⟨376797353182632845775271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2009585883640708510801445 376797353182632845775271)
                  ·
                    rfl

theorem cell21_1651073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 4].length) (baseStart_1651073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1651073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1651073 prefixEnd_1651073 := by exact prefixLift 1651073
  have htrace : WordTrace (prefixWord ++ tailWord_1651073) baseStart_1651073 baseEnd_1651073 := by
    simpa [prefixWord, tailWord_1651073, baseEnd_1651073] using wordTrace_append hprefix tailTrace_1651073
  have hstable : (prefixWord ++ tailWord_1651073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651073).length < 2 ^ (prefixWord ++ tailWord_1651073).sum := by decide
  have hdescent : baseEnd_1651073 < baseStart_1651073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651129 : List Nat := [1, 2, 1, 4, 3, 1, 3, 6]
def baseStart_1651129 : Nat := 118140960795 + 1651129 * 2 ^ 59
def prefixEnd_1651129 : Nat := 4983230072969 + 3 ^ 40 * 1651129 * 2
def baseEnd_1651129 : Nat := 125603377715196397613941

theorem tailTrace_1651129 : CollatzResearch.WordTrace tailWord_1651129 prefixEnd_1651129 125603377715196397613941 := by
  unfold tailWord_1651129
  simp only [CollatzResearch.WordTrace]
  refine ⟨60221622035249098227908441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40147748023499398818605627 60221622035249098227908441)
  ·
    refine ⟨45166216526436823670931331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60221622035249098227908441 45166216526436823670931331)
    ·
      refine ⟨67749324789655235506396997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45166216526436823670931331 67749324789655235506396997)
      ·
        refine ⟨12702998398060356657449437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67749324789655235506396997 12702998398060356657449437)
        ·
          refine ⟨4763624399272633746543539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12702998398060356657449437 4763624399272633746543539)
          ·
            refine ⟨7145436598908950619815309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4763624399272633746543539 7145436598908950619815309)
            ·
              refine ⟨2679538724590856482430741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7145436598908950619815309 2679538724590856482430741)
              ·
                refine ⟨125603377715196397613941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2679538724590856482430741 125603377715196397613941)
                ·
                  rfl

theorem cell21_1651129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 6].length) (baseStart_1651129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1651129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1651129 prefixEnd_1651129 := by exact prefixLift 1651129
  have htrace : WordTrace (prefixWord ++ tailWord_1651129) baseStart_1651129 baseEnd_1651129 := by
    simpa [prefixWord, tailWord_1651129, baseEnd_1651129] using wordTrace_append hprefix tailTrace_1651129
  have hstable : (prefixWord ++ tailWord_1651129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651129).length < 2 ^ (prefixWord ++ tailWord_1651129).sum := by decide
  have hdescent : baseEnd_1651129 < baseStart_1651129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651143 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 7]
def baseStart_1651143 : Nat := 118140960795 + 1651143 * 2 ^ 59
def prefixEnd_1651143 : Nat := 4983230072969 + 3 ^ 40 * 1651143 * 2
def baseEnd_1651143 : Nat := 376813328136328279608461

theorem tailTrace_1651143 : CollatzResearch.WordTrace tailWord_1651143 prefixEnd_1651143 376813328136328279608461 := by
  unfold tailWord_1651143
  simp only [CollatzResearch.WordTrace]
  refine ⟨60222132657198378618918083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40148088438132252412612055 60222132657198378618918083)
  ·
    refine ⟨90333198985797567928377125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60222132657198378618918083 90333198985797567928377125)
    ·
      refine ⟨16937474809837043986570711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90333198985797567928377125 16937474809837043986570711)
      ·
        refine ⟨25406212214755565979856067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16937474809837043986570711 25406212214755565979856067)
        ·
          refine ⟨38109318322133348969784101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25406212214755565979856067 38109318322133348969784101)
          ·
            refine ⟨7145497185400002931834519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38109318322133348969784101 7145497185400002931834519)
            ·
              refine ⟨10718245778100004397751779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7145497185400002931834519 10718245778100004397751779)
              ·
                refine ⟨16077368667150006596627669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10718245778100004397751779 16077368667150006596627669)
                ·
                  refine ⟨376813328136328279608461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16077368667150006596627669 376813328136328279608461)
                  ·
                    rfl

theorem cell21_1651143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 7].length) (baseStart_1651143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1651143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1651143 prefixEnd_1651143 := by exact prefixLift 1651143
  have htrace : WordTrace (prefixWord ++ tailWord_1651143) baseStart_1651143 baseEnd_1651143 := by
    simpa [prefixWord, tailWord_1651143, baseEnd_1651143] using wordTrace_append hprefix tailTrace_1651143
  have hstable : (prefixWord ++ tailWord_1651143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651143).length < 2 ^ (prefixWord ++ tailWord_1651143).sum := by decide
  have hdescent : baseEnd_1651143 < baseStart_1651143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651205 : List Nat := [1, 3, 1, 1, 2, 2, 6, 5]
def baseStart_1651205 : Nat := 118140960795 + 1651205 * 2 ^ 59
def prefixEnd_1651205 : Nat := 4983230072969 + 3 ^ 40 * 1651205 * 2
def baseEnd_1651205 : Nat := 125609159127009983191667

theorem tailTrace_1651205 : CollatzResearch.WordTrace tailWord_1651205 prefixEnd_1651205 125609159127009983191667 := by
  unfold tailWord_1651205
  simp only [CollatzResearch.WordTrace]
  refine ⟨60224393982973763207675069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40149595988649175471783379 60224393982973763207675069)
  ·
    refine ⟨22584147743615161202878151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60224393982973763207675069 22584147743615161202878151)
    ·
      refine ⟨33876221615422741804317227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22584147743615161202878151 33876221615422741804317227)
      ·
        refine ⟨50814332423134112706475841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33876221615422741804317227 50814332423134112706475841)
        ·
          refine ⟨38110749317350584529856881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50814332423134112706475841 38110749317350584529856881)
          ·
            refine ⟨28583061988012938397392661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38110749317350584529856881 28583061988012938397392661)
            ·
              refine ⟨1339831030688106487377781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28583061988012938397392661 1339831030688106487377781)
              ·
                refine ⟨125609159127009983191667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1339831030688106487377781 125609159127009983191667)
                ·
                  rfl

theorem cell21_1651205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 5].length) (baseStart_1651205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1651205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1651205 prefixEnd_1651205 := by exact prefixLift 1651205
  have htrace : WordTrace (prefixWord ++ tailWord_1651205) baseStart_1651205 baseEnd_1651205 := by
    simpa [prefixWord, tailWord_1651205, baseEnd_1651205] using wordTrace_append hprefix tailTrace_1651205
  have hstable : (prefixWord ++ tailWord_1651205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651205).length < 2 ^ (prefixWord ++ tailWord_1651205).sum := by decide
  have hdescent : baseEnd_1651205 < baseStart_1651205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651239 : List Nat := [1, 1, 7, 2, 1, 1, 2, 6]
def baseStart_1651239 : Nat := 118140960795 + 1651239 * 2 ^ 59
def prefixEnd_1651239 : Nat := 4983230072969 + 3 ^ 40 * 1651239 * 2
def baseEnd_1651239 : Nat := 125611745548084482002755

theorem tailTrace_1651239 : CollatzResearch.WordTrace tailWord_1651239 prefixEnd_1651239 125611745548084482002755 := by
  unfold tailWord_1651239
  simp only [CollatzResearch.WordTrace]
  refine ⟨60225634064850587014412771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40150422709900391342941847 60225634064850587014412771)
  ·
    refine ⟨90338451097275880521619157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60225634064850587014412771 90338451097275880521619157)
    ·
      refine ⟨2117307447592403449725449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 90338451097275880521619157 2117307447592403449725449)
      ·
        refine ⟨1587980585694302587294087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2117307447592403449725449 1587980585694302587294087)
        ·
          refine ⟨2381970878541453880941131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1587980585694302587294087 2381970878541453880941131)
          ·
            refine ⟨3572956317812180821411697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2381970878541453880941131 3572956317812180821411697)
            ·
              refine ⟨2679717238359135616058773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3572956317812180821411697 2679717238359135616058773)
              ·
                refine ⟨125611745548084482002755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2679717238359135616058773 125611745548084482002755)
                ·
                  rfl

theorem cell21_1651239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 6].length) (baseStart_1651239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1651239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1651239 prefixEnd_1651239 := by exact prefixLift 1651239
  have htrace : WordTrace (prefixWord ++ tailWord_1651239) baseStart_1651239 baseEnd_1651239 := by
    simpa [prefixWord, tailWord_1651239, baseEnd_1651239] using wordTrace_append hprefix tailTrace_1651239
  have hstable : (prefixWord ++ tailWord_1651239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651239).length < 2 ^ (prefixWord ++ tailWord_1651239).sum := by decide
  have hdescent : baseEnd_1651239 < baseStart_1651239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651264 : List Nat := [2, 1, 1, 2, 2, 2, 4, 7]
def baseStart_1651264 : Nat := 118140960795 + 1651264 * 2 ^ 59
def prefixEnd_1651264 : Nat := 4983230072969 + 3 ^ 40 * 1651264 * 2
def baseEnd_1651264 : Nat := 125613647328286319363849

theorem tailTrace_1651264 : CollatzResearch.WordTrace tailWord_1651264 prefixEnd_1651264 125613647328286319363849 := by
  unfold tailWord_1651264
  simp only [CollatzResearch.WordTrace]
  refine ⟨30113272944880008142036423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40151030593173344189381897 30113272944880008142036423)
  ·
    refine ⟨45169909417320012213054635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30113272944880008142036423 45169909417320012213054635)
    ·
      refine ⟨67754864125980018319581953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45169909417320012213054635 67754864125980018319581953)
      ·
        refine ⟨50816148094485013739686465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67754864125980018319581953 50816148094485013739686465)
        ·
          refine ⟨38112111070863760304764849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50816148094485013739686465 38112111070863760304764849)
          ·
            refine ⟨28584083303147820228573637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38112111070863760304764849 28584083303147820228573637)
            ·
              refine ⟨5359515619340216292857557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28584083303147820228573637 5359515619340216292857557)
              ·
                refine ⟨125613647328286319363849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5359515619340216292857557 125613647328286319363849)
                ·
                  rfl

theorem cell21_1651264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 7].length) (baseStart_1651264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1651264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1651264 prefixEnd_1651264 := by exact prefixLift 1651264
  have htrace : WordTrace (prefixWord ++ tailWord_1651264) baseStart_1651264 baseEnd_1651264 := by
    simpa [prefixWord, tailWord_1651264, baseEnd_1651264] using wordTrace_append hprefix tailTrace_1651264
  have hstable : (prefixWord ++ tailWord_1651264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651264).length < 2 ^ (prefixWord ++ tailWord_1651264).sum := by decide
  have hdescent : baseEnd_1651264 < baseStart_1651264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651312 : List Nat := [2, 1, 1, 1, 7, 1, 1, 2, 5]
def baseStart_1651312 : Nat := 118140960795 + 1651312 * 2 ^ 59
def prefixEnd_1651312 : Nat := 4983230072969 + 3 ^ 40 * 1651312 * 2
def baseEnd_1651312 : Nat := 376851896238821541291449

theorem tailTrace_1651312 : CollatzResearch.WordTrace tailWord_1651312 prefixEnd_1651312 376851896238821541291449 := by
  unfold tailWord_1651312
  simp only [CollatzResearch.WordTrace]
  refine ⟨30114148296793060240910095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40152197729057413654546793 30114148296793060240910095)
  ·
    refine ⟨45171222445189590361365143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30114148296793060240910095 45171222445189590361365143)
    ·
      refine ⟨67756833667784385542047715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45171222445189590361365143 67756833667784385542047715)
      ·
        refine ⟨101635250501676578313071573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67756833667784385542047715 101635250501676578313071573)
        ·
          refine ⟨2382076183633044804212615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 101635250501676578313071573 2382076183633044804212615)
          ·
            refine ⟨3573114275449567206318923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2382076183633044804212615 3573114275449567206318923)
            ·
              refine ⟨5359671413174350809478385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3573114275449567206318923 5359671413174350809478385)
              ·
                refine ⟨4019753559880763107108789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5359671413174350809478385 4019753559880763107108789)
                ·
                  refine ⟨376851896238821541291449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4019753559880763107108789 376851896238821541291449)
                  ·
                    rfl

theorem cell21_1651312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 5].length) (baseStart_1651312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1651312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1651312 prefixEnd_1651312 := by exact prefixLift 1651312
  have htrace : WordTrace (prefixWord ++ tailWord_1651312) baseStart_1651312 baseEnd_1651312 := by
    simpa [prefixWord, tailWord_1651312, baseEnd_1651312] using wordTrace_append hprefix tailTrace_1651312
  have hstable : (prefixWord ++ tailWord_1651312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651312).length < 2 ^ (prefixWord ++ tailWord_1651312).sum := by decide
  have hdescent : baseEnd_1651312 < baseStart_1651312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651329 : List Nat := [1, 2, 4, 2, 1, 1, 4, 3, 3]
def baseStart_1651329 : Nat := 118140960795 + 1651329 * 2 ^ 59
def prefixEnd_1651329 : Nat := 4983230072969 + 3 ^ 40 * 1651329 * 2
def baseEnd_1651329 : Nat := 376855775870433289508081

theorem tailTrace_1651329 : CollatzResearch.WordTrace tailWord_1651329 prefixEnd_1651329 376855775870433289508081 := by
  unfold tailWord_1651329
  simp only [CollatzResearch.WordTrace]
  refine ⟨60228916634524532385189041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40152611089683021590126027 60228916634524532385189041)
  ·
    refine ⟨45171687475893399288891781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60228916634524532385189041 45171687475893399288891781)
    ·
      refine ⟨8469691401730012366667209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45171687475893399288891781 8469691401730012366667209)
      ·
        refine ⟨6352268551297509275000407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8469691401730012366667209 6352268551297509275000407)
        ·
          refine ⟨9528402826946263912500611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6352268551297509275000407 9528402826946263912500611)
          ·
            refine ⟨14292604240419395868750917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9528402826946263912500611 14292604240419395868750917)
            ·
              refine ⟨2679863295078636725390797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14292604240419395868750917 2679863295078636725390797)
              ·
                refine ⟨1004948735654488772021549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2679863295078636725390797 1004948735654488772021549)
                ·
                  refine ⟨376855775870433289508081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1004948735654488772021549 376855775870433289508081)
                  ·
                    rfl

theorem cell21_1651329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3, 3].length) (baseStart_1651329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1651329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1651329 prefixEnd_1651329 := by exact prefixLift 1651329
  have htrace : WordTrace (prefixWord ++ tailWord_1651329) baseStart_1651329 baseEnd_1651329 := by
    simpa [prefixWord, tailWord_1651329, baseEnd_1651329] using wordTrace_append hprefix tailTrace_1651329
  have hstable : (prefixWord ++ tailWord_1651329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651329).length < 2 ^ (prefixWord ++ tailWord_1651329).sum := by decide
  have hdescent : baseEnd_1651329 < baseStart_1651329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651360 : List Nat := [2, 1, 1, 4, 4, 1, 3, 1, 4]
def baseStart_1651360 : Nat := 118140960795 + 1651360 * 2 ^ 59
def prefixEnd_1651360 : Nat := 4983230072969 + 3 ^ 40 * 1651360 * 2
def baseEnd_1651360 : Nat := 376862850492784124491351

theorem tailTrace_1651360 : CollatzResearch.WordTrace tailWord_1651360 prefixEnd_1651360 376862850492784124491351 := by
  unfold tailWord_1651360
  simp only [CollatzResearch.WordTrace]
  refine ⟨30115023648706112339783767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40153364864941483119711689 30115023648706112339783767)
  ·
    refine ⟨45172535473059168509675651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30115023648706112339783767 45172535473059168509675651)
    ·
      refine ⟨67758803209588752764513477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45172535473059168509675651 67758803209588752764513477)
      ·
        refine ⟨12704775601797891143346277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67758803209588752764513477 12704775601797891143346277)
        ·
          refine ⟨2382145425337104589377427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12704775601797891143346277 2382145425337104589377427)
          ·
            refine ⟨3573218138005656884066141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2382145425337104589377427 3573218138005656884066141)
            ·
              refine ⟨1339956801752121331524803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3573218138005656884066141 1339956801752121331524803)
              ·
                refine ⟨2009935202628181997287205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339956801752121331524803 2009935202628181997287205)
                ·
                  refine ⟨376862850492784124491351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2009935202628181997287205 376862850492784124491351)
                  ·
                    rfl

theorem cell21_1651360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 4].length) (baseStart_1651360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1651360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1651360 prefixEnd_1651360 := by exact prefixLift 1651360
  have htrace : WordTrace (prefixWord ++ tailWord_1651360) baseStart_1651360 baseEnd_1651360 := by
    simpa [prefixWord, tailWord_1651360, baseEnd_1651360] using wordTrace_append hprefix tailTrace_1651360
  have hstable : (prefixWord ++ tailWord_1651360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651360).length < 2 ^ (prefixWord ++ tailWord_1651360).sum := by decide
  have hdescent : baseEnd_1651360 < baseStart_1651360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651374 : List Nat := [4, 1, 4, 1, 1, 2, 1, 7]
def baseStart_1651374 : Nat := 118140960795 + 1651374 * 2 ^ 59
def prefixEnd_1651374 : Nat := 4983230072969 + 3 ^ 40 * 1651374 * 2
def baseEnd_1651374 : Nat := 125622015161174403752663

theorem tailTrace_1651374 : CollatzResearch.WordTrace tailWord_1651374 prefixEnd_1651374 125622015161174403752663 := by
  unfold tailWord_1651374
  simp only [CollatzResearch.WordTrace]
  refine ⟨7528819739920188133822147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40153705279574336713718117 7528819739920188133822147)
  ·
    refine ⟨11293229609880282200733221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7528819739920188133822147 11293229609880282200733221)
    ·
      refine ⟨2117480551852552912637479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11293229609880282200733221 2117480551852552912637479)
      ·
        refine ⟨3176220827778829368956219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2117480551852552912637479 3176220827778829368956219)
        ·
          refine ⟨4764331241668244053434329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3176220827778829368956219 4764331241668244053434329)
          ·
            refine ⟨3573248431251183040075747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4764331241668244053434329 3573248431251183040075747)
            ·
              refine ⟨5359872646876774560113621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3573248431251183040075747 5359872646876774560113621)
              ·
                refine ⟨125622015161174403752663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5359872646876774560113621 125622015161174403752663)
                ·
                  rfl

theorem cell21_1651374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_1651374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1651374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1651374 prefixEnd_1651374 := by exact prefixLift 1651374
  have htrace : WordTrace (prefixWord ++ tailWord_1651374) baseStart_1651374 baseEnd_1651374 := by
    simpa [prefixWord, tailWord_1651374, baseEnd_1651374] using wordTrace_append hprefix tailTrace_1651374
  have hstable : (prefixWord ++ tailWord_1651374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651374).length < 2 ^ (prefixWord ++ tailWord_1651374).sum := by decide
  have hdescent : baseEnd_1651374 < baseStart_1651374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651402 : List Nat := [3, 1, 2, 1, 4, 1, 2, 1, 6]
def baseStart_1651402 : Nat := 118140960795 + 1651402 * 2 ^ 59
def prefixEnd_1651402 : Nat := 4983230072969 + 3 ^ 40 * 1651402 * 2
def baseEnd_1651402 : Nat := 376872435465001384791265

theorem tailTrace_1651402 : CollatzResearch.WordTrace tailWord_1651402 prefixEnd_1651402 376872435465001384791265 := by
  unfold tailWord_1651402
  simp only [CollatzResearch.WordTrace]
  refine ⟨15057894790815016463149115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40154386108840043901730973 15057894790815016463149115)
  ·
    refine ⟨22586842186222524694723673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15057894790815016463149115 22586842186222524694723673)
    ·
      refine ⟨16940131639666893521042755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22586842186222524694723673 16940131639666893521042755)
      ·
        refine ⟨25410197459500340281564133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16940131639666893521042755 25410197459500340281564133)
        ·
          refine ⟨4764412023656313802793275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25410197459500340281564133 4764412023656313802793275)
          ·
            refine ⟨7146618035484470704189913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4764412023656313802793275 7146618035484470704189913)
            ·
              refine ⟨5359963526613353028142435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7146618035484470704189913 5359963526613353028142435)
              ·
                refine ⟨8039945289920029542213653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5359963526613353028142435 8039945289920029542213653)
                ·
                  refine ⟨376872435465001384791265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8039945289920029542213653 376872435465001384791265)
                  ·
                    rfl

theorem cell21_1651402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_1651402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1651402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1651402 prefixEnd_1651402 := by exact prefixLift 1651402
  have htrace : WordTrace (prefixWord ++ tailWord_1651402) baseStart_1651402 baseEnd_1651402 := by
    simpa [prefixWord, tailWord_1651402, baseEnd_1651402] using wordTrace_append hprefix tailTrace_1651402
  have hstable : (prefixWord ++ tailWord_1651402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651402).length < 2 ^ (prefixWord ++ tailWord_1651402).sum := by decide
  have hdescent : baseEnd_1651402 < baseStart_1651402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651416 : List Nat := [2, 1, 2, 2, 3, 2, 1, 8]
def baseStart_1651416 : Nat := 118140960795 + 1651416 * 2 ^ 59
def prefixEnd_1651416 : Nat := 4983230072969 + 3 ^ 40 * 1651416 * 2
def baseEnd_1651416 : Nat := 125625210151913490519301

theorem tailTrace_1651416 : CollatzResearch.WordTrace tailWord_1651416 prefixEnd_1651416 125625210151913490519301 := by
  unfold tailWord_1651416
  simp only [CollatzResearch.WordTrace]
  refine ⟨30116044892604673121803051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40154726523472897495737401 30116044892604673121803051)
  ·
    refine ⟨45174067338907009682704577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30116044892604673121803051 45174067338907009682704577)
    ·
      refine ⟨33880550504180257262028433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45174067338907009682704577 33880550504180257262028433)
      ·
        refine ⟨25410412878135192946521325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33880550504180257262028433 25410412878135192946521325)
        ·
          refine ⟨9528904829300697354945497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25410412878135192946521325 9528904829300697354945497)
          ·
            refine ⟨7146678621975523016209123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9528904829300697354945497 7146678621975523016209123)
            ·
              refine ⟨10720017932963284524313685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7146678621975523016209123 10720017932963284524313685)
              ·
                refine ⟨125625210151913490519301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10720017932963284524313685 125625210151913490519301)
                ·
                  rfl

theorem cell21_1651416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 8].length) (baseStart_1651416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1651416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1651416 prefixEnd_1651416 := by exact prefixLift 1651416
  have htrace : WordTrace (prefixWord ++ tailWord_1651416) baseStart_1651416 baseEnd_1651416 := by
    simpa [prefixWord, tailWord_1651416, baseEnd_1651416] using wordTrace_append hprefix tailTrace_1651416
  have hstable : (prefixWord ++ tailWord_1651416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651416).length < 2 ^ (prefixWord ++ tailWord_1651416).sum := by decide
  have hdescent : baseEnd_1651416 < baseStart_1651416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651461 : List Nat := [1, 3, 1, 1, 2, 1, 1, 5, 6]
def baseStart_1651461 : Nat := 118140960795 + 1651461 * 2 ^ 59
def prefixEnd_1651461 : Nat := 4983230072969 + 3 ^ 40 * 1651461 * 2
def baseEnd_1651461 : Nat := 376885900068830393307811

theorem tailTrace_1651461 : CollatzResearch.WordTrace tailWord_1651461 prefixEnd_1651461 376885900068830393307811 := by
  unfold tailWord_1651461
  simp only [CollatzResearch.WordTrace]
  refine ⟨60233731070046318928994237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40155820713364212619329491 60233731070046318928994237)
  ·
    refine ⟨22587649151267369598372839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60233731070046318928994237 22587649151267369598372839)
    ·
      refine ⟨33881473726901054397559259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22587649151267369598372839 33881473726901054397559259)
      ·
        refine ⟨50822210590351581596338889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33881473726901054397559259 50822210590351581596338889)
        ·
          refine ⟨38116657942763686197254167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50822210590351581596338889 38116657942763686197254167)
          ·
            refine ⟨57174986914145529295881251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38116657942763686197254167 57174986914145529295881251)
            ·
              refine ⟨85762480371218293943821877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57174986914145529295881251 85762480371218293943821877)
              ·
                refine ⟨8040232534801715057233301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85762480371218293943821877 8040232534801715057233301)
                ·
                  refine ⟨376885900068830393307811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8040232534801715057233301 376885900068830393307811)
                  ·
                    rfl

theorem cell21_1651461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_1651461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1651461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1651461 prefixEnd_1651461 := by exact prefixLift 1651461
  have htrace : WordTrace (prefixWord ++ tailWord_1651461) baseStart_1651461 baseEnd_1651461 := by
    simpa [prefixWord, tailWord_1651461, baseEnd_1651461] using wordTrace_append hprefix tailTrace_1651461
  have hstable : (prefixWord ++ tailWord_1651461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651461).length < 2 ^ (prefixWord ++ tailWord_1651461).sum := by decide
  have hdescent : baseEnd_1651461 < baseStart_1651461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651523 : List Nat := [1, 1, 1, 3, 1, 4, 4, 1, 5]
def baseStart_1651523 : Nat := 118140960795 + 1651523 * 2 ^ 59
def prefixEnd_1651523 : Nat := 4983230072969 + 3 ^ 40 * 1651523 * 2
def baseEnd_1651523 : Nat := 376900049313532063274351

theorem tailTrace_1651523 : CollatzResearch.WordTrace tailWord_1651523 prefixEnd_1651523 376900049313532063274351 := by
  unfold tailWord_1651523
  simp only [CollatzResearch.WordTrace]
  refine ⟨60235992395821703517751223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40157328263881135678500815 60235992395821703517751223)
  ·
    refine ⟨90353988593732555276626835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60235992395821703517751223 90353988593732555276626835)
    ·
      refine ⟨135530982890598832914940253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90353988593732555276626835 135530982890598832914940253)
      ·
        refine ⟨50824118583974562343102595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135530982890598832914940253 50824118583974562343102595)
        ·
          refine ⟨76236177875961843514653893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50824118583974562343102595 76236177875961843514653893)
          ·
            refine ⟨14294283351742845658997605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76236177875961843514653893 14294283351742845658997605)
            ·
              refine ⟨2680178128451783561062051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14294283351742845658997605 2680178128451783561062051)
              ·
                refine ⟨4020267192677675341593077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2680178128451783561062051 4020267192677675341593077)
                ·
                  refine ⟨376900049313532063274351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4020267192677675341593077 376900049313532063274351)
                  ·
                    rfl

theorem cell21_1651523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 5].length) (baseStart_1651523 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1651523 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1651523 prefixEnd_1651523 := by exact prefixLift 1651523
  have htrace : WordTrace (prefixWord ++ tailWord_1651523) baseStart_1651523 baseEnd_1651523 := by
    simpa [prefixWord, tailWord_1651523, baseEnd_1651523] using wordTrace_append hprefix tailTrace_1651523
  have hstable : (prefixWord ++ tailWord_1651523).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651523).length < 2 ^ (prefixWord ++ tailWord_1651523).sum := by decide
  have hdescent : baseEnd_1651523 < baseStart_1651523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651633 : List Nat := [1, 2, 2, 4, 3, 1, 1, 4, 3]
def baseStart_1651633 : Nat := 118140960795 + 1651633 * 2 ^ 59
def prefixEnd_1651633 : Nat := 4983230072969 + 3 ^ 40 * 1651633 * 2
def baseEnd_1651633 : Nat := 376925152812196316440793

theorem tailTrace_1651633 : CollatzResearch.WordTrace tailWord_1651633 prefixEnd_1651633 376925152812196316440793 := by
  unfold tailWord_1651633
  simp only [CollatzResearch.WordTrace]
  refine ⟨60240004425423192304255553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40160002950282128202837035 60240004425423192304255553)
  ·
    refine ⟨45180003319067394228191665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60240004425423192304255553 45180003319067394228191665)
    ·
      refine ⟨33885002489300545671143749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45180003319067394228191665 33885002489300545671143749)
      ·
        refine ⟨6353437966743852313339453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33885002489300545671143749 6353437966743852313339453)
        ·
          refine ⟨2382539237528944617502295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6353437966743852313339453 2382539237528944617502295)
          ·
            refine ⟨3573808856293416926253443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2382539237528944617502295 3573808856293416926253443)
            ·
              refine ⟨5360713284440125389380165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3573808856293416926253443 5360713284440125389380165)
              ·
                refine ⟨1005133740832523510508781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5360713284440125389380165 1005133740832523510508781)
                ·
                  refine ⟨376925152812196316440793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1005133740832523510508781 376925152812196316440793)
                  ·
                    rfl

theorem cell21_1651633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4, 3].length) (baseStart_1651633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1651633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1651633 prefixEnd_1651633 := by exact prefixLift 1651633
  have htrace : WordTrace (prefixWord ++ tailWord_1651633) baseStart_1651633 baseEnd_1651633 := by
    simpa [prefixWord, tailWord_1651633, baseEnd_1651633] using wordTrace_append hprefix tailTrace_1651633
  have hstable : (prefixWord ++ tailWord_1651633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651633).length < 2 ^ (prefixWord ++ tailWord_1651633).sum := by decide
  have hdescent : baseEnd_1651633 < baseStart_1651633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651720 : List Nat := [2, 1, 3, 2, 1, 4, 1, 7]
def baseStart_1651720 : Nat := 118140960795 + 1651720 * 2 ^ 59
def prefixEnd_1651720 : Nat := 4983230072969 + 3 ^ 40 * 1651720 * 2
def baseEnd_1651720 : Nat := 125648335799167832830205

theorem tailTrace_1651720 : CollatzResearch.WordTrace tailWord_1651720 prefixEnd_1651720 125648335799167832830205 := by
  unfold tailWord_1651720
  simp only [CollatzResearch.WordTrace]
  refine ⟨30121588788054003081336307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40162118384072004108448409 30121588788054003081336307)
  ·
    refine ⟨45182383182081004622004461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30121588788054003081336307 45182383182081004622004461)
    ·
      refine ⟨16943393693280376733251673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45182383182081004622004461 16943393693280376733251673)
      ·
        refine ⟨12707545269960282549938755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16943393693280376733251673 12707545269960282549938755)
        ·
          refine ⟨19061317904940423824908133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12707545269960282549938755 19061317904940423824908133)
          ·
            refine ⟨3573997107176329467170275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19061317904940423824908133 3573997107176329467170275)
            ·
              refine ⟨5360995660764494200755413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3573997107176329467170275 5360995660764494200755413)
              ·
                refine ⟨125648335799167832830205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5360995660764494200755413 125648335799167832830205)
                ·
                  rfl

theorem cell21_1651720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 7].length) (baseStart_1651720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1651720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1651720 prefixEnd_1651720 := by exact prefixLift 1651720
  have htrace : WordTrace (prefixWord ++ tailWord_1651720) baseStart_1651720 baseEnd_1651720 := by
    simpa [prefixWord, tailWord_1651720, baseEnd_1651720] using wordTrace_append hprefix tailTrace_1651720
  have hstable : (prefixWord ++ tailWord_1651720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651720).length < 2 ^ (prefixWord ++ tailWord_1651720).sum := by decide
  have hdescent : baseEnd_1651720 < baseStart_1651720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651779 : List Nat := [1, 1, 1, 3, 1, 2, 3, 9]
def baseStart_1651779 : Nat := 118140960795 + 1651779 * 2 ^ 59
def prefixEnd_1651779 : Nat := 4983230072969 + 3 ^ 40 * 1651779 * 2
def baseEnd_1651779 : Nat := 125652824000444169002387

theorem tailTrace_1651779 : CollatzResearch.WordTrace tailWord_1651779 prefixEnd_1651779 125652824000444169002387 := by
  unfold tailWord_1651779
  simp only [CollatzResearch.WordTrace]
  refine ⟨60245329482894259239070391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40163552988596172826046927 60245329482894259239070391)
  ·
    refine ⟨90367994224341388858605587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60245329482894259239070391 90367994224341388858605587)
    ·
      refine ⟨135551991336512083287908381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90367994224341388858605587 135551991336512083287908381)
      ·
        refine ⟨50831996751192031232965643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135551991336512083287908381 50831996751192031232965643)
        ·
          refine ⟨76247995126788046849448465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50831996751192031232965643 76247995126788046849448465)
          ·
            refine ⟨57185996345091035137086349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76247995126788046849448465 57185996345091035137086349)
            ·
              refine ⟨21444748629409138176407381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57185996345091035137086349 21444748629409138176407381)
              ·
                refine ⟨125652824000444169002387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21444748629409138176407381 125652824000444169002387)
                ·
                  rfl

theorem cell21_1651779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 9].length) (baseStart_1651779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1651779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1651779 prefixEnd_1651779 := by exact prefixLift 1651779
  have htrace : WordTrace (prefixWord ++ tailWord_1651779) baseStart_1651779 baseEnd_1651779 := by
    simpa [prefixWord, tailWord_1651779, baseEnd_1651779] using wordTrace_append hprefix tailTrace_1651779
  have hstable : (prefixWord ++ tailWord_1651779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651779).length < 2 ^ (prefixWord ++ tailWord_1651779).sum := by decide
  have hdescent : baseEnd_1651779 < baseStart_1651779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651844 : List Nat := [2, 3, 2, 1, 2, 2, 1, 5, 3]
def baseStart_1651844 : Nat := 118140960795 + 1651844 * 2 ^ 59
def prefixEnd_1651844 : Nat := 4983230072969 + 3 ^ 40 * 1651844 * 2
def baseEnd_1651844 : Nat := 376973305886906838423695

theorem tailTrace_1651844 : CollatzResearch.WordTrace tailWord_1651844 prefixEnd_1651844 376973305886906838423695 := by
  unfold tailWord_1651844
  simp only [CollatzResearch.WordTrace]
  refine ⟨30123850113829387670093293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40165133485105850226791057 30123850113829387670093293)
  ·
    refine ⟨11296443792686020376284985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30123850113829387670093293 11296443792686020376284985)
    ·
      refine ⟨8472332844514515282213739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11296443792686020376284985 8472332844514515282213739)
      ·
        refine ⟨12708499266771772923320609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8472332844514515282213739 12708499266771772923320609)
        ·
          refine ⟨9531374450078829692490457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12708499266771772923320609 9531374450078829692490457)
          ·
            refine ⟨7148530837559122269367843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9531374450078829692490457 7148530837559122269367843)
            ·
              refine ⟨10722796256338683404051765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7148530837559122269367843 10722796256338683404051765)
              ·
                refine ⟨1005262149031751569129853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10722796256338683404051765 1005262149031751569129853)
                ·
                  refine ⟨376973305886906838423695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1005262149031751569129853 376973305886906838423695)
                  ·
                    rfl

theorem cell21_1651844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_1651844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1651844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1651844 prefixEnd_1651844 := by exact prefixLift 1651844
  have htrace : WordTrace (prefixWord ++ tailWord_1651844) baseStart_1651844 baseEnd_1651844 := by
    simpa [prefixWord, tailWord_1651844, baseEnd_1651844] using wordTrace_append hprefix tailTrace_1651844
  have hstable : (prefixWord ++ tailWord_1651844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651844).length < 2 ^ (prefixWord ++ tailWord_1651844).sum := by decide
  have hdescent : baseEnd_1651844 < baseStart_1651844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651858 : List Nat := [3, 2, 3, 1, 1, 3, 1, 1, 6]
def baseStart_1651858 : Nat := 118140960795 + 1651858 * 2 ^ 59
def prefixEnd_1651858 : Nat := 4983230072969 + 3 ^ 40 * 1651858 * 2
def baseEnd_1651858 : Nat := 376976500877645925190333

theorem tailTrace_1651858 : CollatzResearch.WordTrace tailWord_1651858 prefixEnd_1651858 376976500877645925190333 := by
  unfold tailWord_1651858
  simp only [CollatzResearch.WordTrace]
  refine ⟨15062052712402013932799057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40165473899738703820797485 15062052712402013932799057)
  ·
    refine ⟨11296539534301510449599293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15062052712402013932799057 11296539534301510449599293)
    ·
      refine ⟨4236202325363066418599735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11296539534301510449599293 4236202325363066418599735)
      ·
        refine ⟨6354303488044599627899603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4236202325363066418599735 6354303488044599627899603)
        ·
          refine ⟨9531455232066899441849405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6354303488044599627899603 9531455232066899441849405)
          ·
            refine ⟨3574295712025087290693527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9531455232066899441849405 3574295712025087290693527)
            ·
              refine ⟨5361443568037630936040291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3574295712025087290693527 5361443568037630936040291)
              ·
                refine ⟨8042165352056446404060437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5361443568037630936040291 8042165352056446404060437)
                ·
                  refine ⟨376976500877645925190333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8042165352056446404060437 376976500877645925190333)
                  ·
                    rfl

theorem cell21_1651858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_1651858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1651858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1651858 prefixEnd_1651858 := by exact prefixLift 1651858
  have htrace : WordTrace (prefixWord ++ tailWord_1651858) baseStart_1651858 baseEnd_1651858 := by
    simpa [prefixWord, tailWord_1651858, baseEnd_1651858] using wordTrace_append hprefix tailTrace_1651858
  have hstable : (prefixWord ++ tailWord_1651858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651858).length < 2 ^ (prefixWord ++ tailWord_1651858).sum := by decide
  have hdescent : baseEnd_1651858 < baseStart_1651858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651889 : List Nat := [1, 2, 2, 5, 1, 1, 4, 5]
def baseStart_1651889 : Nat := 118140960795 + 1651889 * 2 ^ 59
def prefixEnd_1651889 : Nat := 4983230072969 + 3 ^ 40 * 1651889 * 2
def baseEnd_1651889 : Nat := 125661191833332253391201

theorem tailTrace_1651889 : CollatzResearch.WordTrace tailWord_1651889 prefixEnd_1651889 125661191833332253391201 := by
  unfold tailWord_1651889
  simp only [CollatzResearch.WordTrace]
  refine ⟨60249341512495748025574721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40166227674997165350383147 60249341512495748025574721)
  ·
    refine ⟨45187006134371811019181041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60249341512495748025574721 45187006134371811019181041)
    ·
      refine ⟨33890254600778858264385781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45187006134371811019181041 33890254600778858264385781)
      ·
        refine ⟨3177211368823017962286167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33890254600778858264385781 3177211368823017962286167)
        ·
          refine ⟨4765817053234526943429251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3177211368823017962286167 4765817053234526943429251)
          ·
            refine ⟨7148725579851790415143877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4765817053234526943429251 7148725579851790415143877)
            ·
              refine ⟨1340386046222210702839477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7148725579851790415143877 1340386046222210702839477)
              ·
                refine ⟨125661191833332253391201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1340386046222210702839477 125661191833332253391201)
                ·
                  rfl

theorem cell21_1651889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 5].length) (baseStart_1651889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1651889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1651889 prefixEnd_1651889 := by exact prefixLift 1651889
  have htrace : WordTrace (prefixWord ++ tailWord_1651889) baseStart_1651889 baseEnd_1651889 := by
    simpa [prefixWord, tailWord_1651889, baseEnd_1651889] using wordTrace_append hprefix tailTrace_1651889
  have hstable : (prefixWord ++ tailWord_1651889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651889).length < 2 ^ (prefixWord ++ tailWord_1651889).sum := by decide
  have hdescent : baseEnd_1651889 < baseStart_1651889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651926 : List Nat := [5, 2, 1, 2, 3, 1, 2, 1, 4]
def baseStart_1651926 : Nat := 118140960795 + 1651926 * 2 ^ 59
def prefixEnd_1651926 : Nat := 4983230072969 + 3 ^ 40 * 1651926 * 2
def baseEnd_1651926 : Nat := 376992019404092918056861

theorem tailTrace_1651926 : CollatzResearch.WordTrace tailWord_1651926 prefixEnd_1651926 376992019404092918056861 := by
  unfold tailWord_1651926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3765668188335106459041977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40167127342241135563114421 3765668188335106459041977)
  ·
    refine ⟨2824251141251329844281483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3765668188335106459041977 2824251141251329844281483)
    ·
      refine ⟨4236376711876994766422225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2824251141251329844281483 4236376711876994766422225)
      ·
        refine ⟨3177282533907746074816669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4236376711876994766422225 3177282533907746074816669)
        ·
          refine ⟨1191480950215404778056251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3177282533907746074816669 1191480950215404778056251)
          ·
            refine ⟨1787221425323107167084377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1191480950215404778056251 1787221425323107167084377)
            ·
              refine ⟨1340416068992330375313283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1787221425323107167084377 1340416068992330375313283)
              ·
                refine ⟨2010624103488495562969925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1340416068992330375313283 2010624103488495562969925)
                ·
                  refine ⟨376992019404092918056861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2010624103488495562969925 376992019404092918056861)
                  ·
                    rfl

theorem cell21_1651926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_1651926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1651926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1651926 prefixEnd_1651926 := by exact prefixLift 1651926
  have htrace : WordTrace (prefixWord ++ tailWord_1651926) baseStart_1651926 baseEnd_1651926 := by
    simpa [prefixWord, tailWord_1651926, baseEnd_1651926] using wordTrace_append hprefix tailTrace_1651926
  have hstable : (prefixWord ++ tailWord_1651926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651926).length < 2 ^ (prefixWord ++ tailWord_1651926).sum := by decide
  have hdescent : baseEnd_1651926 < baseStart_1651926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652013 : List Nat := [1, 5, 3, 1, 1, 1, 1, 5, 3]
def baseStart_1652013 : Nat := 118140960795 + 1652013 * 2 ^ 59
def prefixEnd_1652013 : Nat := 4983230072969 + 3 ^ 40 * 1652013 * 2
def baseEnd_1652013 : Nat := 377011873989400100106683

theorem tailTrace_1652013 : CollatzResearch.WordTrace tailWord_1652013 prefixEnd_1652013 377011873989400100106683 := by
  unfold tailWord_1652013
  simp only [CollatzResearch.WordTrace]
  refine ⟨60253864164046517203088693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40169242776031011468725795 60253864164046517203088693)
  ·
    refine ⟨5648799765379360987789565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60253864164046517203088693 5648799765379360987789565)
    ·
      refine ⟨2118299912017260370421087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5648799765379360987789565 2118299912017260370421087)
      ·
        refine ⟨3177449868025890555631631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2118299912017260370421087 3177449868025890555631631)
        ·
          refine ⟨4766174802038835833447447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3177449868025890555631631 4766174802038835833447447)
          ·
            refine ⟨7149262203058253750171171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4766174802038835833447447 7149262203058253750171171)
            ·
              refine ⟨10723893304587380625256757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7149262203058253750171171 10723893304587380625256757)
              ·
                refine ⟨1005364997305066933617821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10723893304587380625256757 1005364997305066933617821)
                ·
                  refine ⟨377011873989400100106683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1005364997305066933617821 377011873989400100106683)
                  ·
                    rfl

theorem cell21_1652013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_1652013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1652013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1652013 prefixEnd_1652013 := by exact prefixLift 1652013
  have htrace : WordTrace (prefixWord ++ tailWord_1652013) baseStart_1652013 baseEnd_1652013 := by
    simpa [prefixWord, tailWord_1652013, baseEnd_1652013] using wordTrace_append hprefix tailTrace_1652013
  have hstable : (prefixWord ++ tailWord_1652013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652013).length < 2 ^ (prefixWord ++ tailWord_1652013).sum := by decide
  have hdescent : baseEnd_1652013 < baseStart_1652013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652100 : List Nat := [2, 3, 2, 1, 1, 4, 2, 6]
def baseStart_1652100 : Nat := 118140960795 + 1652100 * 2 ^ 59
def prefixEnd_1652100 : Nat := 4983230072969 + 3 ^ 40 * 1652100 * 2
def baseEnd_1652100 : Nat := 125677242858235760718835

theorem tailTrace_1652100 : CollatzResearch.WordTrace tailWord_1652100 prefixEnd_1652100 125677242858235760718835 := by
  unfold tailWord_1652100
  simp only [CollatzResearch.WordTrace]
  refine ⟨30128518657365665530752877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40171358209820887374337169 30128518657365665530752877)
  ·
    refine ⟨11298194496512124574032329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30128518657365665530752877 11298194496512124574032329)
    ·
      refine ⟨8473645872384093430524247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11298194496512124574032329 8473645872384093430524247)
      ·
        refine ⟨12710468808576140145786371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8473645872384093430524247 12710468808576140145786371)
        ·
          refine ⟨19065703212864210218679557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12710468808576140145786371 19065703212864210218679557)
          ·
            refine ⟨3574819352412039416002417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19065703212864210218679557 3574819352412039416002417)
            ·
              refine ⟨2681114514309029562001813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3574819352412039416002417 2681114514309029562001813)
              ·
                refine ⟨125677242858235760718835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2681114514309029562001813 125677242858235760718835)
                ·
                  rfl

theorem cell21_1652100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 6].length) (baseStart_1652100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1652100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1652100 prefixEnd_1652100 := by exact prefixLift 1652100
  have htrace : WordTrace (prefixWord ++ tailWord_1652100) baseStart_1652100 baseEnd_1652100 := by
    simpa [prefixWord, tailWord_1652100, baseEnd_1652100] using wordTrace_append hprefix tailTrace_1652100
  have hstable : (prefixWord ++ tailWord_1652100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652100).length < 2 ^ (prefixWord ++ tailWord_1652100).sum := by decide
  have hdescent : baseEnd_1652100 < baseStart_1652100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652103 : List Nat := [1, 1, 4, 2, 2, 4, 2, 1, 4]
def baseStart_1652103 : Nat := 118140960795 + 1652103 * 2 ^ 59
def prefixEnd_1652103 : Nat := 4983230072969 + 3 ^ 40 * 1652103 * 2
def baseEnd_1652103 : Nat := 377032413215579943606499

theorem tailTrace_1652103 : CollatzResearch.WordTrace tailWord_1652103 prefixEnd_1652103 377032413215579943606499 := by
  unfold tailWord_1652103
  simp only [CollatzResearch.WordTrace]
  refine ⟨60257146733720462573864963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40171431155813641715909975 60257146733720462573864963)
  ·
    refine ⟨90385720100580693860797445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60257146733720462573864963 90385720100580693860797445)
    ·
      refine ⟨16947322518858880098899521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90385720100580693860797445 16947322518858880098899521)
      ·
        refine ⟨12710491889144160074174641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16947322518858880098899521 12710491889144160074174641)
        ·
          refine ⟨9532868916858120055630981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12710491889144160074174641 9532868916858120055630981)
          ·
            refine ⟨1787412921910897510430809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9532868916858120055630981 1787412921910897510430809)
            ·
              refine ⟨1340559691433173132823107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1787412921910897510430809 1340559691433173132823107)
              ·
                refine ⟨2010839537149759699234661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1340559691433173132823107 2010839537149759699234661)
                ·
                  refine ⟨377032413215579943606499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2010839537149759699234661 377032413215579943606499)
                  ·
                    rfl

theorem cell21_1652103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 4].length) (baseStart_1652103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1652103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1652103 prefixEnd_1652103 := by exact prefixLift 1652103
  have htrace : WordTrace (prefixWord ++ tailWord_1652103) baseStart_1652103 baseEnd_1652103 := by
    simpa [prefixWord, tailWord_1652103, baseEnd_1652103] using wordTrace_append hprefix tailTrace_1652103
  have hstable : (prefixWord ++ tailWord_1652103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652103).length < 2 ^ (prefixWord ++ tailWord_1652103).sum := by decide
  have hdescent : baseEnd_1652103 < baseStart_1652103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652131 : List Nat := [1, 1, 1, 4, 1, 3, 2, 5, 3]
def baseStart_1652131 : Nat := 118140960795 + 1652131 * 2 ^ 59
def prefixEnd_1652131 : Nat := 4983230072969 + 3 ^ 40 * 1652131 * 2
def baseEnd_1652131 : Nat := 377038803197058117139775

theorem tailTrace_1652131 : CollatzResearch.WordTrace tailWord_1652131 prefixEnd_1652131 377038803197058117139775 := by
  unfold tailWord_1652131
  simp only [CollatzResearch.WordTrace]
  refine ⟨60258167977619023355884247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40172111985079348903922831 60258167977619023355884247)
  ·
    refine ⟨90387251966428535033826371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60258167977619023355884247 90387251966428535033826371)
    ·
      refine ⟨135580877949642802550739557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90387251966428535033826371 135580877949642802550739557)
      ·
        refine ⟨25421414615558025478263667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135580877949642802550739557 25421414615558025478263667)
        ·
          refine ⟨38132121923337038217395501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25421414615558025478263667 38132121923337038217395501)
          ·
            refine ⟨14299545721251389331523313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38132121923337038217395501 14299545721251389331523313)
            ·
              refine ⟨10724659290938541998642485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14299545721251389331523313 10724659290938541998642485)
              ·
                refine ⟨1005436808525488312372733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10724659290938541998642485 1005436808525488312372733)
                ·
                  refine ⟨377038803197058117139775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1005436808525488312372733 377038803197058117139775)
                  ·
                    rfl

theorem cell21_1652131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5, 3].length) (baseStart_1652131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1652131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1652131 prefixEnd_1652131 := by exact prefixLift 1652131
  have htrace : WordTrace (prefixWord ++ tailWord_1652131) baseStart_1652131 baseEnd_1652131 := by
    simpa [prefixWord, tailWord_1652131, baseEnd_1652131] using wordTrace_append hprefix tailTrace_1652131
  have hstable : (prefixWord ++ tailWord_1652131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652131).length < 2 ^ (prefixWord ++ tailWord_1652131).sum := by decide
  have hdescent : baseEnd_1652131 < baseStart_1652131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652207 : List Nat := [1, 1, 2, 1, 4, 1, 4, 4, 3]
def baseStart_1652207 : Nat := 118140960795 + 1652207 * 2 ^ 59
def prefixEnd_1652207 : Nat := 4983230072969 + 3 ^ 40 * 1652207 * 2
def baseEnd_1652207 : Nat := 377056147432498873872953

theorem tailTrace_1652207 : CollatzResearch.WordTrace tailWord_1652207 prefixEnd_1652207 377056147432498873872953 := by
  unfold tailWord_1652207
  simp only [CollatzResearch.WordTrace]
  refine ⟨60260939925343688335650875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40173959950229125557100583 60260939925343688335650875)
  ·
    refine ⟨90391409888015532503476313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60260939925343688335650875 90391409888015532503476313)
    ·
      refine ⟨67793557416011649377607235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90391409888015532503476313 67793557416011649377607235)
      ·
        refine ⟨101690336124017474066410853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67793557416011649377607235 101690336124017474066410853)
        ·
          refine ⟨19066938023253276387452035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101690336124017474066410853 19066938023253276387452035)
          ·
            refine ⟨28600407034879914581178053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19066938023253276387452035 28600407034879914581178053)
            ·
              refine ⟨5362576319039983983970885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28600407034879914581178053 5362576319039983983970885)
              ·
                refine ⟨1005483059819996996994541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5362576319039983983970885 1005483059819996996994541)
                ·
                  refine ⟨377056147432498873872953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1005483059819996996994541 377056147432498873872953)
                  ·
                    rfl

theorem cell21_1652207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4, 3].length) (baseStart_1652207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1652207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1652207 prefixEnd_1652207 := by exact prefixLift 1652207
  have htrace : WordTrace (prefixWord ++ tailWord_1652207) baseStart_1652207 baseEnd_1652207 := by
    simpa [prefixWord, tailWord_1652207, baseEnd_1652207] using wordTrace_append hprefix tailTrace_1652207
  have hstable : (prefixWord ++ tailWord_1652207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652207).length < 2 ^ (prefixWord ++ tailWord_1652207).sum := by decide
  have hdescent : baseEnd_1652207 < baseStart_1652207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652328 : List Nat := [2, 1, 4, 3, 1, 1, 3, 6]
def baseStart_1652328 : Nat := 118140960795 + 1652328 * 2 ^ 59
def prefixEnd_1652328 : Nat := 4983230072969 + 3 ^ 40 * 1652328 * 2
def baseEnd_1652328 : Nat := 125694587093676517452013

theorem tailTrace_1652328 : CollatzResearch.WordTrace tailWord_1652328 prefixEnd_1652328 125694587093676517452013 := by
  unfold tailWord_1652328
  simp only [CollatzResearch.WordTrace]
  refine ⟨30132676578952663000402819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40176902105270217333870425 30132676578952663000402819)
  ·
    refine ⟨45199014868428994500604229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30132676578952663000402819 45199014868428994500604229)
    ·
      refine ⟨8474815287830436468863293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45199014868428994500604229 8474815287830436468863293)
      ·
        refine ⟨3178055732936413675823735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8474815287830436468863293 3178055732936413675823735)
        ·
          refine ⟨4767083599404620513735603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3178055732936413675823735 4767083599404620513735603)
          ·
            refine ⟨7150625399106930770603405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4767083599404620513735603 7150625399106930770603405)
            ·
              refine ⟨2681484524665099038976277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7150625399106930770603405 2681484524665099038976277)
              ·
                refine ⟨125694587093676517452013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2681484524665099038976277 125694587093676517452013)
                ·
                  rfl

theorem cell21_1652328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 6].length) (baseStart_1652328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1652328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1652328 prefixEnd_1652328 := by exact prefixLift 1652328
  have htrace : WordTrace (prefixWord ++ tailWord_1652328) baseStart_1652328 baseEnd_1652328 := by
    simpa [prefixWord, tailWord_1652328, baseEnd_1652328] using wordTrace_append hprefix tailTrace_1652328
  have hstable : (prefixWord ++ tailWord_1652328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652328).length < 2 ^ (prefixWord ++ tailWord_1652328).sum := by decide
  have hdescent : baseEnd_1652328 < baseStart_1652328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652359 : List Nat := [1, 1, 4, 2, 1, 3, 1, 5, 3]
def baseStart_1652359 : Nat := 118140960795 + 1652359 * 2 ^ 59
def prefixEnd_1652359 : Nat := 4983230072969 + 3 ^ 40 * 1652359 * 2
def baseEnd_1652359 : Nat := 377090835903380387339309

theorem tailTrace_1652359 : CollatzResearch.WordTrace tailWord_1652359 prefixEnd_1652359 377090835903380387339309 := by
  unfold tailWord_1652359
  simp only [CollatzResearch.WordTrace]
  refine ⟨60266483820793018295184131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40177655880528678863456087 60266483820793018295184131)
  ·
    refine ⟨90399725731189527442776197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60266483820793018295184131 90399725731189527442776197)
    ·
      refine ⟨16949948574598036395520537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90399725731189527442776197 16949948574598036395520537)
      ·
        refine ⟨12712461430948527296640403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16949948574598036395520537 12712461430948527296640403)
        ·
          refine ⟨19068692146422790944960605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12712461430948527296640403 19068692146422790944960605)
          ·
            refine ⟨7150759554908546604360227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19068692146422790944960605 7150759554908546604360227)
            ·
              refine ⟨10726139332362819906540341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7150759554908546604360227 10726139332362819906540341)
              ·
                refine ⟨1005575562409014366238157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10726139332362819906540341 1005575562409014366238157)
                ·
                  refine ⟨377090835903380387339309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1005575562409014366238157 377090835903380387339309)
                  ·
                    rfl

theorem cell21_1652359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5, 3].length) (baseStart_1652359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1652359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1652359 prefixEnd_1652359 := by exact prefixLift 1652359
  have htrace : WordTrace (prefixWord ++ tailWord_1652359) baseStart_1652359 baseEnd_1652359 := by
    simpa [prefixWord, tailWord_1652359, baseEnd_1652359] using wordTrace_append hprefix tailTrace_1652359
  have hstable : (prefixWord ++ tailWord_1652359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652359).length < 2 ^ (prefixWord ++ tailWord_1652359).sum := by decide
  have hdescent : baseEnd_1652359 < baseStart_1652359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652438 : List Nat := [5, 2, 1, 3, 1, 1, 2, 6]
def baseStart_1652438 : Nat := 118140960795 + 1652438 * 2 ^ 59
def prefixEnd_1652438 : Nat := 4983230072969 + 3 ^ 40 * 1652438 * 2
def baseEnd_1652438 : Nat := 125702954926564601840827

theorem tailTrace_1652438 : CollatzResearch.WordTrace tailWord_1652438 prefixEnd_1652438 125702954926564601840827 := by
  unfold tailWord_1652438
  simp only [CollatzResearch.WordTrace]
  refine ⟨3766835324219175924206873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40179576791671209858206645 3766835324219175924206873)
  ·
    refine ⟨2825126493164381943155155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3766835324219175924206873 2825126493164381943155155)
    ·
      refine ⟨4237689739746572914732733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2825126493164381943155155 4237689739746572914732733)
      ·
        refine ⟨1589133652404964843024775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4237689739746572914732733 1589133652404964843024775)
        ·
          refine ⟨2383700478607447264537163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1589133652404964843024775 2383700478607447264537163)
          ·
            refine ⟨3575550717911170896805745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2383700478607447264537163 3575550717911170896805745)
            ·
              refine ⟨2681663038433378172604309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3575550717911170896805745 2681663038433378172604309)
              ·
                refine ⟨125702954926564601840827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2681663038433378172604309 125702954926564601840827)
                ·
                  rfl

theorem cell21_1652438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_1652438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1652438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1652438 prefixEnd_1652438 := by exact prefixLift 1652438
  have htrace : WordTrace (prefixWord ++ tailWord_1652438) baseStart_1652438 baseEnd_1652438 := by
    simpa [prefixWord, tailWord_1652438, baseEnd_1652438] using wordTrace_append hprefix tailTrace_1652438
  have hstable : (prefixWord ++ tailWord_1652438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652438).length < 2 ^ (prefixWord ++ tailWord_1652438).sum := by decide
  have hdescent : baseEnd_1652438 < baseStart_1652438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652477 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 9]
def baseStart_1652477 : Nat := 118140960795 + 1652477 * 2 ^ 59
def prefixEnd_1652477 : Nat := 4983230072969 + 3 ^ 40 * 1652477 * 2
def baseEnd_1652477 : Nat := 377117765111038404372401

theorem tailTrace_1652477 : CollatzResearch.WordTrace tailWord_1652477 prefixEnd_1652477 377117765111038404372401 := by
  unfold tailWord_1652477
  simp only [CollatzResearch.WordTrace]
  refine ⟨60270787634365524447979685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40180525089577016298653123 60270787634365524447979685)
  ·
    refine ⟨11300772681443535833996191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60270787634365524447979685 11300772681443535833996191)
    ·
      refine ⟨16951159022165303750994287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11300772681443535833996191 16951159022165303750994287)
      ·
        refine ⟨25426738533247955626491431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16951159022165303750994287 25426738533247955626491431)
        ·
          refine ⟨38140107799871933439737147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25426738533247955626491431 38140107799871933439737147)
          ·
            refine ⟨57210161699807900159605721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38140107799871933439737147 57210161699807900159605721)
            ·
              refine ⟨42907621274855925119704291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57210161699807900159605721 42907621274855925119704291)
              ·
                refine ⟨64361431912283887679556437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42907621274855925119704291 64361431912283887679556437)
                ·
                  refine ⟨377117765111038404372401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64361431912283887679556437 377117765111038404372401)
                  ·
                    rfl

theorem cell21_1652477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_1652477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1652477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1652477 prefixEnd_1652477 := by exact prefixLift 1652477
  have htrace : WordTrace (prefixWord ++ tailWord_1652477) baseStart_1652477 baseEnd_1652477 := by
    simpa [prefixWord, tailWord_1652477, baseEnd_1652477] using wordTrace_append hprefix tailTrace_1652477
  have hstable : (prefixWord ++ tailWord_1652477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652477).length < 2 ^ (prefixWord ++ tailWord_1652477).sum := by decide
  have hdescent : baseEnd_1652477 < baseStart_1652477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652542 : List Nat := [4, 2, 1, 2, 2, 1, 3, 2, 4]
def baseStart_1652542 : Nat := 118140960795 + 1652542 * 2 ^ 59
def prefixEnd_1652542 : Nat := 4983230072969 + 3 ^ 40 * 1652542 * 2
def baseEnd_1652542 : Nat := 377132598996612735788935

theorem tailTrace_1652542 : CollatzResearch.WordTrace tailWord_1652542 prefixEnd_1652542 377132598996612735788935 := by
  unfold tailWord_1652542
  simp only [CollatzResearch.WordTrace]
  refine ⟨7534144797391255068636985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40182105586086693699397253 7534144797391255068636985)
  ·
    refine ⟨5650608598043441301477739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7534144797391255068636985 5650608598043441301477739)
    ·
      refine ⟨8475912897065161952216609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5650608598043441301477739 8475912897065161952216609)
      ·
        refine ⟨6356934672798871464162457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8475912897065161952216609 6356934672798871464162457)
        ·
          refine ⟨4767701004599153598121843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6356934672798871464162457 4767701004599153598121843)
          ·
            refine ⟨7151551506898730397182765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4767701004599153598121843 7151551506898730397182765)
            ·
              refine ⟨2681831815087023898943537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7151551506898730397182765 2681831815087023898943537)
              ·
                refine ⟨2011373861315267924207653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2681831815087023898943537 2011373861315267924207653)
                ·
                  refine ⟨377132598996612735788935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2011373861315267924207653 377132598996612735788935)
                  ·
                    rfl

theorem cell21_1652542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_1652542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1652542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1652542 prefixEnd_1652542 := by exact prefixLift 1652542
  have htrace : WordTrace (prefixWord ++ tailWord_1652542) baseStart_1652542 baseEnd_1652542 := by
    simpa [prefixWord, tailWord_1652542, baseEnd_1652542] using wordTrace_append hprefix tailTrace_1652542
  have hstable : (prefixWord ++ tailWord_1652542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652542).length < 2 ^ (prefixWord ++ tailWord_1652542).sum := by decide
  have hdescent : baseEnd_1652542 < baseStart_1652542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652584 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 8]
def baseStart_1652584 : Nat := 118140960795 + 1652584 * 2 ^ 59
def prefixEnd_1652584 : Nat := 4983230072969 + 3 ^ 40 * 1652584 * 2
def baseEnd_1652584 : Nat := 377142183968829996088849

theorem tailTrace_1652584 : CollatzResearch.WordTrace tailWord_1652584 prefixEnd_1652584 377142183968829996088849 := by
  unfold tailWord_1652584
  simp only [CollatzResearch.WordTrace]
  refine ⟨30137345122488940861062403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40183126829985254481416537 30137345122488940861062403)
  ·
    refine ⟨45206017683733411291593605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30137345122488940861062403 45206017683733411291593605)
    ·
      refine ⟨8476128315700014617173801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45206017683733411291593605 8476128315700014617173801)
      ·
        refine ⟨6357096236775010962880351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8476128315700014617173801 6357096236775010962880351)
        ·
          refine ⟨9535644355162516444320527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6357096236775010962880351 9535644355162516444320527)
          ·
            refine ⟨14303466532743774666480791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9535644355162516444320527 14303466532743774666480791)
            ·
              refine ⟨21455199799115661999721187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14303466532743774666480791 21455199799115661999721187)
              ·
                refine ⟨32182799698673492999581781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21455199799115661999721187 32182799698673492999581781)
                ·
                  refine ⟨377142183968829996088849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32182799698673492999581781 377142183968829996088849)
                  ·
                    rfl

theorem cell21_1652584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 8].length) (baseStart_1652584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1652584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1652584 prefixEnd_1652584 := by exact prefixLift 1652584
  have htrace : WordTrace (prefixWord ++ tailWord_1652584) baseStart_1652584 baseEnd_1652584 := by
    simpa [prefixWord, tailWord_1652584, baseEnd_1652584] using wordTrace_append hprefix tailTrace_1652584
  have hstable : (prefixWord ++ tailWord_1652584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652584).length < 2 ^ (prefixWord ++ tailWord_1652584).sum := by decide
  have hdescent : baseEnd_1652584 < baseStart_1652584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652618 : List Nat := [3, 1, 2, 4, 2, 1, 1, 3, 4]
def baseStart_1652618 : Nat := 118140960795 + 1652618 * 2 ^ 59
def prefixEnd_1652618 : Nat := 4983230072969 + 3 ^ 40 * 1652618 * 2
def baseEnd_1652618 : Nat := 377149943232053492522113

theorem tailTrace_1652618 : CollatzResearch.WordTrace tailWord_1652618 prefixEnd_1652618 377149943232053492522113 := by
  unfold tailWord_1652618
  simp only [CollatzResearch.WordTrace]
  refine ⟨15068982581713676382215627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40183953551236470352575005 15068982581713676382215627)
  ·
    refine ⟨22603473872570514573323441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15068982581713676382215627 22603473872570514573323441)
    ·
      refine ⟨16952605404427885929992581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22603473872570514573323441 16952605404427885929992581)
      ·
        refine ⟨3178613513330228611873609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16952605404427885929992581 3178613513330228611873609)
        ·
          refine ⟨2383960134997671458905207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3178613513330228611873609 2383960134997671458905207)
          ·
            refine ⟨3575940202496507188357811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2383960134997671458905207 3575940202496507188357811)
            ·
              refine ⟨5363910303744760782536717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3575940202496507188357811 5363910303744760782536717)
              ·
                refine ⟨2011466363904285293451269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5363910303744760782536717 2011466363904285293451269)
                ·
                  refine ⟨377149943232053492522113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2011466363904285293451269 377149943232053492522113)
                  ·
                    rfl

theorem cell21_1652618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_1652618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1652618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1652618 prefixEnd_1652618 := by exact prefixLift 1652618
  have htrace : WordTrace (prefixWord ++ tailWord_1652618) baseStart_1652618 baseEnd_1652618 := by
    simpa [prefixWord, tailWord_1652618, baseEnd_1652618] using wordTrace_append hprefix tailTrace_1652618
  have hstable : (prefixWord ++ tailWord_1652618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652618).length < 2 ^ (prefixWord ++ tailWord_1652618).sum := by decide
  have hdescent : baseEnd_1652618 < baseStart_1652618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652629 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 7]
def baseStart_1652629 : Nat := 118140960795 + 1652629 * 2 ^ 59
def prefixEnd_1652629 : Nat := 4983230072969 + 3 ^ 40 * 1652629 * 2
def baseEnd_1652629 : Nat := 377152453581919917838757

theorem tailTrace_1652629 : CollatzResearch.WordTrace tailWord_1652629 prefixEnd_1652629 377152453581919917838757 := by
  unfold tailWord_1652629
  simp only [CollatzResearch.WordTrace]
  refine ⟨60276331529814854407512941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40184221019876569605008627 60276331529814854407512941)
  ·
    refine ⟨22603624323680570402817353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60276331529814854407512941 22603624323680570402817353)
    ·
      refine ⟨16952718242760427802113015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22603624323680570402817353 16952718242760427802113015)
      ·
        refine ⟨25429077364140641703169523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16952718242760427802113015 25429077364140641703169523)
        ·
          refine ⟨38143616046210962554754285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25429077364140641703169523 38143616046210962554754285)
          ·
            refine ⟨14303856017329110958032857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38143616046210962554754285 14303856017329110958032857)
            ·
              refine ⟨10727892012996833218524643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14303856017329110958032857 10727892012996833218524643)
              ·
                refine ⟨16091838019495249827786965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10727892012996833218524643 16091838019495249827786965)
                ·
                  refine ⟨377152453581919917838757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16091838019495249827786965 377152453581919917838757)
                  ·
                    rfl

theorem cell21_1652629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_1652629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1652629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1652629 prefixEnd_1652629 := by exact prefixLift 1652629
  have htrace : WordTrace (prefixWord ++ tailWord_1652629) baseStart_1652629 baseEnd_1652629 := by
    simpa [prefixWord, tailWord_1652629, baseEnd_1652629] using wordTrace_append hprefix tailTrace_1652629
  have hstable : (prefixWord ++ tailWord_1652629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652629).length < 2 ^ (prefixWord ++ tailWord_1652629).sum := by decide
  have hdescent : baseEnd_1652629 < baseStart_1652629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652711 : List Nat := [1, 1, 5, 2, 4, 1, 1, 2, 4]
def baseStart_1652711 : Nat := 118140960795 + 1652711 * 2 ^ 59
def prefixEnd_1652711 : Nat := 4983230072969 + 3 ^ 40 * 1652711 * 2
def baseEnd_1652711 : Nat := 377171167099105997471923

theorem tailTrace_1652711 : CollatzResearch.WordTrace tailWord_1652711 prefixEnd_1652711 377171167099105997471923 := by
  unfold tailWord_1652711
  simp only [CollatzResearch.WordTrace]
  refine ⟨60279322315517782411997987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40186214877011854941331991 60279322315517782411997987)
  ·
    refine ⟨90418983473276673617996981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60279322315517782411997987 90418983473276673617996981)
    ·
      refine ⟨8476779700619688151687217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90418983473276673617996981 8476779700619688151687217)
      ·
        refine ⟨6357584775464766113765413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8476779700619688151687217 6357584775464766113765413)
        ·
          refine ⟨1192047145399643646331015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6357584775464766113765413 1192047145399643646331015)
          ·
            refine ⟨1788070718099465469496523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192047145399643646331015 1788070718099465469496523)
            ·
              refine ⟨2682106077149198204244785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1788070718099465469496523 2682106077149198204244785)
              ·
                refine ⟨2011579557861898653183589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2682106077149198204244785 2011579557861898653183589)
                ·
                  refine ⟨377171167099105997471923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2011579557861898653183589 377171167099105997471923)
                  ·
                    rfl

theorem cell21_1652711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 4].length) (baseStart_1652711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1652711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1652711 prefixEnd_1652711 := by exact prefixLift 1652711
  have htrace : WordTrace (prefixWord ++ tailWord_1652711) baseStart_1652711 baseEnd_1652711 := by
    simpa [prefixWord, tailWord_1652711, baseEnd_1652711] using wordTrace_append hprefix tailTrace_1652711
  have hstable : (prefixWord ++ tailWord_1652711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652711).length < 2 ^ (prefixWord ++ tailWord_1652711).sum := by decide
  have hdescent : baseEnd_1652711 < baseStart_1652711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652832 : List Nat := [2, 1, 1, 3, 2, 5, 2, 2, 3]
def baseStart_1652832 : Nat := 118140960795 + 1652832 * 2 ^ 59
def prefixEnd_1652832 : Nat := 4983230072969 + 3 ^ 40 * 1652832 * 2
def baseEnd_1652832 : Nat := 377198780947636675955009

theorem tailTrace_1652832 : CollatzResearch.WordTrace tailWord_1652832 prefixEnd_1652832 377198780947636675955009 := by
  unfold tailWord_1652832
  simp only [CollatzResearch.WordTrace]
  refine ⟨30141867774039710038576375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40189157032052946718101833 30141867774039710038576375)
  ·
    refine ⟨45212801661059565057864563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30141867774039710038576375 45212801661059565057864563)
    ·
      refine ⟨67819202491589347586796845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45212801661059565057864563 67819202491589347586796845)
      ·
        refine ⟨25432200934346005345048817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67819202491589347586796845 25432200934346005345048817)
        ·
          refine ⟨19074150700759504008786613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25432200934346005345048817 19074150700759504008786613)
          ·
            refine ⟨1788201628196203500823745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19074150700759504008786613 1788201628196203500823745)
            ·
              refine ⟨1341151221147152625617809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1788201628196203500823745 1341151221147152625617809)
              ·
                refine ⟨1005863415860364469213357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1341151221147152625617809 1005863415860364469213357)
                ·
                  refine ⟨377198780947636675955009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1005863415860364469213357 377198780947636675955009)
                  ·
                    rfl

theorem cell21_1652832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2, 3].length) (baseStart_1652832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1652832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1652832 prefixEnd_1652832 := by exact prefixLift 1652832
  have htrace : WordTrace (prefixWord ++ tailWord_1652832) baseStart_1652832 baseEnd_1652832 := by
    simpa [prefixWord, tailWord_1652832, baseEnd_1652832] using wordTrace_append hprefix tailTrace_1652832
  have hstable : (prefixWord ++ tailWord_1652832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652832).length < 2 ^ (prefixWord ++ tailWord_1652832).sum := by decide
  have hdescent : baseEnd_1652832 < baseStart_1652832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652857 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 7]
def baseStart_1652857 : Nat := 118140960795 + 1652857 * 2 ^ 59
def prefixEnd_1652857 : Nat := 4983230072969 + 3 ^ 40 * 1652857 * 2
def baseEnd_1652857 : Nat := 377204486288242188038291

theorem tailTrace_1652857 : CollatzResearch.WordTrace tailWord_1652857 prefixEnd_1652857 377204486288242188038291 := by
  unfold tailWord_1652857
  simp only [CollatzResearch.WordTrace]
  refine ⟨60284647372988849346812825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40189764915325899564541883 60284647372988849346812825)
  ·
    refine ⟨45213485529741637010109619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60284647372988849346812825 45213485529741637010109619)
    ·
      refine ⟨67820228294612455515164429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45213485529741637010109619 67820228294612455515164429)
      ·
        refine ⟨25432585610479670818186661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67820228294612455515164429 25432585610479670818186661)
        ·
          refine ⟨4768609801964938278409999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25432585610479670818186661 4768609801964938278409999)
          ·
            refine ⟨7152914702947407417614999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4768609801964938278409999 7152914702947407417614999)
            ·
              refine ⟨10729372054421111126422499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7152914702947407417614999 10729372054421111126422499)
              ·
                refine ⟨16094058081631666689633749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10729372054421111126422499 16094058081631666689633749)
                ·
                  refine ⟨377204486288242188038291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16094058081631666689633749 377204486288242188038291)
                  ·
                    rfl

theorem cell21_1652857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 7].length) (baseStart_1652857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1652857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1652857 prefixEnd_1652857 := by exact prefixLift 1652857
  have htrace : WordTrace (prefixWord ++ tailWord_1652857) baseStart_1652857 baseEnd_1652857 := by
    simpa [prefixWord, tailWord_1652857, baseEnd_1652857] using wordTrace_append hprefix tailTrace_1652857
  have hstable : (prefixWord ++ tailWord_1652857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652857).length < 2 ^ (prefixWord ++ tailWord_1652857).sum := by decide
  have hdescent : baseEnd_1652857 < baseStart_1652857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652919 : List Nat := [1, 1, 3, 1, 4, 2, 4, 5]
def baseStart_1652919 : Nat := 118140960795 + 1652919 * 2 ^ 59
def prefixEnd_1652919 : Nat := 4983230072969 + 3 ^ 40 * 1652919 * 2
def baseEnd_1652919 : Nat := 125739545177647952668277

theorem tailTrace_1652919 : CollatzResearch.WordTrace tailWord_1652919 prefixEnd_1652919 125739545177647952668277 := by
  unfold tailWord_1652919
  simp only [CollatzResearch.WordTrace]
  refine ⟨60286908698764233935569811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40191272465842822623713207 60286908698764233935569811)
  ·
    refine ⟨90430363048146350903354717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60286908698764233935569811 90430363048146350903354717)
    ·
      refine ⟨33911386143054881588758019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90430363048146350903354717 33911386143054881588758019)
      ·
        refine ⟨50867079214582322383137029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33911386143054881588758019 50867079214582322383137029)
        ·
          refine ⟨9537577352734185446838193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50867079214582322383137029 9537577352734185446838193)
          ·
            refine ⟨7153183014550639085128645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9537577352734185446838193 7153183014550639085128645)
            ·
              refine ⟨1341221815228244828461621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7153183014550639085128645 1341221815228244828461621)
              ·
                refine ⟨125739545177647952668277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1341221815228244828461621 125739545177647952668277)
                ·
                  rfl

theorem cell21_1652919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 5].length) (baseStart_1652919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1652919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1652919 prefixEnd_1652919 := by exact prefixLift 1652919
  have htrace : WordTrace (prefixWord ++ tailWord_1652919) baseStart_1652919 baseEnd_1652919 := by
    simpa [prefixWord, tailWord_1652919, baseEnd_1652919] using wordTrace_append hprefix tailTrace_1652919
  have hstable : (prefixWord ++ tailWord_1652919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652919).length < 2 ^ (prefixWord ++ tailWord_1652919).sum := by decide
  have hdescent : baseEnd_1652919 < baseStart_1652919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652956 : List Nat := [2, 2, 5, 2, 1, 2, 2, 1, 4]
def baseStart_1652956 : Nat := 118140960795 + 1652956 * 2 ^ 59
def prefixEnd_1652956 : Nat := 4983230072969 + 3 ^ 40 * 1652956 * 2
def baseEnd_1652956 : Nat := 377227079437040015888089

theorem tailTrace_1652956 : CollatzResearch.WordTrace tailWord_1652956 prefixEnd_1652956 377227079437040015888089 := by
  unfold tailWord_1652956
  simp only [CollatzResearch.WordTrace]
  refine ⟨30144129099815094627333361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40192172133086792836444481 30144129099815094627333361)
  ·
    refine ⟨22608096824861320970500021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30144129099815094627333361 22608096824861320970500021)
    ·
      refine ⟨2119509077330748840984377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22608096824861320970500021 2119509077330748840984377)
      ·
        refine ⟨1589631807998061630738283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2119509077330748840984377 1589631807998061630738283)
        ·
          refine ⟨2384447711997092446107425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1589631807998061630738283 2384447711997092446107425)
          ·
            refine ⟨1788335783997819334580569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2384447711997092446107425 1788335783997819334580569)
            ·
              refine ⟨1341251837998364500935427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1788335783997819334580569 1341251837998364500935427)
              ·
                refine ⟨2011877756997546751403141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1341251837998364500935427 2011877756997546751403141)
                ·
                  refine ⟨377227079437040015888089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2011877756997546751403141 377227079437040015888089)
                  ·
                    rfl

theorem cell21_1652956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_1652956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1652956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1652956 prefixEnd_1652956 := by exact prefixLift 1652956
  have htrace : WordTrace (prefixWord ++ tailWord_1652956) baseStart_1652956 baseEnd_1652956 := by
    simpa [prefixWord, tailWord_1652956, baseEnd_1652956] using wordTrace_append hprefix tailTrace_1652956
  have hstable : (prefixWord ++ tailWord_1652956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652956).length < 2 ^ (prefixWord ++ tailWord_1652956).sum := by decide
  have hdescent : baseEnd_1652956 < baseStart_1652956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653026 : List Nat := [3, 3, 1, 1, 3, 2, 1, 2, 5]
def baseStart_1653026 : Nat := 118140960795 + 1653026 * 2 ^ 59
def prefixEnd_1653026 : Nat := 4983230072969 + 3 ^ 40 * 1653026 * 2
def baseEnd_1653026 : Nat := 377243054390735449721279

theorem tailTrace_1653026 : CollatzResearch.WordTrace tailWord_1653026 prefixEnd_1653026 377243054390735449721279 := by
  unfold tailWord_1653026
  simp only [CollatzResearch.WordTrace]
  refine ⟨15072702827344147802428733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40193874206251060806476621 15072702827344147802428733)
  ·
    refine ⟨5652263560254055425910775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15072702827344147802428733 5652263560254055425910775)
    ·
      refine ⟨8478395340381083138866163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5652263560254055425910775 8478395340381083138866163)
      ·
        refine ⟨12717593010571624708299245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8478395340381083138866163 12717593010571624708299245)
        ·
          refine ⟨4769097378964359265612217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12717593010571624708299245 4769097378964359265612217)
          ·
            refine ⟨3576823034223269449209163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4769097378964359265612217 3576823034223269449209163)
            ·
              refine ⟨5365234551334904173813745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3576823034223269449209163 5365234551334904173813745)
              ·
                refine ⟨4023925913501178130360309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5365234551334904173813745 4023925913501178130360309)
                ·
                  refine ⟨377243054390735449721279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4023925913501178130360309 377243054390735449721279)
                  ·
                    rfl

theorem cell21_1653026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_1653026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1653026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1653026 prefixEnd_1653026 := by exact prefixLift 1653026
  have htrace : WordTrace (prefixWord ++ tailWord_1653026) baseStart_1653026 baseEnd_1653026 := by
    simpa [prefixWord, tailWord_1653026, baseEnd_1653026] using wordTrace_append hprefix tailTrace_1653026
  have hstable : (prefixWord ++ tailWord_1653026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653026).length < 2 ^ (prefixWord ++ tailWord_1653026).sum := by decide
  have hdescent : baseEnd_1653026 < baseStart_1653026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653057 : List Nat := [1, 2, 5, 2, 2, 1, 1, 1, 6]
def baseStart_1653057 : Nat := 118140960795 + 1653057 * 2 ^ 59
def prefixEnd_1653057 : Nat := 4983230072969 + 3 ^ 40 * 1653057 * 2
def baseEnd_1653057 : Nat := 377250129013086284704549

theorem tailTrace_1653057 : CollatzResearch.WordTrace tailWord_1653057 prefixEnd_1653057 377250129013086284704549 := by
  unfold tailWord_1653057
  simp only [CollatzResearch.WordTrace]
  refine ⟨60291941972264283504093425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40194627981509522336062283 60291941972264283504093425)
  ·
    refine ⟨45218956479198212628070069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60291941972264283504093425 45218956479198212628070069)
    ·
      refine ⟨4239277169924832433881569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45218956479198212628070069 4239277169924832433881569)
      ·
        refine ⟨3179457877443624325411177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4239277169924832433881569 3179457877443624325411177)
        ·
          refine ⟨2384593408082718244058383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3179457877443624325411177 2384593408082718244058383)
          ·
            refine ⟨3576890112124077366087575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2384593408082718244058383 3576890112124077366087575)
            ·
              refine ⟨5365335168186116049131363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3576890112124077366087575 5365335168186116049131363)
              ·
                refine ⟨8048002752279174073697045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5365335168186116049131363 8048002752279174073697045)
                ·
                  refine ⟨377250129013086284704549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8048002752279174073697045 377250129013086284704549)
                  ·
                    rfl

theorem cell21_1653057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 6].length) (baseStart_1653057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1653057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1653057 prefixEnd_1653057 := by exact prefixLift 1653057
  have htrace : WordTrace (prefixWord ++ tailWord_1653057) baseStart_1653057 baseEnd_1653057 := by
    simpa [prefixWord, tailWord_1653057, baseEnd_1653057] using wordTrace_append hprefix tailTrace_1653057
  have hstable : (prefixWord ++ tailWord_1653057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653057).length < 2 ^ (prefixWord ++ tailWord_1653057).sum := by decide
  have hdescent : baseEnd_1653057 < baseStart_1653057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653088 : List Nat := [2, 1, 1, 3, 5, 2, 2, 5]
def baseStart_1653088 : Nat := 118140960795 + 1653088 * 2 ^ 59
def prefixEnd_1653088 : Nat := 4983230072969 + 3 ^ 40 * 1653088 * 2
def baseEnd_1653088 : Nat := 125752401211812373229273

theorem tailTrace_1653088 : CollatzResearch.WordTrace tailWord_1653088 prefixEnd_1653088 125752401211812373229273 := by
  unfold tailWord_1653088
  simp only [CollatzResearch.WordTrace]
  refine ⟨30146536317575987899235959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40195381756767983865647945 30146536317575987899235959)
  ·
    refine ⟨45219804476363981848853939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30146536317575987899235959 45219804476363981848853939)
    ·
      refine ⟨67829706714545972773280909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45219804476363981848853939 67829706714545972773280909)
      ·
        refine ⟨25436140017954739789980341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67829706714545972773280909 25436140017954739789980341)
        ·
          refine ⟨2384638126683256855310657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25436140017954739789980341 2384638126683256855310657)
          ·
            refine ⟨1788478595012442641482993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2384638126683256855310657 1788478595012442641482993)
            ·
              refine ⟨1341358946259331981112245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1788478595012442641482993 1341358946259331981112245)
              ·
                refine ⟨125752401211812373229273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1341358946259331981112245 125752401211812373229273)
                ·
                  rfl

theorem cell21_1653088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 5].length) (baseStart_1653088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1653088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1653088 prefixEnd_1653088 := by exact prefixLift 1653088
  have htrace : WordTrace (prefixWord ++ tailWord_1653088) baseStart_1653088 baseEnd_1653088 := by
    simpa [prefixWord, tailWord_1653088, baseEnd_1653088] using wordTrace_append hprefix tailTrace_1653088
  have hstable : (prefixWord ++ tailWord_1653088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653088).length < 2 ^ (prefixWord ++ tailWord_1653088).sum := by decide
  have hdescent : baseEnd_1653088 < baseStart_1653088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653192 : List Nat := [2, 1, 3, 1, 3, 2, 2, 3, 4]
def baseStart_1653192 : Nat := 118140960795 + 1653192 * 2 ^ 59
def prefixEnd_1653192 : Nat := 4983230072969 + 3 ^ 40 * 1653192 * 2
def baseEnd_1653192 : Nat := 377280937852356049954273

theorem tailTrace_1653192 : CollatzResearch.WordTrace tailWord_1653192 prefixEnd_1653192 377280937852356049954273 := by
  unfold tailWord_1653192
  simp only [CollatzResearch.WordTrace]
  refine ⟨30148432913387600780128915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40197910551183467706838553 30148432913387600780128915)
  ·
    refine ⟨45222649370081401170193373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30148432913387600780128915 45222649370081401170193373)
    ·
      refine ⟨16958493513780525438822515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45222649370081401170193373 16958493513780525438822515)
      ·
        refine ⟨25437740270670788158233773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16958493513780525438822515 25437740270670788158233773)
        ·
          refine ⟨9539152601501545559337665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25437740270670788158233773 9539152601501545559337665)
          ·
            refine ⟨7154364451126159169503249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9539152601501545559337665 7154364451126159169503249)
            ·
              refine ⟨5365773338344619377127437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7154364451126159169503249 5365773338344619377127437)
              ·
                refine ⟨2012165001879232266422789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5365773338344619377127437 2012165001879232266422789)
                ·
                  refine ⟨377280937852356049954273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2012165001879232266422789 377280937852356049954273)
                  ·
                    rfl

theorem cell21_1653192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 4].length) (baseStart_1653192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1653192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1653192 prefixEnd_1653192 := by exact prefixLift 1653192
  have htrace : WordTrace (prefixWord ++ tailWord_1653192) baseStart_1653192 baseEnd_1653192 := by
    simpa [prefixWord, tailWord_1653192, baseEnd_1653192] using wordTrace_append hprefix tailTrace_1653192
  have hstable : (prefixWord ++ tailWord_1653192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653192).length < 2 ^ (prefixWord ++ tailWord_1653192).sum := by decide
  have hdescent : baseEnd_1653192 < baseStart_1653192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653288 : List Nat := [2, 1, 5, 2, 1, 2, 3, 2, 3]
def baseStart_1653288 : Nat := 118140960795 + 1653288 * 2 ^ 59
def prefixEnd_1653288 : Nat := 4983230072969 + 3 ^ 40 * 1653288 * 2
def baseEnd_1653288 : Nat := 377302846360281216354077

theorem tailTrace_1653288 : CollatzResearch.WordTrace tailWord_1653288 prefixEnd_1653288 377302846360281216354077 := by
  unfold tailWord_1653288
  simp only [CollatzResearch.WordTrace]
  refine ⟨30150183617213704977876259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40200244822951606637168345 30150183617213704977876259)
  ·
    refine ⟨45225275425820557466814389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30150183617213704977876259 45225275425820557466814389)
    ·
      refine ⟨4239869571170677262513849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45225275425820557466814389 4239869571170677262513849)
      ·
        refine ⟨3179902178378007946885387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4239869571170677262513849 3179902178378007946885387)
        ·
          refine ⟨4769853267567011920328081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3179902178378007946885387 4769853267567011920328081)
          ·
            refine ⟨3577389950675258940246061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4769853267567011920328081 3577389950675258940246061)
            ·
              refine ⟨1341521231503222102592273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3577389950675258940246061 1341521231503222102592273)
              ·
                refine ⟨1006140923627416576944205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1341521231503222102592273 1006140923627416576944205)
                ·
                  refine ⟨377302846360281216354077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1006140923627416576944205 377302846360281216354077)
                  ·
                    rfl

theorem cell21_1653288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2, 3].length) (baseStart_1653288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1653288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1653288 prefixEnd_1653288 := by exact prefixLift 1653288
  have htrace : WordTrace (prefixWord ++ tailWord_1653288) baseStart_1653288 baseEnd_1653288 := by
    simpa [prefixWord, tailWord_1653288, baseEnd_1653288] using wordTrace_append hprefix tailTrace_1653288
  have hstable : (prefixWord ++ tailWord_1653288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653288).length < 2 ^ (prefixWord ++ tailWord_1653288).sum := by decide
  have hdescent : baseEnd_1653288 < baseStart_1653288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653302 : List Nat := [5, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_1653302 : Nat := 118140960795 + 1653302 * 2 ^ 59
def prefixEnd_1653302 : Nat := 4983230072969 + 3 ^ 40 * 1653302 * 2
def baseEnd_1653302 : Nat := 377306041351020303120715

theorem tailTrace_1653302 : CollatzResearch.WordTrace tailWord_1653302 prefixEnd_1653302 377306041351020303120715 := by
  unfold tailWord_1653302
  simp only [CollatzResearch.WordTrace]
  refine ⟨3768804866023543146672635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40200585237584460231174773 3768804866023543146672635)
  ·
    refine ⟨5653207299035314720008953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3768804866023543146672635 5653207299035314720008953)
    ·
      refine ⟨4239905474276486040006715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5653207299035314720008953 4239905474276486040006715)
      ·
        refine ⟨6359858211414729060010073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4239905474276486040006715 6359858211414729060010073)
        ·
          refine ⟨4769893658561046795007555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6359858211414729060010073 4769893658561046795007555)
          ·
            refine ⟨7154840487841570192511333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4769893658561046795007555 7154840487841570192511333)
            ·
              refine ⟨1341532591470294411095875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7154840487841570192511333 1341532591470294411095875)
              ·
                refine ⟨2012298887205441616643813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1341532591470294411095875 2012298887205441616643813)
                ·
                  refine ⟨377306041351020303120715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2012298887205441616643813 377306041351020303120715)
                  ·
                    rfl

theorem cell21_1653302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_1653302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1653302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1653302 prefixEnd_1653302 := by exact prefixLift 1653302
  have htrace : WordTrace (prefixWord ++ tailWord_1653302) baseStart_1653302 baseEnd_1653302 := by
    simpa [prefixWord, tailWord_1653302, baseEnd_1653302] using wordTrace_append hprefix tailTrace_1653302
  have hstable : (prefixWord ++ tailWord_1653302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653302).length < 2 ^ (prefixWord ++ tailWord_1653302).sum := by decide
  have hdescent : baseEnd_1653302 < baseStart_1653302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653330 : List Nat := [3, 2, 2, 1, 2, 1, 2, 5, 3]
def baseStart_1653330 : Nat := 118140960795 + 1653330 * 2 ^ 59
def prefixEnd_1653330 : Nat := 4983230072969 + 3 ^ 40 * 1653330 * 2
def baseEnd_1653330 : Nat := 377312431332498476653991

theorem tailTrace_1653330 : CollatzResearch.WordTrace tailWord_1653330 prefixEnd_1653330 377312431332498476653991 := by
  unfold tailWord_1653330
  simp only [CollatzResearch.WordTrace]
  refine ⟨15075474775068812782195361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40201266066850167419187629 15075474775068812782195361)
  ·
    refine ⟨11306606081301609586646521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15075474775068812782195361 11306606081301609586646521)
    ·
      refine ⟨8479954560976207189984891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11306606081301609586646521 8479954560976207189984891)
      ·
        refine ⟨12719931841464310784977337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8479954560976207189984891 12719931841464310784977337)
        ·
          refine ⟨9539948881098233088733003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12719931841464310784977337 9539948881098233088733003)
          ·
            refine ⟨14309923321647349633099505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9539948881098233088733003 14309923321647349633099505)
            ·
              refine ⟨10732442491235512224824629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14309923321647349633099505 10732442491235512224824629)
              ·
                refine ⟨1006166483553329271077309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10732442491235512224824629 1006166483553329271077309)
                ·
                  refine ⟨377312431332498476653991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1006166483553329271077309 377312431332498476653991)
                  ·
                    rfl

theorem cell21_1653330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_1653330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1653330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1653330 prefixEnd_1653330 := by exact prefixLift 1653330
  have htrace : WordTrace (prefixWord ++ tailWord_1653330) baseStart_1653330 baseEnd_1653330 := by
    simpa [prefixWord, tailWord_1653330, baseEnd_1653330] using wordTrace_append hprefix tailTrace_1653330
  have hstable : (prefixWord ++ tailWord_1653330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653330).length < 2 ^ (prefixWord ++ tailWord_1653330).sum := by decide
  have hdescent : baseEnd_1653330 < baseStart_1653330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653372 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 7]
def baseStart_1653372 : Nat := 118140960795 + 1653372 * 2 ^ 59
def prefixEnd_1653372 : Nat := 4983230072969 + 3 ^ 40 * 1653372 * 2
def baseEnd_1653372 : Nat := 377322016304715736953905

theorem tailTrace_1653372 : CollatzResearch.WordTrace tailWord_1653372 prefixEnd_1653372 377322016304715736953905 := by
  unfold tailWord_1653372
  simp only [CollatzResearch.WordTrace]
  refine ⟨30151715483061546150905185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40202287310748728201206913 30151715483061546150905185)
  ·
    refine ⟨22613786612296159613178889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30151715483061546150905185 22613786612296159613178889)
    ·
      refine ⟨16960339959222119709884167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22613786612296159613178889 16960339959222119709884167)
      ·
        refine ⟨25440509938833179564826251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16960339959222119709884167 25440509938833179564826251)
        ·
          refine ⟨38160764908249769347239377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25440509938833179564826251 38160764908249769347239377)
          ·
            refine ⟨28620573681187327010429533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38160764908249769347239377 28620573681187327010429533)
            ·
              refine ⟨10732715130445247628911075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28620573681187327010429533 10732715130445247628911075)
              ·
                refine ⟨16099072695667871443366613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10732715130445247628911075 16099072695667871443366613)
                ·
                  refine ⟨377322016304715736953905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16099072695667871443366613 377322016304715736953905)
                  ·
                    rfl

theorem cell21_1653372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_1653372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1653372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1653372 prefixEnd_1653372 := by exact prefixLift 1653372
  have htrace : WordTrace (prefixWord ++ tailWord_1653372) baseStart_1653372 baseEnd_1653372 := by
    simpa [prefixWord, tailWord_1653372, baseEnd_1653372] using wordTrace_append hprefix tailTrace_1653372
  have hstable : (prefixWord ++ tailWord_1653372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653372).length < 2 ^ (prefixWord ++ tailWord_1653372).sum := by decide
  have hdescent : baseEnd_1653372 < baseStart_1653372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653406 : List Nat := [4, 3, 1, 1, 1, 1, 4, 1, 5]
def baseStart_1653406 : Nat := 118140960795 + 1653406 * 2 ^ 59
def prefixEnd_1653406 : Nat := 4983230072969 + 3 ^ 40 * 1653406 * 2
def baseEnd_1653406 : Nat := 377329775567939233387169

theorem tailTrace_1653406 : CollatzResearch.WordTrace tailWord_1653406 prefixEnd_1653406 377329775567939233387169 := by
  unfold tailWord_1653406
  simp only [CollatzResearch.WordTrace]
  refine ⟨7538083880999989513568509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40203114031999944072365381 7538083880999989513568509)
  ·
    refine ⟨2826781455374996067588191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7538083880999989513568509 2826781455374996067588191)
    ·
      refine ⟨4240172183062494101382287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2826781455374996067588191 4240172183062494101382287)
      ·
        refine ⟨6360258274593741152073431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4240172183062494101382287 6360258274593741152073431)
        ·
          refine ⟨9540387411890611728110147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6360258274593741152073431 9540387411890611728110147)
          ·
            refine ⟨14310581117835917592165221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9540387411890611728110147 14310581117835917592165221)
            ·
              refine ⟨2683233959594234548530979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14310581117835917592165221 2683233959594234548530979)
              ·
                refine ⟨4024850939391351822796469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2683233959594234548530979 4024850939391351822796469)
                ·
                  refine ⟨377329775567939233387169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4024850939391351822796469 377329775567939233387169)
                  ·
                    rfl

theorem cell21_1653406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_1653406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1653406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1653406 prefixEnd_1653406 := by exact prefixLift 1653406
  have htrace : WordTrace (prefixWord ++ tailWord_1653406) baseStart_1653406 baseEnd_1653406 := by
    simpa [prefixWord, tailWord_1653406, baseEnd_1653406] using wordTrace_append hprefix tailTrace_1653406
  have hstable : (prefixWord ++ tailWord_1653406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653406).length < 2 ^ (prefixWord ++ tailWord_1653406).sum := by decide
  have hdescent : baseEnd_1653406 < baseStart_1653406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653527 : List Nat := [1, 1, 3, 4, 3, 2, 1, 6]
def baseStart_1653527 : Nat := 118140960795 + 1653527 * 2 ^ 59
def prefixEnd_1653527 : Nat := 4983230072969 + 3 ^ 40 * 1653527 * 2
def baseEnd_1653527 : Nat := 125785796472156637290085

theorem tailTrace_1653527 : CollatzResearch.WordTrace tailWord_1653527 prefixEnd_1653527 125785796472156637290085 := by
  unfold tailWord_1653527
  simp only [CollatzResearch.WordTrace]
  refine ⟨60309084280561553773702835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40206056187041035849135223 60309084280561553773702835)
  ·
    refine ⟨90463626420842330660554253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60309084280561553773702835 90463626420842330660554253)
    ·
      refine ⟨33923859907815873997707845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90463626420842330660554253 33923859907815873997707845)
      ·
        refine ⟨6360723732715476374570221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33923859907815873997707845 6360723732715476374570221)
        ·
          refine ⟨2385271399768303640463833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6360723732715476374570221 2385271399768303640463833)
          ·
            refine ⟨1788953549826227730347875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2385271399768303640463833 1788953549826227730347875)
            ·
              refine ⟨2683430324739341595521813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1788953549826227730347875 2683430324739341595521813)
              ·
                refine ⟨125785796472156637290085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2683430324739341595521813 125785796472156637290085)
                ·
                  rfl

theorem cell21_1653527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 6].length) (baseStart_1653527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1653527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1653527 prefixEnd_1653527 := by exact prefixLift 1653527
  have htrace : WordTrace (prefixWord ++ tailWord_1653527) baseStart_1653527 baseEnd_1653527 := by
    simpa [prefixWord, tailWord_1653527, baseEnd_1653527] using wordTrace_append hprefix tailTrace_1653527
  have hstable : (prefixWord ++ tailWord_1653527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653527).length < 2 ^ (prefixWord ++ tailWord_1653527).sum := by decide
  have hdescent : baseEnd_1653527 < baseStart_1653527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653600 : List Nat := [2, 1, 1, 3, 3, 1, 1, 4, 5]
def baseStart_1653600 : Nat := 118140960795 + 1653600 * 2 ^ 59
def prefixEnd_1653600 : Nat := 4983230072969 + 3 ^ 40 * 1653600 * 2
def baseEnd_1653600 : Nat := 377374049011038007153439

theorem tailTrace_1653600 : CollatzResearch.WordTrace tailWord_1653600 prefixEnd_1653600 377374049011038007153439 := by
  unfold tailWord_1653600
  simp only [CollatzResearch.WordTrace]
  refine ⟨30155873404648543620555127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40207831206198058160740169 30155873404648543620555127)
  ·
    refine ⟨45233810106972815430832691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30155873404648543620555127 45233810106972815430832691)
    ·
      refine ⟨67850715160459223146249037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45233810106972815430832691 67850715160459223146249037)
      ·
        refine ⟨25444018185172208679843389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67850715160459223146249037 25444018185172208679843389)
        ·
          refine ⟨9541506819439578254941271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25444018185172208679843389 9541506819439578254941271)
          ·
            refine ⟨14312260229159367382411907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9541506819439578254941271 14312260229159367382411907)
            ·
              refine ⟨21468390343739051073617861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14312260229159367382411907 21468390343739051073617861)
              ·
                refine ⟨4025323189451072076303349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21468390343739051073617861 4025323189451072076303349)
                ·
                  refine ⟨377374049011038007153439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4025323189451072076303349 377374049011038007153439)
                  ·
                    rfl

theorem cell21_1653600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 5].length) (baseStart_1653600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1653600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1653600 prefixEnd_1653600 := by exact prefixLift 1653600
  have htrace : WordTrace (prefixWord ++ tailWord_1653600) baseStart_1653600 baseEnd_1653600 := by
    simpa [prefixWord, tailWord_1653600, baseEnd_1653600] using wordTrace_append hprefix tailTrace_1653600
  have hstable : (prefixWord ++ tailWord_1653600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653600).length < 2 ^ (prefixWord ++ tailWord_1653600).sum := by decide
  have hdescent : baseEnd_1653600 < baseStart_1653600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653603 : List Nat := [1, 1, 1, 5, 3, 3, 2, 5]
def baseStart_1653603 : Nat := 118140960795 + 1653603 * 2 ^ 59
def prefixEnd_1653603 : Nat := 4983230072969 + 3 ^ 40 * 1653603 * 2
def baseEnd_1653603 : Nat := 125791577883970222867811

theorem tailTrace_1653603 : CollatzResearch.WordTrace tailWord_1653603 prefixEnd_1653603 125791577883970222867811 := by
  unfold tailWord_1653603
  simp only [CollatzResearch.WordTrace]
  refine ⟨60311856228286218753469463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40207904152190812502312975 60311856228286218753469463)
  ·
    refine ⟨90467784342429328130204195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60311856228286218753469463 90467784342429328130204195)
    ·
      refine ⟨135701676513643992195306293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90467784342429328130204195 135701676513643992195306293)
      ·
        refine ⟨12722032173154124268309965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135701676513643992195306293 12722032173154124268309965)
        ·
          refine ⟨4770762064932796600616237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12722032173154124268309965 4770762064932796600616237)
          ·
            refine ⟨1789035774349798725231089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4770762064932796600616237 1789035774349798725231089)
            ·
              refine ⟨1341776830762349043923317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1789035774349798725231089 1341776830762349043923317)
              ·
                refine ⟨125791577883970222867811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1341776830762349043923317 125791577883970222867811)
                ·
                  rfl

theorem cell21_1653603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 5].length) (baseStart_1653603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1653603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1653603 prefixEnd_1653603 := by exact prefixLift 1653603
  have htrace : WordTrace (prefixWord ++ tailWord_1653603) baseStart_1653603 baseEnd_1653603 := by
    simpa [prefixWord, tailWord_1653603, baseEnd_1653603] using wordTrace_append hprefix tailTrace_1653603
  have hstable : (prefixWord ++ tailWord_1653603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653603).length < 2 ^ (prefixWord ++ tailWord_1653603).sum := by decide
  have hdescent : baseEnd_1653603 < baseStart_1653603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653707 : List Nat := [1, 1, 1, 1, 3, 5, 2, 3, 4]
def baseStart_1653707 : Nat := 118140960795 + 1653707 * 2 ^ 59
def prefixEnd_1653707 : Nat := 4983230072969 + 3 ^ 40 * 1653707 * 2
def baseEnd_1653707 : Nat := 377398467868829598869887

theorem tailTrace_1653707 : CollatzResearch.WordTrace tailWord_1653707 prefixEnd_1653707 377398467868829598869887 := by
  unfold tailWord_1653707
  simp only [CollatzResearch.WordTrace]
  refine ⟨60315649419909444515255375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40210432946606296343503583 60315649419909444515255375)
  ·
    refine ⟨90473474129864166772883063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60315649419909444515255375 90473474129864166772883063)
    ·
      refine ⟨135710211194796250159324595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90473474129864166772883063 135710211194796250159324595)
      ·
        refine ⟨203565316792194375238986893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135710211194796250159324595 203565316792194375238986893)
        ·
          refine ⟨76336993797072890714620085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203565316792194375238986893 76336993797072890714620085)
          ·
            refine ⟨7156593168475583504495633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76336993797072890714620085 7156593168475583504495633)
            ·
              refine ⟨5367444876356687628371725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7156593168475583504495633 5367444876356687628371725)
              ·
                refine ⟨2012791828633757860639397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5367444876356687628371725 2012791828633757860639397)
                ·
                  refine ⟨377398467868829598869887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2012791828633757860639397 377398467868829598869887)
                  ·
                    rfl

theorem cell21_1653707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 4].length) (baseStart_1653707 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1653707 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1653707 prefixEnd_1653707 := by exact prefixLift 1653707
  have htrace : WordTrace (prefixWord ++ tailWord_1653707) baseStart_1653707 baseEnd_1653707 := by
    simpa [prefixWord, tailWord_1653707, baseEnd_1653707] using wordTrace_append hprefix tailTrace_1653707
  have hstable : (prefixWord ++ tailWord_1653707).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653707).length < 2 ^ (prefixWord ++ tailWord_1653707).sum := by decide
  have hdescent : baseEnd_1653707 < baseStart_1653707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653758 : List Nat := [4, 2, 2, 2, 2, 1, 3, 1, 4]
def baseStart_1653758 : Nat := 118140960795 + 1653758 * 2 ^ 59
def prefixEnd_1653758 : Nat := 4983230072969 + 3 ^ 40 * 1653758 * 2
def baseEnd_1653758 : Nat := 377410106763664843519783

theorem tailTrace_1653758 : CollatzResearch.WordTrace tailWord_1653758 prefixEnd_1653758 377410106763664843519783 := by
  unfold tailWord_1653758
  simp only [CollatzResearch.WordTrace]
  refine ⟨7539688692840585028170241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40211673028483120150241285 7539688692840585028170241)
  ·
    refine ⟨5654766519630438771127681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7539688692840585028170241 5654766519630438771127681)
    ·
      refine ⟨4241074889722829078345761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5654766519630438771127681 4241074889722829078345761)
      ·
        refine ⟨3180806167292121808759321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4241074889722829078345761 3180806167292121808759321)
        ·
          refine ⟨2385604625469091356569491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3180806167292121808759321 2385604625469091356569491)
          ·
            refine ⟨3578406938203637034854237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2385604625469091356569491 3578406938203637034854237)
            ·
              refine ⟨1341902601826363888070339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3578406938203637034854237 1341902601826363888070339)
              ·
                refine ⟨2012853902739545832105509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1341902601826363888070339 2012853902739545832105509)
                ·
                  refine ⟨377410106763664843519783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2012853902739545832105509 377410106763664843519783)
                  ·
                    rfl

theorem cell21_1653758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_1653758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1653758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1653758 prefixEnd_1653758 := by exact prefixLift 1653758
  have htrace : WordTrace (prefixWord ++ tailWord_1653758) baseStart_1653758 baseEnd_1653758 := by
    simpa [prefixWord, tailWord_1653758, baseEnd_1653758] using wordTrace_append hprefix tailTrace_1653758
  have hstable : (prefixWord ++ tailWord_1653758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653758).length < 2 ^ (prefixWord ++ tailWord_1653758).sum := by decide
  have hdescent : baseEnd_1653758 < baseStart_1653758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653778 : List Nat := [3, 2, 5, 1, 2, 1, 1, 3, 3]
def baseStart_1653778 : Nat := 118140960795 + 1653778 * 2 ^ 59
def prefixEnd_1653778 : Nat := 4983230072969 + 3 ^ 40 * 1653778 * 2
def baseEnd_1653778 : Nat := 377414671036149253186409

theorem tailTrace_1653778 : CollatzResearch.WordTrace tailWord_1653778 prefixEnd_1653778 377414671036149253186409 := by
  unfold tailWord_1653778
  simp only [CollatzResearch.WordTrace]
  refine ⟨15079559750663055910272497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40212159335101482427393325 15079559750663055910272497)
  ·
    refine ⟨11309669812997291932704373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15079559750663055910272497 11309669812997291932704373)
    ·
      refine ⟨1060281544968496118691035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11309669812997291932704373 1060281544968496118691035)
      ·
        refine ⟨1590422317452744178036553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1060281544968496118691035 1590422317452744178036553)
        ·
          refine ⟨1192816738089558133527415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1590422317452744178036553 1192816738089558133527415)
          ·
            refine ⟨1789225107134337200291123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192816738089558133527415 1789225107134337200291123)
            ·
              refine ⟨2683837660701505800436685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1789225107134337200291123 2683837660701505800436685)
              ·
                refine ⟨1006439122763064675163757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2683837660701505800436685 1006439122763064675163757)
                ·
                  refine ⟨377414671036149253186409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1006439122763064675163757 377414671036149253186409)
                  ·
                    rfl

theorem cell21_1653778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_1653778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1653778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1653778 prefixEnd_1653778 := by exact prefixLift 1653778
  have htrace : WordTrace (prefixWord ++ tailWord_1653778) baseStart_1653778 baseEnd_1653778 := by
    simpa [prefixWord, tailWord_1653778, baseEnd_1653778] using wordTrace_append hprefix tailTrace_1653778
  have hstable : (prefixWord ++ tailWord_1653778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653778).length < 2 ^ (prefixWord ++ tailWord_1653778).sum := by decide
  have hdescent : baseEnd_1653778 < baseStart_1653778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653783 : List Nat := [1, 1, 3, 5, 1, 1, 1, 2, 6]
def baseStart_1653783 : Nat := 118140960795 + 1653783 * 2 ^ 59
def prefixEnd_1653783 : Nat := 4983230072969 + 3 ^ 40 * 1653783 * 2
def baseEnd_1653783 : Nat := 377415812104270355603065

theorem tailTrace_1653783 : CollatzResearch.WordTrace tailWord_1653783 prefixEnd_1653783 377415812104270355603065 := by
  unfold tailWord_1653783
  simp only [CollatzResearch.WordTrace]
  refine ⟨60318421367634109495022003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40212280911756072996681335 60318421367634109495022003)
  ·
    refine ⟨90477632051451164242533005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60318421367634109495022003 90477632051451164242533005)
    ·
      refine ⟨33929112019294186590949877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90477632051451164242533005 33929112019294186590949877)
      ·
        refine ⟨3180854251808829992901551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33929112019294186590949877 3180854251808829992901551)
        ·
          refine ⟨4771281377713244989352327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3180854251808829992901551 4771281377713244989352327)
          ·
            refine ⟨7156922066569867484028491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4771281377713244989352327 7156922066569867484028491)
            ·
              refine ⟨10735383099854801226042737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7156922066569867484028491 10735383099854801226042737)
              ·
                refine ⟨8051537324891100919532053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10735383099854801226042737 8051537324891100919532053)
                ·
                  refine ⟨377415812104270355603065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8051537324891100919532053 377415812104270355603065)
                  ·
                    rfl

theorem cell21_1653783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 6].length) (baseStart_1653783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1653783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1653783 prefixEnd_1653783 := by exact prefixLift 1653783
  have htrace : WordTrace (prefixWord ++ tailWord_1653783) baseStart_1653783 baseEnd_1653783 := by
    simpa [prefixWord, tailWord_1653783, baseEnd_1653783] using wordTrace_append hprefix tailTrace_1653783
  have hstable : (prefixWord ++ tailWord_1653783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653783).length < 2 ^ (prefixWord ++ tailWord_1653783).sum := by decide
  have hdescent : baseEnd_1653783 < baseStart_1653783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653814 : List Nat := [5, 1, 2, 1, 1, 2, 1, 8]
def baseStart_1653814 : Nat := 118140960795 + 1653814 * 2 ^ 59
def prefixEnd_1653814 : Nat := 4983230072969 + 3 ^ 40 * 1653814 * 2
def baseEnd_1653814 : Nat := 125807628908873730195445

theorem tailTrace_1653814 : CollatzResearch.WordTrace tailWord_1653814 prefixEnd_1653814 125807628908873730195445 := by
  unfold tailWord_1653814
  simp only [CollatzResearch.WordTrace]
  refine ⟨3769972001907612611837531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40213034687014534526266997 3769972001907612611837531)
  ·
    refine ⟨5654958002861418917756297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3769972001907612611837531 5654958002861418917756297)
    ·
      refine ⟨4241218502146064188317223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5654958002861418917756297 4241218502146064188317223)
      ·
        refine ⟨6361827753219096282475835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4241218502146064188317223 6361827753219096282475835)
        ·
          refine ⟨9542741629828644423713753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6361827753219096282475835 9542741629828644423713753)
          ·
            refine ⟨7157056222371483317785315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9542741629828644423713753 7157056222371483317785315)
            ·
              refine ⟨10735584333557224976677973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7157056222371483317785315 10735584333557224976677973)
              ·
                refine ⟨125807628908873730195445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10735584333557224976677973 125807628908873730195445)
                ·
                  rfl

theorem cell21_1653814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_1653814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1653814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1653814 prefixEnd_1653814 := by exact prefixLift 1653814
  have htrace : WordTrace (prefixWord ++ tailWord_1653814) baseStart_1653814 baseEnd_1653814 := by
    simpa [prefixWord, tailWord_1653814, baseEnd_1653814] using wordTrace_append hprefix tailTrace_1653814
  have hstable : (prefixWord ++ tailWord_1653814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653814).length < 2 ^ (prefixWord ++ tailWord_1653814).sum := by decide
  have hdescent : baseEnd_1653814 < baseStart_1653814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653817 : List Nat := [1, 2, 1, 5, 2, 3, 2, 1, 4]
def baseStart_1653817 : Nat := 118140960795 + 1653817 * 2 ^ 59
def prefixEnd_1653817 : Nat := 4983230072969 + 3 ^ 40 * 1653817 * 2
def baseEnd_1653817 : Nat := 377423571367493852036329

theorem tailTrace_1653817 : CollatzResearch.WordTrace tailWord_1653817 prefixEnd_1653817 377423571367493852036329 := by
  unfold tailWord_1653817
  simp only [CollatzResearch.WordTrace]
  refine ⟨60319661449510933301759705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40213107633007288867839803 60319661449510933301759705)
  ·
    refine ⟨45239746087133199976319779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60319661449510933301759705 45239746087133199976319779)
    ·
      refine ⟨67859619130699799964479669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45239746087133199976319779 67859619130699799964479669)
      ·
        refine ⟨6361839293503106246669969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67859619130699799964479669 6361839293503106246669969)
        ·
          refine ⟨4771379470127329685002477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6361839293503106246669969 4771379470127329685002477)
          ·
            refine ⟨1789267301297748631875929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4771379470127329685002477 1789267301297748631875929)
            ·
              refine ⟨1341950475973311473906947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1789267301297748631875929 1341950475973311473906947)
              ·
                refine ⟨2012925713959967210860421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1341950475973311473906947 2012925713959967210860421)
                ·
                  refine ⟨377423571367493852036329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2012925713959967210860421 377423571367493852036329)
                  ·
                    rfl

theorem cell21_1653817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 4].length) (baseStart_1653817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1653817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1653817 prefixEnd_1653817 := by exact prefixLift 1653817
  have htrace : WordTrace (prefixWord ++ tailWord_1653817) baseStart_1653817 baseEnd_1653817 := by
    simpa [prefixWord, tailWord_1653817, baseEnd_1653817] using wordTrace_append hprefix tailTrace_1653817
  have hstable : (prefixWord ++ tailWord_1653817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653817).length < 2 ^ (prefixWord ++ tailWord_1653817).sum := by decide
  have hdescent : baseEnd_1653817 < baseStart_1653817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653845 : List Nat := [1, 3, 2, 2, 1, 2, 2, 5, 3]
def baseStart_1653845 : Nat := 118140960795 + 1653845 * 2 ^ 59
def prefixEnd_1653845 : Nat := 4983230072969 + 3 ^ 40 * 1653845 * 2
def baseEnd_1653845 : Nat := 377429961348972025569605

theorem tailTrace_1653845 : CollatzResearch.WordTrace tailWord_1653845 prefixEnd_1653845 377429961348972025569605 := by
  unfold tailWord_1653845
  simp only [CollatzResearch.WordTrace]
  refine ⟨60320682693409494083778989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40213788462272996055852659 60320682693409494083778989)
  ·
    refine ⟨22620256010028560281417121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60320682693409494083778989 22620256010028560281417121)
    ·
      refine ⟨16965192007521420211062841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22620256010028560281417121 16965192007521420211062841)
      ·
        refine ⟨12723894005641065158297131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16965192007521420211062841 12723894005641065158297131)
        ·
          refine ⟨19085841008461597737445697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12723894005641065158297131 19085841008461597737445697)
          ·
            refine ⟨14314380756346198303084273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19085841008461597737445697 14314380756346198303084273)
            ·
              refine ⟨10735785567259648727313205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14314380756346198303084273 10735785567259648727313205)
              ·
                refine ⟨1006479896930592068185613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10735785567259648727313205 1006479896930592068185613)
                ·
                  refine ⟨377429961348972025569605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1006479896930592068185613 377429961348972025569605)
                  ·
                    rfl

theorem cell21_1653845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5, 3].length) (baseStart_1653845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1653845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1653845 prefixEnd_1653845 := by exact prefixLift 1653845
  have htrace : WordTrace (prefixWord ++ tailWord_1653845) baseStart_1653845 baseEnd_1653845 := by
    simpa [prefixWord, tailWord_1653845, baseEnd_1653845] using wordTrace_append hprefix tailTrace_1653845
  have hstable : (prefixWord ++ tailWord_1653845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653845).length < 2 ^ (prefixWord ++ tailWord_1653845).sum := by decide
  have hdescent : baseEnd_1653845 < baseStart_1653845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653921 : List Nat := [1, 2, 3, 3, 1, 1, 1, 6, 3]
def baseStart_1653921 : Nat := 118140960795 + 1653921 * 2 ^ 59
def prefixEnd_1653921 : Nat := 4983230072969 + 3 ^ 40 * 1653921 * 2
def baseEnd_1653921 : Nat := 377447305584412782302783

theorem tailTrace_1653921 : CollatzResearch.WordTrace tailWord_1653921 prefixEnd_1653921 377447305584412782302783 := by
  unfold tailWord_1653921
  simp only [CollatzResearch.WordTrace]
  refine ⟨60323454641134159063545617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40215636427422772709030411 60323454641134159063545617)
  ·
    refine ⟨45242590980850619297659213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60323454641134159063545617 45242590980850619297659213)
    ·
      refine ⟨16965971617818982236622205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45242590980850619297659213 16965971617818982236622205)
      ·
        refine ⟨6362239356682118338733327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16965971617818982236622205 6362239356682118338733327)
        ·
          refine ⟨9543359035023177508099991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6362239356682118338733327 9543359035023177508099991)
          ·
            refine ⟨14315038552534766262149987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9543359035023177508099991 14315038552534766262149987)
            ·
              refine ⟨21472557828802149393224981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14315038552534766262149987 21472557828802149393224981)
              ·
                refine ⟨1006526148225100752807421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21472557828802149393224981 1006526148225100752807421)
                ·
                  refine ⟨377447305584412782302783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1006526148225100752807421 377447305584412782302783)
                  ·
                    rfl

theorem cell21_1653921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6, 3].length) (baseStart_1653921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1653921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1653921 prefixEnd_1653921 := by exact prefixLift 1653921
  have htrace : WordTrace (prefixWord ++ tailWord_1653921) baseStart_1653921 baseEnd_1653921 := by
    simpa [prefixWord, tailWord_1653921, baseEnd_1653921] using wordTrace_append hprefix tailTrace_1653921
  have hstable : (prefixWord ++ tailWord_1653921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653921).length < 2 ^ (prefixWord ++ tailWord_1653921).sum := by decide
  have hdescent : baseEnd_1653921 < baseStart_1653921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653966 : List Nat := [4, 1, 1, 1, 5, 2, 7]
def baseStart_1653966 : Nat := 118140960795 + 1653966 * 2 ^ 59
def prefixEnd_1653966 : Nat := 4983230072969 + 3 ^ 40 * 1653966 * 2
def baseEnd_1653966 : Nat := 41939730577500300450299

theorem tailTrace_1653966 : CollatzResearch.WordTrace tailWord_1653966 prefixEnd_1653966 41939730577500300450299 := by
  unfold tailWord_1653966
  simp only [CollatzResearch.WordTrace]
  refine ⟨7540636990746391468616719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40216730617314087832622501 7540636990746391468616719)
  ·
    refine ⟨11310955486119587202925079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7540636990746391468616719 11310955486119587202925079)
    ·
      refine ⟨16966433229179380804387619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11310955486119587202925079 16966433229179380804387619)
      ·
        refine ⟨25449649843769071206581429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16966433229179380804387619 25449649843769071206581429)
        ·
          refine ⟨2385904672853350425617009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25449649843769071206581429 2385904672853350425617009)
          ·
            refine ⟨1789428504640012819212757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2385904672853350425617009 1789428504640012819212757)
            ·
              refine ⟨41939730577500300450299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1789428504640012819212757 41939730577500300450299)
              ·
                rfl

theorem cell21_1653966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 7].length) (baseStart_1653966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1653966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1653966 prefixEnd_1653966 := by exact prefixLift 1653966
  have htrace : WordTrace (prefixWord ++ tailWord_1653966) baseStart_1653966 baseEnd_1653966 := by
    simpa [prefixWord, tailWord_1653966, baseEnd_1653966] using wordTrace_append hprefix tailTrace_1653966
  have hstable : (prefixWord ++ tailWord_1653966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653966).length < 2 ^ (prefixWord ++ tailWord_1653966).sum := by decide
  have hdescent : baseEnd_1653966 < baseStart_1653966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653972 : List Nat := [2, 4, 1, 4, 1, 1, 3, 2, 3]
def baseStart_1653972 : Nat := 118140960795 + 1653972 * 2 ^ 59
def prefixEnd_1653972 : Nat := 4983230072969 + 3 ^ 40 * 1653972 * 2
def baseEnd_1653972 : Nat := 377458944479248026952679

theorem tailTrace_1653972 : CollatzResearch.WordTrace tailWord_1653972 prefixEnd_1653972 377458944479248026952679 := by
  unfold tailWord_1653972
  simp only [CollatzResearch.WordTrace]
  refine ⟨30162657381974697386826085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40216876509299596515768113 30162657381974697386826085)
  ·
    refine ⟨5655498259120255760029891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30162657381974697386826085 5655498259120255760029891)
    ·
      refine ⟨8483247388680383640044837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5655498259120255760029891 8483247388680383640044837)
      ·
        refine ⟨1590608885377571932508407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8483247388680383640044837 1590608885377571932508407)
        ·
          refine ⟨2385913328066357898762611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1590608885377571932508407 2385913328066357898762611)
          ·
            refine ⟨3578869992099536848143917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2385913328066357898762611 3578869992099536848143917)
            ·
              refine ⟨1342076247037326318053969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3578869992099536848143917 1342076247037326318053969)
              ·
                refine ⟨1006557185277994738540477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1342076247037326318053969 1006557185277994738540477)
                ·
                  refine ⟨377458944479248026952679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1006557185277994738540477 377458944479248026952679)
                  ·
                    rfl

theorem cell21_1653972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_1653972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1653972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1653972 prefixEnd_1653972 := by exact prefixLift 1653972
  have htrace : WordTrace (prefixWord ++ tailWord_1653972) baseStart_1653972 baseEnd_1653972 := by
    simpa [prefixWord, tailWord_1653972, baseEnd_1653972] using wordTrace_append hprefix tailTrace_1653972
  have hstable : (prefixWord ++ tailWord_1653972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653972).length < 2 ^ (prefixWord ++ tailWord_1653972).sum := by decide
  have hdescent : baseEnd_1653972 < baseStart_1653972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654042 : List Nat := [3, 1, 1, 3, 3, 3, 1, 6]
def baseStart_1654042 : Nat := 118140960795 + 1654042 * 2 ^ 59
def prefixEnd_1654042 : Nat := 4983230072969 + 3 ^ 40 * 1654042 * 2
def baseEnd_1654042 : Nat := 125824973144314486928623

theorem tailTrace_1654042 : CollatzResearch.WordTrace tailWord_1654042 prefixEnd_1654042 125824973144314486928623 := by
  unfold tailWord_1654042
  simp only [CollatzResearch.WordTrace]
  refine ⟨15081966968423949182175095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40218578582463864485800253 15081966968423949182175095)
  ·
    refine ⟨22622950452635923773262643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15081966968423949182175095 22622950452635923773262643)
    ·
      refine ⟨33934425678953885659893965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22622950452635923773262643 33934425678953885659893965)
      ·
        refine ⟨12725409629607707122460237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33934425678953885659893965 12725409629607707122460237)
        ·
          refine ⟨4772028611102890170922589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12725409629607707122460237 4772028611102890170922589)
          ·
            refine ⟨1789510729163583814095971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4772028611102890170922589 1789510729163583814095971)
            ·
              refine ⟨2684266093745375721143957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1789510729163583814095971 2684266093745375721143957)
              ·
                refine ⟨125824973144314486928623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2684266093745375721143957 125824973144314486928623)
                ·
                  rfl

theorem cell21_1654042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 6].length) (baseStart_1654042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1654042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1654042 prefixEnd_1654042 := by exact prefixLift 1654042
  have htrace : WordTrace (prefixWord ++ tailWord_1654042) baseStart_1654042 baseEnd_1654042 := by
    simpa [prefixWord, tailWord_1654042, baseEnd_1654042] using wordTrace_append hprefix tailTrace_1654042
  have hstable : (prefixWord ++ tailWord_1654042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654042).length < 2 ^ (prefixWord ++ tailWord_1654042).sum := by decide
  have hdescent : baseEnd_1654042 < baseStart_1654042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654056 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 7]
def baseStart_1654056 : Nat := 118140960795 + 1654056 * 2 ^ 59
def prefixEnd_1654056 : Nat := 4983230072969 + 3 ^ 40 * 1654056 * 2
def baseEnd_1654056 : Nat := 377478114423682547552507

theorem tailTrace_1654056 : CollatzResearch.WordTrace tailWord_1654056 prefixEnd_1654056 377478114423682547552507 := by
  unfold tailWord_1654056
  simp only [CollatzResearch.WordTrace]
  refine ⟨30164189247822538559855011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40218918997096718079806681 30164189247822538559855011)
  ·
    refine ⟨45246283871733807839782517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30164189247822538559855011 45246283871733807839782517)
    ·
      refine ⟨4241839112975044484979611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45246283871733807839782517 4241839112975044484979611)
      ·
        refine ⟨6362758669462566727469417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4241839112975044484979611 6362758669462566727469417)
        ·
          refine ⟨4772069002096925045602063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6362758669462566727469417 4772069002096925045602063)
          ·
            refine ⟨7158103503145387568403095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4772069002096925045602063 7158103503145387568403095)
            ·
              refine ⟨10737155254718081352604643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7158103503145387568403095 10737155254718081352604643)
              ·
                refine ⟨16105732882077122028906965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10737155254718081352604643 16105732882077122028906965)
                ·
                  refine ⟨377478114423682547552507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16105732882077122028906965 377478114423682547552507)
                  ·
                    rfl

theorem cell21_1654056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 7].length) (baseStart_1654056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1654056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1654056 prefixEnd_1654056 := by exact prefixLift 1654056
  have htrace : WordTrace (prefixWord ++ tailWord_1654056) baseStart_1654056 baseEnd_1654056 := by
    simpa [prefixWord, tailWord_1654056, baseEnd_1654056] using wordTrace_append hprefix tailTrace_1654056
  have hstable : (prefixWord ++ tailWord_1654056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654056).length < 2 ^ (prefixWord ++ tailWord_1654056).sum := by decide
  have hdescent : baseEnd_1654056 < baseStart_1654056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654087 : List Nat := [1, 1, 4, 1, 2, 3, 3, 2, 4]
def baseStart_1654087 : Nat := 118140960795 + 1654087 * 2 ^ 59
def prefixEnd_1654087 : Nat := 4983230072969 + 3 ^ 40 * 1654087 * 2
def baseEnd_1654087 : Nat := 377485189046033382535777

theorem tailTrace_1654087 : CollatzResearch.WordTrace tailWord_1654087 prefixEnd_1654087 377485189046033382535777 := by
  unfold tailWord_1654087
  simp only [CollatzResearch.WordTrace]
  refine ⟨60329509158532769414088515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40219672772355179609392343 60329509158532769414088515)
  ·
    refine ⟨90494263737799154121132773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60329509158532769414088515 90494263737799154121132773)
    ·
      refine ⟨16967674450837341397712395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90494263737799154121132773 16967674450837341397712395)
      ·
        refine ⟨25451511676256012096568593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16967674450837341397712395 25451511676256012096568593)
        ·
          refine ⟨19088633757192009072426445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25451511676256012096568593 19088633757192009072426445)
          ·
            refine ⟨7158237658947003402159917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19088633757192009072426445 7158237658947003402159917)
            ·
              refine ⟨2684339122105126275809969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7158237658947003402159917 2684339122105126275809969)
              ·
                refine ⟨2013254341578844706857477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2684339122105126275809969 2013254341578844706857477)
                ·
                  refine ⟨377485189046033382535777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2013254341578844706857477 377485189046033382535777)
                  ·
                    rfl

theorem cell21_1654087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 4].length) (baseStart_1654087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1654087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1654087 prefixEnd_1654087 := by exact prefixLift 1654087
  have htrace : WordTrace (prefixWord ++ tailWord_1654087) baseStart_1654087 baseEnd_1654087 := by
    simpa [prefixWord, tailWord_1654087, baseEnd_1654087] using wordTrace_append hprefix tailTrace_1654087
  have hstable : (prefixWord ++ tailWord_1654087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654087).length < 2 ^ (prefixWord ++ tailWord_1654087).sum := by decide
  have hdescent : baseEnd_1654087 < baseStart_1654087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654329 : List Nat := [1, 2, 1, 5, 1, 3, 2, 6]
def baseStart_1654329 : Nat := 118140960795 + 1654329 * 2 ^ 59
def prefixEnd_1654329 : Nat := 4983230072969 + 3 ^ 40 * 1654329 * 2
def baseEnd_1654329 : Nat := 125846805581031579833983

theorem tailTrace_1654329 : CollatzResearch.WordTrace tailWord_1654329 prefixEnd_1654329 125846805581031579833983 := by
  unfold tailWord_1654329
  simp only [CollatzResearch.WordTrace]
  refine ⟨60338335623656044744398041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40225557082437363162932027 60338335623656044744398041)
  ·
    refine ⟨45253751717742033558298531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60338335623656044744398041 45253751717742033558298531)
    ·
      refine ⟨67880627576613050337447797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45253751717742033558298531 67880627576613050337447797)
      ·
        refine ⟨6363808835307473469135731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67880627576613050337447797 6363808835307473469135731)
        ·
          refine ⟨9545713252961210203703597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6363808835307473469135731 9545713252961210203703597)
          ·
            refine ⟨3579642469860453826388849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9545713252961210203703597 3579642469860453826388849)
            ·
              refine ⟨2684731852395340369791637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3579642469860453826388849 2684731852395340369791637)
              ·
                refine ⟨125846805581031579833983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2684731852395340369791637 125846805581031579833983)
                ·
                  rfl

theorem cell21_1654329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 6].length) (baseStart_1654329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1654329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1654329 prefixEnd_1654329 := by exact prefixLift 1654329
  have htrace : WordTrace (prefixWord ++ tailWord_1654329) baseStart_1654329 baseEnd_1654329 := by
    simpa [prefixWord, tailWord_1654329, baseEnd_1654329] using wordTrace_append hprefix tailTrace_1654329
  have hstable : (prefixWord ++ tailWord_1654329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654329).length < 2 ^ (prefixWord ++ tailWord_1654329).sum := by decide
  have hdescent : baseEnd_1654329 < baseStart_1654329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654360 : List Nat := [2, 1, 2, 2, 1, 2, 1, 7, 3]
def baseStart_1654360 : Nat := 118140960795 + 1654360 * 2 ^ 59
def prefixEnd_1654360 : Nat := 4983230072969 + 3 ^ 40 * 1654360 * 2
def baseEnd_1654360 : Nat := 377547491365445574485219

theorem tailTrace_1654360 : CollatzResearch.WordTrace tailWord_1654360 prefixEnd_1654360 377547491365445574485219 := by
  unfold tailWord_1654360
  simp only [CollatzResearch.WordTrace]
  refine ⟨30169733143271868519388267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40226310857695824692517689 30169733143271868519388267)
  ·
    refine ⟨45254599714907802779082401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30169733143271868519388267 45254599714907802779082401)
    ·
      refine ⟨33940949786180852084311801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45254599714907802779082401 33940949786180852084311801)
      ·
        refine ⟨25455712339635639063233851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33940949786180852084311801 25455712339635639063233851)
        ·
          refine ⟨38183568509453458594850777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25455712339635639063233851 38183568509453458594850777)
          ·
            refine ⟨28637676382090093946138083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38183568509453458594850777 28637676382090093946138083)
            ·
              refine ⟨42956514573135140919207125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28637676382090093946138083 42956514573135140919207125)
              ·
                refine ⟨1006793310307854865293917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 42956514573135140919207125 1006793310307854865293917)
                ·
                  refine ⟨377547491365445574485219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1006793310307854865293917 377547491365445574485219)
                  ·
                    rfl

theorem cell21_1654360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7, 3].length) (baseStart_1654360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1654360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1654360 prefixEnd_1654360 := by exact prefixLift 1654360
  have htrace : WordTrace (prefixWord ++ tailWord_1654360) baseStart_1654360 baseEnd_1654360 := by
    simpa [prefixWord, tailWord_1654360, baseEnd_1654360] using wordTrace_append hprefix tailTrace_1654360
  have hstable : (prefixWord ++ tailWord_1654360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654360).length < 2 ^ (prefixWord ++ tailWord_1654360).sum := by decide
  have hdescent : baseEnd_1654360 < baseStart_1654360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654377 : List Nat := [1, 2, 1, 1, 1, 4, 6, 2, 3]
def baseStart_1654377 : Nat := 118140960795 + 1654377 * 2 ^ 59
def prefixEnd_1654377 : Nat := 4983230072969 + 3 ^ 40 * 1654377 * 2
def baseEnd_1654377 : Nat := 377551370997057322701851

theorem tailTrace_1654377 : CollatzResearch.WordTrace tailWord_1654377 prefixEnd_1654377 377551370997057322701851 := by
  unfold tailWord_1654377
  simp only [CollatzResearch.WordTrace]
  refine ⟨60340086327482148942145385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40226724218321432628096923 60340086327482148942145385)
  ·
    refine ⟨45255064745611611706609039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60340086327482148942145385 45255064745611611706609039)
    ·
      refine ⟨67882597118417417559913559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45255064745611611706609039 67882597118417417559913559)
      ·
        refine ⟨101823895677626126339870339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67882597118417417559913559 101823895677626126339870339)
        ·
          refine ⟨152735843516439189509805509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101823895677626126339870339 152735843516439189509805509)
          ·
            refine ⟨28637970659332348033088533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152735843516439189509805509 28637970659332348033088533)
            ·
              refine ⟨1342404874656203814051025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28637970659332348033088533 1342404874656203814051025)
              ·
                refine ⟨1006803655992152860538269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1342404874656203814051025 1006803655992152860538269)
                ·
                  refine ⟨377551370997057322701851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1006803655992152860538269 377551370997057322701851)
                  ·
                    rfl

theorem cell21_1654377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2, 3].length) (baseStart_1654377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1654377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1654377 prefixEnd_1654377 := by exact prefixLift 1654377
  have htrace : WordTrace (prefixWord ++ tailWord_1654377) baseStart_1654377 baseEnd_1654377 := by
    simpa [prefixWord, tailWord_1654377, baseEnd_1654377] using wordTrace_append hprefix tailTrace_1654377
  have hstable : (prefixWord ++ tailWord_1654377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654377).length < 2 ^ (prefixWord ++ tailWord_1654377).sum := by decide
  have hdescent : baseEnd_1654377 < baseStart_1654377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654405 : List Nat := [1, 3, 1, 1, 4, 1, 5, 5]
def baseStart_1654405 : Nat := 118140960795 + 1654405 * 2 ^ 59
def prefixEnd_1654405 : Nat := 4983230072969 + 3 ^ 40 * 1654405 * 2
def baseEnd_1654405 : Nat := 125852586992845165411709

theorem tailTrace_1654405 : CollatzResearch.WordTrace tailWord_1654405 prefixEnd_1654405 125852586992845165411709 := by
  unfold tailWord_1654405
  simp only [CollatzResearch.WordTrace]
  refine ⟨60341107571380709724164669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40227405047587139816109779 60341107571380709724164669)
  ·
    refine ⟨22627915339267766146561751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60341107571380709724164669 22627915339267766146561751)
    ·
      refine ⟨33941873008901649219842627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22627915339267766146561751 33941873008901649219842627)
      ·
        refine ⟨50912809513352473829763941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33941873008901649219842627 50912809513352473829763941)
        ·
          refine ⟨9546151783753588843080739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50912809513352473829763941 9546151783753588843080739)
          ·
            refine ⟨14319227675630383264621109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9546151783753588843080739 14319227675630383264621109)
            ·
              refine ⟨1342427594590348431058229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14319227675630383264621109 1342427594590348431058229)
              ·
                refine ⟨125852586992845165411709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1342427594590348431058229 125852586992845165411709)
                ·
                  rfl

theorem cell21_1654405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 5].length) (baseStart_1654405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1654405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1654405 prefixEnd_1654405 := by exact prefixLift 1654405
  have htrace : WordTrace (prefixWord ++ tailWord_1654405) baseStart_1654405 baseEnd_1654405 := by
    simpa [prefixWord, tailWord_1654405, baseEnd_1654405] using wordTrace_append hprefix tailTrace_1654405
  have hstable : (prefixWord ++ tailWord_1654405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654405).length < 2 ^ (prefixWord ++ tailWord_1654405).sum := by decide
  have hdescent : baseEnd_1654405 < baseStart_1654405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654436 : List Nat := [2, 3, 1, 2, 2, 3, 2, 1, 5]
def baseStart_1654436 : Nat := 118140960795 + 1654436 * 2 ^ 59
def prefixEnd_1654436 : Nat := 4983230072969 + 3 ^ 40 * 1654436 * 2
def baseEnd_1654436 : Nat := 377564835600886331218397

theorem tailTrace_1654436 : CollatzResearch.WordTrace tailWord_1654436 prefixEnd_1654436 377564835600886331218397 := by
  unfold tailWord_1654436
  simp only [CollatzResearch.WordTrace]
  refine ⟨30171119117134201009271581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40228158822845601345695441 30171119117134201009271581)
  ·
    refine ⟨11314169668925325378476843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30171119117134201009271581 11314169668925325378476843)
    ·
      refine ⟨16971254503387988067715265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11314169668925325378476843 16971254503387988067715265)
      ·
        refine ⟨12728440877540991050786449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16971254503387988067715265 12728440877540991050786449)
        ·
          refine ⟨9546330658155743288089837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12728440877540991050786449 9546330658155743288089837)
          ·
            refine ⟨3579873996808403733033689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9546330658155743288089837 3579873996808403733033689)
            ·
              refine ⟨2684905497606302799775267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3579873996808403733033689 2684905497606302799775267)
              ·
                refine ⟨4027358246409454199662901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2684905497606302799775267 4027358246409454199662901)
                ·
                  refine ⟨377564835600886331218397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4027358246409454199662901 377564835600886331218397)
                  ·
                    rfl

theorem cell21_1654436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_1654436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1654436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1654436 prefixEnd_1654436 := by exact prefixLift 1654436
  have htrace : WordTrace (prefixWord ++ tailWord_1654436) baseStart_1654436 baseEnd_1654436 := by
    simpa [prefixWord, tailWord_1654436, baseEnd_1654436] using wordTrace_append hprefix tailTrace_1654436
  have hstable : (prefixWord ++ tailWord_1654436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654436).length < 2 ^ (prefixWord ++ tailWord_1654436).sum := by decide
  have hdescent : baseEnd_1654436 < baseStart_1654436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654450 : List Nat := [3, 2, 1, 1, 1, 2, 2, 5, 4]
def baseStart_1654450 : Nat := 118140960795 + 1654450 * 2 ^ 59
def prefixEnd_1654450 : Nat := 4983230072969 + 3 ^ 40 * 1654450 * 2
def baseEnd_1654450 : Nat := 377568030591625417985035

theorem tailTrace_1654450 : CollatzResearch.WordTrace tailWord_1654450 prefixEnd_1654450 377568030591625417985035 := by
  unfold tailWord_1654450
  simp only [CollatzResearch.WordTrace]
  refine ⟨15085687214054420602388201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40228499237478454939701869 15085687214054420602388201)
  ·
    refine ⟨11314265410540815451791151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15085687214054420602388201 11314265410540815451791151)
    ·
      refine ⟨16971398115811223177686727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11314265410540815451791151 16971398115811223177686727)
      ·
        refine ⟨25457097173716834766530091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16971398115811223177686727 25457097173716834766530091)
        ·
          refine ⟨38185645760575252149795137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25457097173716834766530091 38185645760575252149795137)
          ·
            refine ⟨28639234320431439112346353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38185645760575252149795137 28639234320431439112346353)
            ·
              refine ⟨21479425740323579334259765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28639234320431439112346353 21479425740323579334259765)
              ·
                refine ⟨2013696163155335562586853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21479425740323579334259765 2013696163155335562586853)
                ·
                  refine ⟨377568030591625417985035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2013696163155335562586853 377568030591625417985035)
                  ·
                    rfl

theorem cell21_1654450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_1654450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1654450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1654450 prefixEnd_1654450 := by exact prefixLift 1654450
  have htrace : WordTrace (prefixWord ++ tailWord_1654450) baseStart_1654450 baseEnd_1654450 := by
    simpa [prefixWord, tailWord_1654450, baseEnd_1654450] using wordTrace_append hprefix tailTrace_1654450
  have hstable : (prefixWord ++ tailWord_1654450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654450).length < 2 ^ (prefixWord ++ tailWord_1654450).sum := by decide
  have hdescent : baseEnd_1654450 < baseStart_1654450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654464 : List Nat := [2, 1, 1, 2, 4, 1, 3, 7]
def baseStart_1654464 : Nat := 118140960795 + 1654464 * 2 ^ 59
def prefixEnd_1654464 : Nat := 4983230072969 + 3 ^ 40 * 1654464 * 2
def baseEnd_1654464 : Nat := 125857075194121501583891

theorem tailTrace_1654464 : CollatzResearch.WordTrace tailWord_1654464 prefixEnd_1654464 125857075194121501583891 := by
  unfold tailWord_1654464
  simp only [CollatzResearch.WordTrace]
  refine ⟨30171629739083481400281223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40228839652111308533708297 30171629739083481400281223)
  ·
    refine ⟨45257444608625222100421835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30171629739083481400281223 45257444608625222100421835)
    ·
      refine ⟨67886166912937833150632753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45257444608625222100421835 67886166912937833150632753)
      ·
        refine ⟨50914625184703374862974565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67886166912937833150632753 50914625184703374862974565)
        ·
          refine ⟨9546492222131882786807731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50914625184703374862974565 9546492222131882786807731)
          ·
            refine ⟨14319738333197824180211597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9546492222131882786807731 14319738333197824180211597)
            ·
              refine ⟨5369901874949184067579349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14319738333197824180211597 5369901874949184067579349)
              ·
                refine ⟨125857075194121501583891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5369901874949184067579349 125857075194121501583891)
                ·
                  rfl

theorem cell21_1654464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 7].length) (baseStart_1654464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1654464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1654464 prefixEnd_1654464 := by exact prefixLift 1654464
  have htrace : WordTrace (prefixWord ++ tailWord_1654464) baseStart_1654464 baseEnd_1654464 := by
    simpa [prefixWord, tailWord_1654464, baseEnd_1654464] using wordTrace_append hprefix tailTrace_1654464
  have hstable : (prefixWord ++ tailWord_1654464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654464).length < 2 ^ (prefixWord ++ tailWord_1654464).sum := by decide
  have hdescent : baseEnd_1654464 < baseStart_1654464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654546 : List Nat := [3, 2, 4, 1, 1, 2, 1, 4, 3]
def baseStart_1654546 : Nat := 118140960795 + 1654546 * 2 ^ 59
def prefixEnd_1654546 : Nat := 4983230072969 + 3 ^ 40 * 1654546 * 2
def baseEnd_1654546 : Nat := 377589939099550584384839

theorem tailTrace_1654546 : CollatzResearch.WordTrace tailWord_1654546 prefixEnd_1654546 377589939099550584384839 := by
  unfold tailWord_1654546
  simp only [CollatzResearch.WordTrace]
  refine ⟨15086562565967472701261873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40230833509246593870031661 15086562565967472701261873)
  ·
    refine ⟨11314921924475604525946405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15086562565967472701261873 11314921924475604525946405)
    ·
      refine ⟨2121547860839175848614951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11314921924475604525946405 2121547860839175848614951)
      ·
        refine ⟨3182321791258763772922427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2121547860839175848614951 3182321791258763772922427)
        ·
          refine ⟨4773482686888145659383641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3182321791258763772922427 4773482686888145659383641)
          ·
            refine ⟨3580112015166109244537731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4773482686888145659383641 3580112015166109244537731)
            ·
              refine ⟨5370168022749163866806597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3580112015166109244537731 5370168022749163866806597)
              ·
                refine ⟨1006906504265468225026237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5370168022749163866806597 1006906504265468225026237)
                ·
                  refine ⟨377589939099550584384839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1006906504265468225026237 377589939099550584384839)
                  ·
                    rfl

theorem cell21_1654546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_1654546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1654546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1654546 prefixEnd_1654546 := by exact prefixLift 1654546
  have htrace : WordTrace (prefixWord ++ tailWord_1654546) baseStart_1654546 baseEnd_1654546 := by
    simpa [prefixWord, tailWord_1654546, baseEnd_1654546] using wordTrace_append hprefix tailTrace_1654546
  have hstable : (prefixWord ++ tailWord_1654546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654546).length < 2 ^ (prefixWord ++ tailWord_1654546).sum := by decide
  have hdescent : baseEnd_1654546 < baseStart_1654546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654588 : List Nat := [2, 2, 2, 2, 1, 1, 3, 5, 3]
def baseStart_1654588 : Nat := 118140960795 + 1654588 * 2 ^ 59
def prefixEnd_1654588 : Nat := 4983230072969 + 3 ^ 40 * 1654588 * 2
def baseEnd_1654588 : Nat := 377599524071767844684753

theorem tailTrace_1654588 : CollatzResearch.WordTrace tailWord_1654588 prefixEnd_1654588 377599524071767844684753 := by
  unfold tailWord_1654588
  simp only [CollatzResearch.WordTrace]
  refine ⟨30173891064858865989038209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40231854753145154652050945 30173891064858865989038209)
  ·
    refine ⟨22630418298644149491778657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30173891064858865989038209 22630418298644149491778657)
    ·
      refine ⟨16972813723983112118833993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22630418298644149491778657 16972813723983112118833993)
      ·
        refine ⟨12729610292987334089125495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16972813723983112118833993 12729610292987334089125495)
        ·
          refine ⟨19094415439481001133688243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12729610292987334089125495 19094415439481001133688243)
          ·
            refine ⟨28641623159221501700532365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19094415439481001133688243 28641623159221501700532365)
            ·
              refine ⟨10740608684708063137699637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28641623159221501700532365 10740608684708063137699637)
              ·
                refine ⟨1006932064191380919159341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10740608684708063137699637 1006932064191380919159341)
                ·
                  refine ⟨377599524071767844684753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1006932064191380919159341 377599524071767844684753)
                  ·
                    rfl

theorem cell21_1654588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5, 3].length) (baseStart_1654588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1654588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1654588 prefixEnd_1654588 := by exact prefixLift 1654588
  have htrace : WordTrace (prefixWord ++ tailWord_1654588) baseStart_1654588 baseEnd_1654588 := by
    simpa [prefixWord, tailWord_1654588, baseEnd_1654588] using wordTrace_append hprefix tailTrace_1654588
  have hstable : (prefixWord ++ tailWord_1654588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654588).length < 2 ^ (prefixWord ++ tailWord_1654588).sum := by decide
  have hdescent : baseEnd_1654588 < baseStart_1654588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654605 : List Nat := [1, 6, 1, 2, 1, 2, 2, 1, 5]
def baseStart_1654605 : Nat := 118140960795 + 1654605 * 2 ^ 59
def prefixEnd_1654605 : Nat := 4983230072969 + 3 ^ 40 * 1654605 * 2
def baseEnd_1654605 : Nat := 377603403703379592901385

theorem tailTrace_1654605 : CollatzResearch.WordTrace tailWord_1654605 prefixEnd_1654605 377603403703379592901385 := by
  unfold tailWord_1654605
  simp only [CollatzResearch.WordTrace]
  refine ⟨60348402170656143881445269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40232268113770762587630179 60348402170656143881445269)
  ·
    refine ⟨2828831351749506744442747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 60348402170656143881445269 2828831351749506744442747)
    ·
      refine ⟨4243247027624260116664121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2828831351749506744442747 4243247027624260116664121)
      ·
        refine ⟨3182435270718195087498091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4243247027624260116664121 3182435270718195087498091)
        ·
          refine ⟨4773652906077292631247137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3182435270718195087498091 4773652906077292631247137)
          ·
            refine ⟨3580239679557969473435353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4773652906077292631247137 3580239679557969473435353)
            ·
              refine ⟨2685179759668477105076515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3580239679557969473435353 2685179759668477105076515)
              ·
                refine ⟨4027769639502715657614773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2685179759668477105076515 4027769639502715657614773)
                ·
                  refine ⟨377603403703379592901385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4027769639502715657614773 377603403703379592901385)
                  ·
                    rfl

theorem cell21_1654605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_1654605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1654605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1654605 prefixEnd_1654605 := by exact prefixLift 1654605
  have htrace : WordTrace (prefixWord ++ tailWord_1654605) baseStart_1654605 baseEnd_1654605 := by
    simpa [prefixWord, tailWord_1654605, baseEnd_1654605] using wordTrace_append hprefix tailTrace_1654605
  have hstable : (prefixWord ++ tailWord_1654605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654605).length < 2 ^ (prefixWord ++ tailWord_1654605).sum := by decide
  have hdescent : baseEnd_1654605 < baseStart_1654605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654661 : List Nat := [1, 3, 1, 1, 3, 2, 1, 3, 6]
def baseStart_1654661 : Nat := 118140960795 + 1654661 * 2 ^ 59
def prefixEnd_1654661 : Nat := 4983230072969 + 3 ^ 40 * 1654661 * 2
def baseEnd_1654661 : Nat := 377616183666335939967937

theorem tailTrace_1654661 : CollatzResearch.WordTrace tailWord_1654661 prefixEnd_1654661 377616183666335939967937 := by
  unfold tailWord_1654661
  simp only [CollatzResearch.WordTrace]
  refine ⟨60350444658453265445483837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40233629772302176963655891 60350444658453265445483837)
  ·
    refine ⟨22631416746919974542056439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60350444658453265445483837 22631416746919974542056439)
    ·
      refine ⟨33947125120379961813084659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22631416746919974542056439 33947125120379961813084659)
      ·
        refine ⟨50920687680569942719626989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33947125120379961813084659 50920687680569942719626989)
        ·
          refine ⟨19095257880213728519860121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50920687680569942719626989 19095257880213728519860121)
          ·
            refine ⟨14321443410160296389895091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19095257880213728519860121 14321443410160296389895091)
            ·
              refine ⟨21482165115240444584842637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14321443410160296389895091 21482165115240444584842637)
              ·
                refine ⟨8055811918215166719315989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21482165115240444584842637 8055811918215166719315989)
                ·
                  refine ⟨377616183666335939967937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8055811918215166719315989 377616183666335939967937)
                  ·
                    rfl

theorem cell21_1654661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_1654661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1654661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1654661 prefixEnd_1654661 := by exact prefixLift 1654661
  have htrace : WordTrace (prefixWord ++ tailWord_1654661) baseStart_1654661 baseEnd_1654661 := by
    simpa [prefixWord, tailWord_1654661, baseEnd_1654661] using wordTrace_append hprefix tailTrace_1654661
  have hstable : (prefixWord ++ tailWord_1654661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654661).length < 2 ^ (prefixWord ++ tailWord_1654661).sum := by decide
  have hdescent : baseEnd_1654661 < baseStart_1654661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654670 : List Nat := [4, 1, 1, 5, 2, 1, 2, 1, 4]
def baseStart_1654670 : Nat := 118140960795 + 1654670 * 2 ^ 59
def prefixEnd_1654670 : Nat := 4983230072969 + 3 ^ 40 * 1654670 * 2
def baseEnd_1654670 : Nat := 377618237588953924317919

theorem tailTrace_1654670 : CollatzResearch.WordTrace tailWord_1654670 prefixEnd_1654670 377618237588953924317919 := by
  unfold tailWord_1654670
  simp only [CollatzResearch.WordTrace]
  refine ⟨7543846614427582497820183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40233848610280439988374309 7543846614427582497820183)
  ·
    refine ⟨11315769921641373746730275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7543846614427582497820183 11315769921641373746730275)
    ·
      refine ⟨16973654882462060620095413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11315769921641373746730275 16973654882462060620095413)
      ·
        refine ⟨1591280145230818183133945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16973654882462060620095413 1591280145230818183133945)
        ·
          refine ⟨1193460108923113637350459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1591280145230818183133945 1193460108923113637350459)
          ·
            refine ⟨1790190163384670456025689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1193460108923113637350459 1790190163384670456025689)
            ·
              refine ⟨1342642622538502842019267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1790190163384670456025689 1342642622538502842019267)
              ·
                refine ⟨2013963933807754263028901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1342642622538502842019267 2013963933807754263028901)
                ·
                  refine ⟨377618237588953924317919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2013963933807754263028901 377618237588953924317919)
                  ·
                    rfl

theorem cell21_1654670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_1654670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1654670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1654670 prefixEnd_1654670 := by exact prefixLift 1654670
  have htrace : WordTrace (prefixWord ++ tailWord_1654670) baseStart_1654670 baseEnd_1654670 := by
    simpa [prefixWord, tailWord_1654670, baseEnd_1654670] using wordTrace_append hprefix tailTrace_1654670
  have hstable : (prefixWord ++ tailWord_1654670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654670).length < 2 ^ (prefixWord ++ tailWord_1654670).sum := by decide
  have hdescent : baseEnd_1654670 < baseStart_1654670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654692 : List Nat := [2, 3, 1, 2, 1, 3, 2, 7]
def baseStart_1654692 : Nat := 118140960795 + 1654692 * 2 ^ 59
def prefixEnd_1654692 : Nat := 4983230072969 + 3 ^ 40 * 1654692 * 2
def baseEnd_1654692 : Nat := 125874419429562258317069

theorem tailTrace_1654692 : CollatzResearch.WordTrace tailWord_1654692 prefixEnd_1654692 125874419429562258317069 := by
  unfold tailWord_1654692
  simp only [CollatzResearch.WordTrace]
  refine ⟨30175787660670478869931165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40234383547560638493241553 30175787660670478869931165)
  ·
    refine ⟨11315920372751429576224187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30175787660670478869931165 11315920372751429576224187)
    ·
      refine ⟨16973880559127144364336281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11315920372751429576224187 16973880559127144364336281)
      ·
        refine ⟨12730410419345358273252211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16973880559127144364336281 12730410419345358273252211)
        ·
          refine ⟨19095615629018037409878317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12730410419345358273252211 19095615629018037409878317)
          ·
            refine ⟨7160855860881764028704369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19095615629018037409878317 7160855860881764028704369)
            ·
              refine ⟨5370641895661323021528277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7160855860881764028704369 5370641895661323021528277)
              ·
                refine ⟨125874419429562258317069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5370641895661323021528277 125874419429562258317069)
                ·
                  rfl

theorem cell21_1654692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 7].length) (baseStart_1654692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1654692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1654692 prefixEnd_1654692 := by exact prefixLift 1654692
  have htrace : WordTrace (prefixWord ++ tailWord_1654692) baseStart_1654692 baseEnd_1654692 := by
    simpa [prefixWord, tailWord_1654692, baseEnd_1654692] using wordTrace_append hprefix tailTrace_1654692
  have hstable : (prefixWord ++ tailWord_1654692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654692).length < 2 ^ (prefixWord ++ tailWord_1654692).sum := by decide
  have hdescent : baseEnd_1654692 < baseStart_1654692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654830 : List Nat := [4, 1, 3, 1, 1, 2, 2, 1, 6]
def baseStart_1654830 : Nat := 118140960795 + 1654830 * 2 ^ 59
def prefixEnd_1654830 : Nat := 4983230072969 + 3 ^ 40 * 1654830 * 2
def baseEnd_1654830 : Nat := 377654751768829201650925

theorem tailTrace_1654830 : CollatzResearch.WordTrace tailWord_1654830 prefixEnd_1654830 377654751768829201650925 := by
  unfold tailWord_1654830
  simp only [CollatzResearch.WordTrace]
  refine ⟨7544576074355125913548243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40237739063227338205590629 7544576074355125913548243)
  ·
    refine ⟨11316864111532688870322365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7544576074355125913548243 11316864111532688870322365)
    ·
      refine ⟨4243824041824758326370887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11316864111532688870322365 4243824041824758326370887)
      ·
        refine ⟨6365736062737137489556331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4243824041824758326370887 6365736062737137489556331)
        ·
          refine ⟨9548604094105706234334497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6365736062737137489556331 9548604094105706234334497)
          ·
            refine ⟨7161453070579279675750873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9548604094105706234334497 7161453070579279675750873)
            ·
              refine ⟨5371089802934459756813155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7161453070579279675750873 5371089802934459756813155)
              ·
                refine ⟨8056634704401689635219733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5371089802934459756813155 8056634704401689635219733)
                ·
                  refine ⟨377654751768829201650925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8056634704401689635219733 377654751768829201650925)
                  ·
                    rfl

theorem cell21_1654830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_1654830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1654830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1654830 prefixEnd_1654830 := by exact prefixLift 1654830
  have htrace : WordTrace (prefixWord ++ tailWord_1654830) baseStart_1654830 baseEnd_1654830 := by
    simpa [prefixWord, tailWord_1654830, baseEnd_1654830] using wordTrace_append hprefix tailTrace_1654830
  have hstable : (prefixWord ++ tailWord_1654830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654830).length < 2 ^ (prefixWord ++ tailWord_1654830).sum := by decide
  have hdescent : baseEnd_1654830 < baseStart_1654830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654833 : List Nat := [1, 2, 2, 3, 1, 4, 3, 2, 3]
def baseStart_1654833 : Nat := 118140960795 + 1654833 * 2 ^ 59
def prefixEnd_1654833 : Nat := 4983230072969 + 3 ^ 40 * 1654833 * 2
def baseEnd_1654833 : Nat := 377655436409701863100919

theorem tailTrace_1654833 : CollatzResearch.WordTrace tailWord_1654833 prefixEnd_1654833 377655436409701863100919 := by
  unfold tailWord_1654833
  simp only [CollatzResearch.WordTrace]
  refine ⟨60356718013830138820745153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40237812009220092547163435 60356718013830138820745153)
  ·
    refine ⟨45267538510372604115558865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60356718013830138820745153 45267538510372604115558865)
    ·
      refine ⟨33950653882779453086669149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45267538510372604115558865 33950653882779453086669149)
      ·
        refine ⟨12731495206042294907500931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33950653882779453086669149 12731495206042294907500931)
        ·
          refine ⟨19097242809063442361251397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12731495206042294907500931 19097242809063442361251397)
          ·
            refine ⟨3580733026699395442734637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19097242809063442361251397 3580733026699395442734637)
            ·
              refine ⟨1342774885012273291025489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3580733026699395442734637 1342774885012273291025489)
              ·
                refine ⟨1007081163759204968269117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1342774885012273291025489 1007081163759204968269117)
                ·
                  refine ⟨377655436409701863100919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1007081163759204968269117 377655436409701863100919)
                  ·
                    rfl

theorem cell21_1654833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2, 3].length) (baseStart_1654833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1654833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1654833 prefixEnd_1654833 := by exact prefixLift 1654833
  have htrace : WordTrace (prefixWord ++ tailWord_1654833) baseStart_1654833 baseEnd_1654833 := by
    simpa [prefixWord, tailWord_1654833, baseEnd_1654833] using wordTrace_append hprefix tailTrace_1654833
  have hstable : (prefixWord ++ tailWord_1654833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654833).length < 2 ^ (prefixWord ++ tailWord_1654833).sum := by decide
  have hdescent : baseEnd_1654833 < baseStart_1654833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654844 : List Nat := [2, 2, 2, 2, 2, 1, 4, 6]
def baseStart_1654844 : Nat := 118140960795 + 1654844 * 2 ^ 59
def prefixEnd_1654844 : Nat := 4983230072969 + 3 ^ 40 * 1654844 * 2
def baseEnd_1654844 : Nat := 125885982253189429472521

theorem tailTrace_1654844 : CollatzResearch.WordTrace tailWord_1654844 prefixEnd_1654844 125885982253189429472521 := by
  unfold tailWord_1654844
  simp only [CollatzResearch.WordTrace]
  refine ⟨30178559608395143849697793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40238079477860191799597057 30178559608395143849697793)
  ·
    refine ⟨22633919706296357887273345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30178559608395143849697793 22633919706296357887273345)
    ·
      refine ⟨16975439779722268415455009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22633919706296357887273345 16975439779722268415455009)
      ·
        refine ⟨12731579834791701311591257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16975439779722268415455009 12731579834791701311591257)
        ·
          refine ⟨9548684876093775983693443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12731579834791701311591257 9548684876093775983693443)
          ·
            refine ⟨14323027314140663975540165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9548684876093775983693443 14323027314140663975540165)
            ·
              refine ⟨2685567621401374495413781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14323027314140663975540165 2685567621401374495413781)
              ·
                refine ⟨125885982253189429472521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2685567621401374495413781 125885982253189429472521)
                ·
                  rfl

theorem cell21_1654844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 6].length) (baseStart_1654844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1654844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1654844 prefixEnd_1654844 := by exact prefixLift 1654844
  have htrace : WordTrace (prefixWord ++ tailWord_1654844) baseStart_1654844 baseEnd_1654844 := by
    simpa [prefixWord, tailWord_1654844, baseEnd_1654844] using wordTrace_append hprefix tailTrace_1654844
  have hstable : (prefixWord ++ tailWord_1654844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654844).length < 2 ^ (prefixWord ++ tailWord_1654844).sum := by decide
  have hdescent : baseEnd_1654844 < baseStart_1654844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654858 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 7]
def baseStart_1654858 : Nat := 118140960795 + 1654858 * 2 ^ 59
def prefixEnd_1654858 : Nat := 4983230072969 + 3 ^ 40 * 1654858 * 2
def baseEnd_1654858 : Nat := 377661141750307375184201

theorem tailTrace_1654858 : CollatzResearch.WordTrace tailWord_1654858 prefixEnd_1654858 377661141750307375184201 := by
  unfold tailWord_1654858
  simp only [CollatzResearch.WordTrace]
  refine ⟨15089407459684892022601307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40238419892493045393603485 15089407459684892022601307)
  ·
    refine ⟨22634111189527338033901961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15089407459684892022601307 22634111189527338033901961)
    ·
      refine ⟨16975583392145503525426471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22634111189527338033901961 16975583392145503525426471)
      ·
        refine ⟨25463375088218255288139707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16975583392145503525426471 25463375088218255288139707)
        ·
          refine ⟨38195062632327382932209561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25463375088218255288139707 38195062632327382932209561)
          ·
            refine ⟨28646296974245537199157171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38195062632327382932209561 28646296974245537199157171)
            ·
              refine ⟨42969445461368305798735757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28646296974245537199157171 42969445461368305798735757)
              ·
                refine ⟨16113542048013114674525909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42969445461368305798735757 16113542048013114674525909)
                ·
                  refine ⟨377661141750307375184201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16113542048013114674525909 377661141750307375184201)
                  ·
                    rfl

theorem cell21_1654858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_1654858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1654858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1654858 prefixEnd_1654858 := by exact prefixLift 1654858
  have htrace : WordTrace (prefixWord ++ tailWord_1654858) baseStart_1654858 baseEnd_1654858 := by
    simpa [prefixWord, tailWord_1654858, baseEnd_1654858] using wordTrace_append hprefix tailTrace_1654858
  have hstable : (prefixWord ++ tailWord_1654858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654858).length < 2 ^ (prefixWord ++ tailWord_1654858).sum := by decide
  have hdescent : baseEnd_1654858 < baseStart_1654858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654878 : List Nat := [4, 4, 1, 1, 2, 9]
def baseStart_1654878 : Nat := 118140960795 + 1654878 * 2 ^ 59
def prefixEnd_1654878 : Nat := 4983230072969 + 3 ^ 40 * 1654878 * 2
def baseEnd_1654878 : Nat := 13987618741584880920401

theorem tailTrace_1654878 : CollatzResearch.WordTrace tailWord_1654878 prefixEnd_1654878 13987618741584880920401 := by
  unfold tailWord_1654878
  simp only [CollatzResearch.WordTrace]
  refine ⟨7544794912333388938266661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40238906199111407670755525 7544794912333388938266661)
  ·
    refine ⟨1414649046062510425924999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7544794912333388938266661 1414649046062510425924999)
    ·
      refine ⟨2121973569093765638887499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1414649046062510425924999 2121973569093765638887499)
      ·
        refine ⟨3182960353640648458331249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2121973569093765638887499 3182960353640648458331249)
        ·
          refine ⟨2387220265230486343748437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3182960353640648458331249 2387220265230486343748437)
          ·
            refine ⟨13987618741584880920401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2387220265230486343748437 13987618741584880920401)
            ·
              rfl

theorem cell21_1654878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 9].length) (baseStart_1654878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1654878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1654878 prefixEnd_1654878 := by exact prefixLift 1654878
  have htrace : WordTrace (prefixWord ++ tailWord_1654878) baseStart_1654878 baseEnd_1654878 := by
    simpa [prefixWord, tailWord_1654878, baseEnd_1654878] using wordTrace_append hprefix tailTrace_1654878
  have hstable : (prefixWord ++ tailWord_1654878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654878).length < 2 ^ (prefixWord ++ tailWord_1654878).sum := by decide
  have hdescent : baseEnd_1654878 < baseStart_1654878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654892 : List Nat := [2, 2, 1, 1, 3, 4, 1, 4, 3]
def baseStart_1654892 : Nat := 118140960795 + 1654892 * 2 ^ 59
def prefixEnd_1654892 : Nat := 4983230072969 + 3 ^ 40 * 1654892 * 2
def baseEnd_1654892 : Nat := 377668901013530871617465

theorem tailTrace_1654892 : CollatzResearch.WordTrace tailWord_1654892 prefixEnd_1654892 377668901013530871617465 := by
  unfold tailWord_1654892
  simp only [CollatzResearch.WordTrace]
  refine ⟨30179434960308195948571465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40239246613744261264761953 30179434960308195948571465)
  ·
    refine ⟨22634576220231146961428599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30179434960308195948571465 22634576220231146961428599)
    ·
      refine ⟨33951864330346720442142899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22634576220231146961428599 33951864330346720442142899)
      ·
        refine ⟨50927796495520080663214349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33951864330346720442142899 50927796495520080663214349)
        ·
          refine ⟨19097923685820030248705381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50927796495520080663214349 19097923685820030248705381)
          ·
            refine ⟨3580860691091255671632259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19097923685820030248705381 3580860691091255671632259)
            ·
              refine ⟨5371291036636883507448389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3580860691091255671632259 5371291036636883507448389)
              ·
                refine ⟨1007117069369415657646573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5371291036636883507448389 1007117069369415657646573)
                ·
                  refine ⟨377668901013530871617465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1007117069369415657646573 377668901013530871617465)
                  ·
                    rfl

theorem cell21_1654892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4, 3].length) (baseStart_1654892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1654892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1654892 prefixEnd_1654892 := by exact prefixLift 1654892
  have htrace : WordTrace (prefixWord ++ tailWord_1654892) baseStart_1654892 baseEnd_1654892 := by
    simpa [prefixWord, tailWord_1654892, baseEnd_1654892] using wordTrace_append hprefix tailTrace_1654892
  have hstable : (prefixWord ++ tailWord_1654892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654892).length < 2 ^ (prefixWord ++ tailWord_1654892).sum := by decide
  have hdescent : baseEnd_1654892 < baseStart_1654892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655072 : List Nat := [2, 1, 1, 5, 2, 1, 3, 6]
def baseStart_1655072 : Nat := 118140960795 + 1655072 * 2 ^ 59
def prefixEnd_1655072 : Nat := 4983230072969 + 3 ^ 40 * 1655072 * 2
def baseEnd_1655072 : Nat := 125903326488630186205699

theorem tailTrace_1655072 : CollatzResearch.WordTrace tailWord_1655072 prefixEnd_1655072 125903326488630186205699 := by
  unfold tailWord_1655072
  simp only [CollatzResearch.WordTrace]
  refine ⟨30182717529982141319347735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40243623373309521759130313 30182717529982141319347735)
  ·
    refine ⟨45274076294973211979021603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30182717529982141319347735 45274076294973211979021603)
    ·
      refine ⟨67911114442459817968532405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45274076294973211979021603 67911114442459817968532405)
      ·
        refine ⟨6366666978980607934549913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67911114442459817968532405 6366666978980607934549913)
        ·
          refine ⟨4775000234235455950912435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6366666978980607934549913 4775000234235455950912435)
          ·
            refine ⟨7162500351353183926368653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4775000234235455950912435 7162500351353183926368653)
            ·
              refine ⟨2685937631757443972388245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7162500351353183926368653 2685937631757443972388245)
              ·
                refine ⟨125903326488630186205699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2685937631757443972388245 125903326488630186205699)
                ·
                  rfl

theorem cell21_1655072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 6].length) (baseStart_1655072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1655072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1655072 prefixEnd_1655072 := by exact prefixLift 1655072
  have htrace : WordTrace (prefixWord ++ tailWord_1655072) baseStart_1655072 baseEnd_1655072 := by
    simpa [prefixWord, tailWord_1655072, baseEnd_1655072] using wordTrace_append hprefix tailTrace_1655072
  have hstable : (prefixWord ++ tailWord_1655072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655072).length < 2 ^ (prefixWord ++ tailWord_1655072).sum := by decide
  have hdescent : baseEnd_1655072 < baseStart_1655072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655089 : List Nat := [1, 2, 2, 3, 4, 1, 3, 5]
def baseStart_1655089 : Nat := 118140960795 + 1655089 * 2 ^ 59
def prefixEnd_1655089 : Nat := 4983230072969 + 3 ^ 40 * 1655089 * 2
def baseEnd_1655089 : Nat := 125904619699167435611243

theorem tailTrace_1655089 : CollatzResearch.WordTrace tailWord_1655089 prefixEnd_1655089 125904619699167435611243 := by
  unfold tailWord_1655089
  simp only [CollatzResearch.WordTrace]
  refine ⟨60366055100902694542064321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40244036733935129694709547 60366055100902694542064321)
  ·
    refine ⟨45274541325677020906548241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60366055100902694542064321 45274541325677020906548241)
    ·
      refine ⟨33955905994257765679911181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45274541325677020906548241 33955905994257765679911181)
      ·
        refine ⟨12733464747846662129966693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33955905994257765679911181 12733464747846662129966693)
        ·
          refine ⟨2387524640221249149368755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12733464747846662129966693 2387524640221249149368755)
          ·
            refine ⟨3581286960331873724053133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2387524640221249149368755 3581286960331873724053133)
            ·
              refine ⟨1342982610124452646519925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3581286960331873724053133 1342982610124452646519925)
              ·
                refine ⟨125904619699167435611243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1342982610124452646519925 125904619699167435611243)
                ·
                  rfl

theorem cell21_1655089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 5].length) (baseStart_1655089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1655089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1655089 prefixEnd_1655089 := by exact prefixLift 1655089
  have htrace : WordTrace (prefixWord ++ tailWord_1655089) baseStart_1655089 baseEnd_1655089 := by
    simpa [prefixWord, tailWord_1655089, baseEnd_1655089] using wordTrace_append hprefix tailTrace_1655089
  have hstable : (prefixWord ++ tailWord_1655089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655089).length < 2 ^ (prefixWord ++ tailWord_1655089).sum := by decide
  have hdescent : baseEnd_1655089 < baseStart_1655089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655148 : List Nat := [2, 2, 1, 1, 6, 1, 1, 7]
def baseStart_1655148 : Nat := 118140960795 + 1655148 * 2 ^ 59
def prefixEnd_1655148 : Nat := 4983230072969 + 3 ^ 40 * 1655148 * 2
def baseEnd_1655148 : Nat := 125909107900443771783425

theorem tailTrace_1655148 : CollatzResearch.WordTrace tailWord_1655148 prefixEnd_1655148 125909107900443771783425 := by
  unfold tailWord_1655148
  simp only [CollatzResearch.WordTrace]
  refine ⟨30184103503844473809231049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40245471338459298412308065 30184103503844473809231049)
  ·
    refine ⟨22638077627883355356923287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30184103503844473809231049 22638077627883355356923287)
    ·
      refine ⟨33957116441825033035384931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22638077627883355356923287 33957116441825033035384931)
      ·
        refine ⟨50935674662737549553077397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33957116441825033035384931 50935674662737549553077397)
        ·
          refine ⟨2387609749815822635300503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50935674662737549553077397 2387609749815822635300503)
          ·
            refine ⟨3581414624723733952950755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2387609749815822635300503 3581414624723733952950755)
            ·
              refine ⟨5372121937085600929426133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3581414624723733952950755 5372121937085600929426133)
              ·
                refine ⟨125909107900443771783425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5372121937085600929426133 125909107900443771783425)
                ·
                  rfl

theorem cell21_1655148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 7].length) (baseStart_1655148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1655148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1655148 prefixEnd_1655148 := by exact prefixLift 1655148
  have htrace : WordTrace (prefixWord ++ tailWord_1655148) baseStart_1655148 baseEnd_1655148 := by
    simpa [prefixWord, tailWord_1655148, baseEnd_1655148] using wordTrace_append hprefix tailTrace_1655148
  have hstable : (prefixWord ++ tailWord_1655148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655148).length < 2 ^ (prefixWord ++ tailWord_1655148).sum := by decide
  have hdescent : baseEnd_1655148 < baseStart_1655148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655179 : List Nat := [1, 1, 1, 1, 4, 6, 1, 1, 5]
def baseStart_1655179 : Nat := 118140960795 + 1655179 * 2 ^ 59
def prefixEnd_1655179 : Nat := 4983230072969 + 3 ^ 40 * 1655179 * 2
def baseEnd_1655179 : Nat := 377734398323682150333545

theorem tailTrace_1655179 : CollatzResearch.WordTrace tailWord_1655179 prefixEnd_1655179 377734398323682150333545 := by
  unfold tailWord_1655179
  simp only [CollatzResearch.WordTrace]
  refine ⟨60369337670576639912840591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40246225113717759941893727 60369337670576639912840591)
  ·
    refine ⟨90554006505864959869260887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60369337670576639912840591 90554006505864959869260887)
    ·
      refine ⟨135831009758797439803891331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90554006505864959869260887 135831009758797439803891331)
      ·
        refine ⟨203746514638196159705836997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135831009758797439803891331 203746514638196159705836997)
        ·
          refine ⟨38202471494661779944844437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203746514638196159705836997 38202471494661779944844437)
          ·
            refine ⟨1790740851312270934914583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38202471494661779944844437 1790740851312270934914583)
            ·
              refine ⟨2686111276968406402371875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1790740851312270934914583 2686111276968406402371875)
              ·
                refine ⟨4029166915452609603557813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2686111276968406402371875 4029166915452609603557813)
                ·
                  refine ⟨377734398323682150333545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4029166915452609603557813 377734398323682150333545)
                  ·
                    rfl

theorem cell21_1655179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 5].length) (baseStart_1655179 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1655179 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1655179 prefixEnd_1655179 := by exact prefixLift 1655179
  have htrace : WordTrace (prefixWord ++ tailWord_1655179) baseStart_1655179 baseEnd_1655179 := by
    simpa [prefixWord, tailWord_1655179, baseEnd_1655179] using wordTrace_append hprefix tailTrace_1655179
  have hstable : (prefixWord ++ tailWord_1655179).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655179).length < 2 ^ (prefixWord ++ tailWord_1655179).sum := by decide
  have hdescent : baseEnd_1655179 < baseStart_1655179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655193 : List Nat := [1, 2, 1, 2, 1, 4, 3, 3, 4]
def baseStart_1655193 : Nat := 118140960795 + 1655193 * 2 ^ 59
def prefixEnd_1655193 : Nat := 4983230072969 + 3 ^ 40 * 1655193 * 2
def baseEnd_1655193 : Nat := 377737593314421237100183

theorem tailTrace_1655193 : CollatzResearch.WordTrace tailWord_1655193 prefixEnd_1655193 377737593314421237100183 := by
  unfold tailWord_1655193
  simp only [CollatzResearch.WordTrace]
  refine ⟨60369848292525920303850233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40246565528350613535900155 60369848292525920303850233)
  ·
    refine ⟨45277386219394440227887675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60369848292525920303850233 45277386219394440227887675)
    ·
      refine ⟨67916079329091660341831513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45277386219394440227887675 67916079329091660341831513)
      ·
        refine ⟨50937059496818745256373635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67916079329091660341831513 50937059496818745256373635)
        ·
          refine ⟨76405589245228117884560453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50937059496818745256373635 76405589245228117884560453)
          ·
            refine ⟨14326047983480272103355085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76405589245228117884560453 14326047983480272103355085)
            ·
              refine ⟨5372267993805102038758157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14326047983480272103355085 5372267993805102038758157)
              ·
                refine ⟨2014600497676913264534309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5372267993805102038758157 2014600497676913264534309)
                ·
                  refine ⟨377737593314421237100183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2014600497676913264534309 377737593314421237100183)
                  ·
                    rfl

theorem cell21_1655193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 4].length) (baseStart_1655193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1655193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1655193 prefixEnd_1655193 := by exact prefixLift 1655193
  have htrace : WordTrace (prefixWord ++ tailWord_1655193) baseStart_1655193 baseEnd_1655193 := by
    simpa [prefixWord, tailWord_1655193, baseEnd_1655193] using wordTrace_append hprefix tailTrace_1655193
  have hstable : (prefixWord ++ tailWord_1655193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655193).length < 2 ^ (prefixWord ++ tailWord_1655193).sum := by decide
  have hdescent : baseEnd_1655193 < baseStart_1655193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655272 : List Nat := [2, 1, 4, 1, 1, 4, 2, 3, 3]
def baseStart_1655272 : Nat := 118140960795 + 1655272 * 2 ^ 59
def prefixEnd_1655272 : Nat := 4983230072969 + 3 ^ 40 * 1655272 * 2
def baseEnd_1655272 : Nat := 377755622190734655283355

theorem tailTrace_1655272 : CollatzResearch.WordTrace tailWord_1655272 prefixEnd_1655272 377755622190734655283355 := by
  unfold tailWord_1655272
  simp only [CollatzResearch.WordTrace]
  refine ⟨30186364829619858397988035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40248486439493144530650713 30186364829619858397988035)
  ·
    refine ⟨45279547244429787596982053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30186364829619858397988035 45279547244429787596982053)
    ·
      refine ⟨8489915108330585174434135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45279547244429787596982053 8489915108330585174434135)
      ·
        refine ⟨12734872662495877761651203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8489915108330585174434135 12734872662495877761651203)
        ·
          refine ⟨19102308993743816642476805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12734872662495877761651203 19102308993743816642476805)
          ·
            refine ⟨3581682936326965620464401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19102308993743816642476805 3581682936326965620464401)
            ·
              refine ⟨2686262202245224215348301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3581682936326965620464401 2686262202245224215348301)
              ·
                refine ⟨1007348325841959080755613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2686262202245224215348301 1007348325841959080755613)
                ·
                  refine ⟨377755622190734655283355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1007348325841959080755613 377755622190734655283355)
                  ·
                    rfl

theorem cell21_1655272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3, 3].length) (baseStart_1655272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1655272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1655272 prefixEnd_1655272 := by exact prefixLift 1655272
  have htrace : WordTrace (prefixWord ++ tailWord_1655272) baseStart_1655272 baseEnd_1655272 := by
    simpa [prefixWord, tailWord_1655272, baseEnd_1655272] using wordTrace_append hprefix tailTrace_1655272
  have hstable : (prefixWord ++ tailWord_1655272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655272).length < 2 ^ (prefixWord ++ tailWord_1655272).sum := by decide
  have hdescent : baseEnd_1655272 < baseStart_1655272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655303 : List Nat := [1, 1, 4, 3, 3, 1, 3, 1, 4]
def baseStart_1655303 : Nat := 118140960795 + 1655303 * 2 ^ 59
def prefixEnd_1655303 : Nat := 4983230072969 + 3 ^ 40 * 1655303 * 2
def baseEnd_1655303 : Nat := 377762696813085490266625

theorem tailTrace_1655303 : CollatzResearch.WordTrace tailWord_1655303 prefixEnd_1655303 377762696813085490266625 := by
  unfold tailWord_1655303
  simp only [CollatzResearch.WordTrace]
  refine ⟨60373860322127409090354563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40249240214751606060236375 60373860322127409090354563)
  ·
    refine ⟨90560790483191113635531845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60373860322127409090354563 90560790483191113635531845)
    ·
      refine ⟨16980148215598333806662221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90560790483191113635531845 16980148215598333806662221)
      ·
        refine ⟨6367555580849375177498333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16980148215598333806662221 6367555580849375177498333)
        ·
          refine ⟨2387833342818515691561875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6367555580849375177498333 2387833342818515691561875)
          ·
            refine ⟨3581750014227773537342813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2387833342818515691561875 3581750014227773537342813)
            ·
              refine ⟨1343156255335415076503555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3581750014227773537342813 1343156255335415076503555)
              ·
                refine ⟨2014734383003122614755333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1343156255335415076503555 2014734383003122614755333)
                ·
                  refine ⟨377762696813085490266625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2014734383003122614755333 377762696813085490266625)
                  ·
                    rfl

theorem cell21_1655303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 4].length) (baseStart_1655303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1655303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1655303 prefixEnd_1655303 := by exact prefixLift 1655303
  have htrace : WordTrace (prefixWord ++ tailWord_1655303) baseStart_1655303 baseEnd_1655303 := by
    simpa [prefixWord, tailWord_1655303, baseEnd_1655303] using wordTrace_append hprefix tailTrace_1655303
  have hstable : (prefixWord ++ tailWord_1655303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655303).length < 2 ^ (prefixWord ++ tailWord_1655303).sum := by decide
  have hdescent : baseEnd_1655303 < baseStart_1655303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655359 : List Nat := [1, 1, 2, 2, 3, 2, 4, 6]
def baseStart_1655359 : Nat := 118140960795 + 1655359 * 2 ^ 59
def prefixEnd_1655359 : Nat := 4983230072969 + 3 ^ 40 * 1655359 * 2
def baseEnd_1655359 : Nat := 125925158925347279111059

theorem tailTrace_1655359 : CollatzResearch.WordTrace tailWord_1655359 prefixEnd_1655359 125925158925347279111059 := by
  unfold tailWord_1655359
  simp only [CollatzResearch.WordTrace]
  refine ⟨60375902809924530654393131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40250601873283020436262087 60375902809924530654393131)
  ·
    refine ⟨90563854214886795981589697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60375902809924530654393131 90563854214886795981589697)
    ·
      refine ⟨67922890661165096986192273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90563854214886795981589697 67922890661165096986192273)
      ·
        refine ⟨50942167995873822739644205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67922890661165096986192273 50942167995873822739644205)
        ·
          refine ⟨19103312998452683527366577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50942167995873822739644205 19103312998452683527366577)
          ·
            refine ⟨14327484748839512645524933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19103312998452683527366577 14327484748839512645524933)
            ·
              refine ⟨2686403390407408621035925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14327484748839512645524933 2686403390407408621035925)
              ·
                refine ⟨125925158925347279111059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2686403390407408621035925 125925158925347279111059)
                ·
                  rfl

theorem cell21_1655359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 6].length) (baseStart_1655359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1655359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1655359 prefixEnd_1655359 := by exact prefixLift 1655359
  have htrace : WordTrace (prefixWord ++ tailWord_1655359) baseStart_1655359 baseEnd_1655359 := by
    simpa [prefixWord, tailWord_1655359, baseEnd_1655359] using wordTrace_append hprefix tailTrace_1655359
  have hstable : (prefixWord ++ tailWord_1655359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655359).length < 2 ^ (prefixWord ++ tailWord_1655359).sum := by decide
  have hdescent : baseEnd_1655359 < baseStart_1655359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655404 : List Nat := [2, 2, 1, 1, 3, 1, 2, 3, 6]
def baseStart_1655404 : Nat := 118140960795 + 1655404 * 2 ^ 59
def prefixEnd_1655404 : Nat := 4983230072969 + 3 ^ 40 * 1655404 * 2
def baseEnd_1655404 : Nat := 377785746389131759083085

theorem tailTrace_1655404 : CollatzResearch.WordTrace tailWord_1655404 prefixEnd_1655404 377785746389131759083085 := by
  unfold tailWord_1655404
  simp only [CollatzResearch.WordTrace]
  refine ⟨30188772047380751669890633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40251696063174335559854177 30188772047380751669890633)
  ·
    refine ⟨22641579035535563752417975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30188772047380751669890633 22641579035535563752417975)
    ·
      refine ⟨33962368553303345628626963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22641579035535563752417975 33962368553303345628626963)
      ·
        refine ⟨50943552829955018442940445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33962368553303345628626963 50943552829955018442940445)
        ·
          refine ⟨19103832311233131916102667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50943552829955018442940445 19103832311233131916102667)
          ·
            refine ⟨28655748466849697874154001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19103832311233131916102667 28655748466849697874154001)
            ·
              refine ⟨21491811350137273405615501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28655748466849697874154001 21491811350137273405615501)
              ·
                refine ⟨8059429256301477527105813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21491811350137273405615501 8059429256301477527105813)
                ·
                  refine ⟨377785746389131759083085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8059429256301477527105813 377785746389131759083085)
                  ·
                    rfl

theorem cell21_1655404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_1655404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1655404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1655404 prefixEnd_1655404 := by exact prefixLift 1655404
  have htrace : WordTrace (prefixWord ++ tailWord_1655404) baseStart_1655404 baseEnd_1655404 := by
    simpa [prefixWord, tailWord_1655404, baseEnd_1655404] using wordTrace_append hprefix tailTrace_1655404
  have hstable : (prefixWord ++ tailWord_1655404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655404).length < 2 ^ (prefixWord ++ tailWord_1655404).sum := by decide
  have hdescent : baseEnd_1655404 < baseStart_1655404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655449 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 7]
def baseStart_1655449 : Nat := 118140960795 + 1655449 * 2 ^ 59
def prefixEnd_1655449 : Nat := 4983230072969 + 3 ^ 40 * 1655449 * 2
def baseEnd_1655449 : Nat := 377796016002221680832993

theorem tailTrace_1655449 : CollatzResearch.WordTrace tailWord_1655449 prefixEnd_1655449 377796016002221680832993 := by
  unfold tailWord_1655449
  simp only [CollatzResearch.WordTrace]
  refine ⟨60379185379598476025169401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40252790253065650683446267 60379185379598476025169401)
  ·
    refine ⟨45284389034698857018877051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60379185379598476025169401 45284389034698857018877051)
    ·
      refine ⟨67926583552048285528315577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45284389034698857018877051 67926583552048285528315577)
      ·
        refine ⟨50944937664036214146236683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67926583552048285528315577 50944937664036214146236683)
        ·
          refine ⟨76417406496054321219355025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50944937664036214146236683 76417406496054321219355025)
          ·
            refine ⟨57313054872040740914516269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76417406496054321219355025 57313054872040740914516269)
            ·
              refine ⟨21492395577015277842943601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57313054872040740914516269 21492395577015277842943601)
              ·
                refine ⟨16119296682761458382207701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21492395577015277842943601 16119296682761458382207701)
                ·
                  refine ⟨377796016002221680832993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16119296682761458382207701 377796016002221680832993)
                  ·
                    rfl

theorem cell21_1655449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_1655449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1655449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1655449 prefixEnd_1655449 := by exact prefixLift 1655449
  have htrace : WordTrace (prefixWord ++ tailWord_1655449) baseStart_1655449 baseEnd_1655449 := by
    simpa [prefixWord, tailWord_1655449, baseEnd_1655449] using wordTrace_append hprefix tailTrace_1655449
  have hstable : (prefixWord ++ tailWord_1655449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655449).length < 2 ^ (prefixWord ++ tailWord_1655449).sum := by decide
  have hdescent : baseEnd_1655449 < baseStart_1655449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655500 : List Nat := [2, 2, 1, 5, 1, 1, 3, 3, 3]
def baseStart_1655500 : Nat := 118140960795 + 1655500 * 2 ^ 59
def prefixEnd_1655500 : Nat := 4983230072969 + 3 ^ 40 * 1655500 * 2
def baseEnd_1655500 : Nat := 377807654897056925482889

theorem tailTrace_1655500 : CollatzResearch.WordTrace tailWord_1655500 prefixEnd_1655500 377807654897056925482889 := by
  unfold tailWord_1655500
  simp only [CollatzResearch.WordTrace]
  refine ⟨30190522751206855867637977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40254030334942474490183969 30190522751206855867637977)
  ·
    refine ⟨22642892063405141900728483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30190522751206855867637977 22642892063405141900728483)
    ·
      refine ⟨33964338095107712851092725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22642892063405141900728483 33964338095107712851092725)
      ·
        refine ⟨3184156696416348079789943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33964338095107712851092725 3184156696416348079789943)
        ·
          refine ⟨4776235044624522119684915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3184156696416348079789943 4776235044624522119684915)
          ·
            refine ⟨7164352566936783179527373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4776235044624522119684915 7164352566936783179527373)
            ·
              refine ⟨2686632212601293692322765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7164352566936783179527373 2686632212601293692322765)
              ·
                refine ⟨1007487079725485134621037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2686632212601293692322765 1007487079725485134621037)
                ·
                  refine ⟨377807654897056925482889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1007487079725485134621037 377807654897056925482889)
                  ·
                    rfl

theorem cell21_1655500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3, 3].length) (baseStart_1655500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1655500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1655500 prefixEnd_1655500 := by exact prefixLift 1655500
  have htrace : WordTrace (prefixWord ++ tailWord_1655500) baseStart_1655500 baseEnd_1655500 := by
    simpa [prefixWord, tailWord_1655500, baseEnd_1655500] using wordTrace_append hprefix tailTrace_1655500
  have hstable : (prefixWord ++ tailWord_1655500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655500).length < 2 ^ (prefixWord ++ tailWord_1655500).sum := by decide
  have hdescent : baseEnd_1655500 < baseStart_1655500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655511 : List Nat := [1, 1, 3, 2, 1, 6, 7]
def baseStart_1655511 : Nat := 118140960795 + 1655511 * 2 ^ 59
def prefixEnd_1655511 : Nat := 4983230072969 + 3 ^ 40 * 1655511 * 2
def baseEnd_1655511 : Nat := 41978907249658150088837

theorem tailTrace_1655511 : CollatzResearch.WordTrace tailWord_1655511 prefixEnd_1655511 41978907249658150088837 := by
  unfold tailWord_1655511
  simp only [CollatzResearch.WordTrace]
  refine ⟨60381446705373860613926387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40254297803582573742617591 60381446705373860613926387)
  ·
    refine ⟨90572170058060790920889581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60381446705373860613926387 90572170058060790920889581)
    ·
      refine ⟨33964563771772796595333593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90572170058060790920889581 33964563771772796595333593)
      ·
        refine ⟨25473422828829597446500195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33964563771772796595333593 25473422828829597446500195)
        ·
          refine ⟨38210134243244396169750293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25473422828829597446500195 38210134243244396169750293)
          ·
            refine ⟨1791100042652081070457045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38210134243244396169750293 1791100042652081070457045)
            ·
              refine ⟨41978907249658150088837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1791100042652081070457045 41978907249658150088837)
              ·
                rfl

theorem cell21_1655511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 7].length) (baseStart_1655511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1655511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1655511 prefixEnd_1655511 := by exact prefixLift 1655511
  have htrace : WordTrace (prefixWord ++ tailWord_1655511) baseStart_1655511 baseEnd_1655511 := by
    simpa [prefixWord, tailWord_1655511, baseEnd_1655511] using wordTrace_append hprefix tailTrace_1655511
  have hstable : (prefixWord ++ tailWord_1655511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655511).length < 2 ^ (prefixWord ++ tailWord_1655511).sum := by decide
  have hdescent : baseEnd_1655511 < baseStart_1655511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655528 : List Nat := [2, 1, 4, 1, 4, 1, 2, 6]
def baseStart_1655528 : Nat := 118140960795 + 1655528 * 2 ^ 59
def prefixEnd_1655528 : Nat := 4983230072969 + 3 ^ 40 * 1655528 * 2
def baseEnd_1655528 : Nat := 125938014959511699672055

theorem tailTrace_1655528 : CollatzResearch.WordTrace tailWord_1655528 prefixEnd_1655528 125938014959511699672055 := by
  unfold tailWord_1655528
  simp only [CollatzResearch.WordTrace]
  refine ⟨30191033373156136258647619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40254711164208181678196825 30191033373156136258647619)
  ·
    refine ⟨45286550059734204387971429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30191033373156136258647619 45286550059734204387971429)
    ·
      refine ⟨8491228136200163322744643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45286550059734204387971429 8491228136200163322744643)
      ·
        refine ⟨12736842204300244984116965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8491228136200163322744643 12736842204300244984116965)
        ·
          refine ⟨2388157913306295934521931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12736842204300244984116965 2388157913306295934521931)
          ·
            refine ⟨3582236869959443901782897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2388157913306295934521931 3582236869959443901782897)
            ·
              refine ⟨2686677652469582926337173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3582236869959443901782897 2686677652469582926337173)
              ·
                refine ⟨125938014959511699672055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2686677652469582926337173 125938014959511699672055)
                ·
                  rfl

theorem cell21_1655528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 6].length) (baseStart_1655528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1655528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1655528 prefixEnd_1655528 := by exact prefixLift 1655528
  have htrace : WordTrace (prefixWord ++ tailWord_1655528) baseStart_1655528 baseEnd_1655528 := by
    simpa [prefixWord, tailWord_1655528, baseEnd_1655528] using wordTrace_append hprefix tailTrace_1655528
  have hstable : (prefixWord ++ tailWord_1655528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655528).length < 2 ^ (prefixWord ++ tailWord_1655528).sum := by decide
  have hdescent : baseEnd_1655528 < baseStart_1655528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655542 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_1655542 : Nat := 118140960795 + 1655542 * 2 ^ 59
def prefixEnd_1655542 : Nat := 4983230072969 + 3 ^ 40 * 1655542 * 2
def baseEnd_1655542 : Nat := 377817239869274185782803

theorem tailTrace_1655542 : CollatzResearch.WordTrace tailWord_1655542 prefixEnd_1655542 377817239869274185782803 := by
  unfold tailWord_1655542
  simp only [CollatzResearch.WordTrace]
  refine ⟨3773911085516347056769055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40255051578841035272203253 3773911085516347056769055)
  ·
    refine ⟨5660866628274520585153583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3773911085516347056769055 5660866628274520585153583)
    ·
      refine ⟨8491299942411780877730375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5660866628274520585153583 8491299942411780877730375)
      ·
        refine ⟨12736949913617671316595563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8491299942411780877730375 12736949913617671316595563)
        ·
          refine ⟨19105424870426506974893345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12736949913617671316595563 19105424870426506974893345)
          ·
            refine ⟨14329068652819880231170009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19105424870426506974893345 14329068652819880231170009)
            ·
              refine ⟨10746801489614910173377507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14329068652819880231170009 10746801489614910173377507)
              ·
                refine ⟨16120202234422365260066261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10746801489614910173377507 16120202234422365260066261)
                ·
                  refine ⟨377817239869274185782803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16120202234422365260066261 377817239869274185782803)
                  ·
                    rfl

theorem cell21_1655542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_1655542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1655542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1655542 prefixEnd_1655542 := by exact prefixLift 1655542
  have htrace : WordTrace (prefixWord ++ tailWord_1655542) baseStart_1655542 baseEnd_1655542 := by
    simpa [prefixWord, tailWord_1655542, baseEnd_1655542] using wordTrace_append hprefix tailTrace_1655542
  have hstable : (prefixWord ++ tailWord_1655542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655542).length < 2 ^ (prefixWord ++ tailWord_1655542).sum := by decide
  have hdescent : baseEnd_1655542 < baseStart_1655542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655573 : List Nat := [1, 3, 2, 1, 2, 2, 4, 2, 4]
def baseStart_1655573 : Nat := 118140960795 + 1655573 * 2 ^ 59
def prefixEnd_1655573 : Nat := 4983230072969 + 3 ^ 40 * 1655573 * 2
def baseEnd_1655573 : Nat := 377824314491625020766073

theorem tailTrace_1655573 : CollatzResearch.WordTrace tailWord_1655573 prefixEnd_1655573 377824314491625020766073 := by
  unfold tailWord_1655573
  simp only [CollatzResearch.WordTrace]
  refine ⟨60383708031149245202683373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40255805354099496801788915 60383708031149245202683373)
  ·
    refine ⟨22643890511680966951006265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60383708031149245202683373 22643890511680966951006265)
    ·
      refine ⟨16982917883760725213254699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22643890511680966951006265 16982917883760725213254699)
      ·
        refine ⟨25474376825641087819882049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16982917883760725213254699 25474376825641087819882049)
        ·
          refine ⟨19105782619230815864911537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25474376825641087819882049 19105782619230815864911537)
          ·
            refine ⟨14329336964423111898683653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19105782619230815864911537 14329336964423111898683653)
            ·
              refine ⟨2686750680829333481003185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14329336964423111898683653 2686750680829333481003185)
              ·
                refine ⟨2015063010622000110752389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2686750680829333481003185 2015063010622000110752389)
                ·
                  refine ⟨377824314491625020766073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2015063010622000110752389 377824314491625020766073)
                  ·
                    rfl

theorem cell21_1655573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_1655573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1655573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1655573 prefixEnd_1655573 := by exact prefixLift 1655573
  have htrace : WordTrace (prefixWord ++ tailWord_1655573) baseStart_1655573 baseEnd_1655573 := by
    simpa [prefixWord, tailWord_1655573, baseEnd_1655573] using wordTrace_append hprefix tailTrace_1655573
  have hstable : (prefixWord ++ tailWord_1655573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655573).length < 2 ^ (prefixWord ++ tailWord_1655573).sum := by decide
  have hdescent : baseEnd_1655573 < baseStart_1655573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655677 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 7]
def baseStart_1655677 : Nat := 118140960795 + 1655677 * 2 ^ 59
def prefixEnd_1655677 : Nat := 4983230072969 + 3 ^ 40 * 1655677 * 2
def baseEnd_1655677 : Nat := 377848048708543951032527

theorem tailTrace_1655677 : CollatzResearch.WordTrace tailWord_1655677 prefixEnd_1655677 377848048708543951032527 := by
  unfold tailWord_1655677
  simp only [CollatzResearch.WordTrace]
  refine ⟨60387501222772470964469285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40258334148514980642979523 60387501222772470964469285)
  ·
    refine ⟨11322656479269838305837991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60387501222772470964469285 11322656479269838305837991)
    ·
      refine ⟨16983984718904757458756987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11322656479269838305837991 16983984718904757458756987)
      ·
        refine ⟨25475977078357136188135481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16983984718904757458756987 25475977078357136188135481)
        ·
          refine ⟨19106982808767852141101611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25475977078357136188135481 19106982808767852141101611)
          ·
            refine ⟨28660474213151778211652417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19106982808767852141101611 28660474213151778211652417)
            ·
              refine ⟨21495355659863833658739313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28660474213151778211652417 21495355659863833658739313)
              ·
                refine ⟨16121516744897875244054485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21495355659863833658739313 16121516744897875244054485)
                ·
                  refine ⟨377848048708543951032527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16121516744897875244054485 377848048708543951032527)
                  ·
                    rfl

theorem cell21_1655677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_1655677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1655677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1655677 prefixEnd_1655677 := by exact prefixLift 1655677
  have htrace : WordTrace (prefixWord ++ tailWord_1655677) baseStart_1655677 baseEnd_1655677 := by
    simpa [prefixWord, tailWord_1655677, baseEnd_1655677] using wordTrace_append hprefix tailTrace_1655677
  have hstable : (prefixWord ++ tailWord_1655677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655677).length < 2 ^ (prefixWord ++ tailWord_1655677).sum := by decide
  have hdescent : baseEnd_1655677 < baseStart_1655677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655770 : List Nat := [3, 1, 1, 2, 4, 2, 1, 2, 5]
def baseStart_1655770 : Nat := 118140960795 + 1655770 * 2 ^ 59
def prefixEnd_1655770 : Nat := 4983230072969 + 3 ^ 40 * 1655770 * 2
def baseEnd_1655770 : Nat := 377869272575596455982337

theorem tailTrace_1655770 : CollatzResearch.WordTrace tailWord_1655770 prefixEnd_1655770 377869272575596455982337 := by
  unfold tailWord_1655770
  simp only [CollatzResearch.WordTrace]
  refine ⟨15097723302858886961901191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40260595474290365231736509 15097723302858886961901191)
  ·
    refine ⟨22646584954288330442851787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15097723302858886961901191 22646584954288330442851787)
    ·
      refine ⟨33969877431432495664277681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22646584954288330442851787 33969877431432495664277681)
      ·
        refine ⟨25477408073574371748208261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33969877431432495664277681 25477408073574371748208261)
        ·
          refine ⟨4777014013795194702789049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25477408073574371748208261 4777014013795194702789049)
          ·
            refine ⟨3582760510346396027091787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4777014013795194702789049 3582760510346396027091787)
            ·
              refine ⟨5374140765519594040637681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3582760510346396027091787 5374140765519594040637681)
              ·
                refine ⟨4030605574139695530478261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5374140765519594040637681 4030605574139695530478261)
                ·
                  refine ⟨377869272575596455982337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4030605574139695530478261 377869272575596455982337)
                  ·
                    rfl

theorem cell21_1655770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_1655770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1655770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1655770 prefixEnd_1655770 := by exact prefixLift 1655770
  have htrace : WordTrace (prefixWord ++ tailWord_1655770) baseStart_1655770 baseEnd_1655770 := by
    simpa [prefixWord, tailWord_1655770, baseEnd_1655770] using wordTrace_append hprefix tailTrace_1655770
  have hstable : (prefixWord ++ tailWord_1655770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655770).length < 2 ^ (prefixWord ++ tailWord_1655770).sum := by decide
  have hdescent : baseEnd_1655770 < baseStart_1655770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655818 : List Nat := [3, 1, 2, 2, 3, 2, 3, 1, 4]
def baseStart_1655818 : Nat := 118140960795 + 1655818 * 2 ^ 59
def prefixEnd_1655818 : Nat := 4983230072969 + 3 ^ 40 * 1655818 * 2
def baseEnd_1655818 : Nat := 377880226829559039182239

theorem tailTrace_1655818 : CollatzResearch.WordTrace tailWord_1655818 prefixEnd_1655818 377880226829559039182239 := by
  unfold tailWord_1655818
  simp only [CollatzResearch.WordTrace]
  refine ⟨15098160978815413011338027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40261762610174434696901405 15098160978815413011338027)
  ·
    refine ⟨22647241468223119517007041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15098160978815413011338027 22647241468223119517007041)
    ·
      refine ⟨16985431101167339637755281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22647241468223119517007041 16985431101167339637755281)
      ·
        refine ⟨12739073325875504728316461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16985431101167339637755281 12739073325875504728316461)
        ·
          refine ⟨4777152497203314273118673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12739073325875504728316461 4777152497203314273118673)
          ·
            refine ⟨3582864372902485704839005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4777152497203314273118673 3582864372902485704839005)
            ·
              refine ⟨1343574139838432139314627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3582864372902485704839005 1343574139838432139314627)
              ·
                refine ⟨2015361209757648208971941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1343574139838432139314627 2015361209757648208971941)
                ·
                  refine ⟨377880226829559039182239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2015361209757648208971941 377880226829559039182239)
                  ·
                    rfl

theorem cell21_1655818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_1655818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1655818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1655818 prefixEnd_1655818 := by exact prefixLift 1655818
  have htrace : WordTrace (prefixWord ++ tailWord_1655818) baseStart_1655818 baseEnd_1655818 := by
    simpa [prefixWord, tailWord_1655818, baseEnd_1655818] using wordTrace_append hprefix tailTrace_1655818
  have hstable : (prefixWord ++ tailWord_1655818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655818).length < 2 ^ (prefixWord ++ tailWord_1655818).sum := by decide
  have hdescent : baseEnd_1655818 < baseStart_1655818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655832 : List Nat := [2, 1, 2, 3, 2, 4, 2, 5]
def baseStart_1655832 : Nat := 118140960795 + 1655832 * 2 ^ 59
def prefixEnd_1655832 : Nat := 4983230072969 + 3 ^ 40 * 1655832 * 2
def baseEnd_1655832 : Nat := 125961140606766041982959

theorem tailTrace_1655832 : CollatzResearch.WordTrace tailWord_1655832 prefixEnd_1655832 125961140606766041982959 := by
  unfold tailWord_1655832
  simp only [CollatzResearch.WordTrace]
  refine ⟨30196577268605466218180875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40262103024807288290907833 30196577268605466218180875)
  ·
    refine ⟨45294865902908199327271313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30196577268605466218180875 45294865902908199327271313)
    ·
      refine ⟨33971149427181149495453485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45294865902908199327271313 33971149427181149495453485)
      ·
        refine ⟨12739181035192931060795057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33971149427181149495453485 12739181035192931060795057)
        ·
          refine ⟨9554385776394698295596293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12739181035192931060795057 9554385776394698295596293)
          ·
            refine ⟨1791447333074005930424305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9554385776394698295596293 1791447333074005930424305)
            ·
              refine ⟨1343585499805504447818229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1791447333074005930424305 1343585499805504447818229)
              ·
                refine ⟨125961140606766041982959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1343585499805504447818229 125961140606766041982959)
                ·
                  rfl

theorem cell21_1655832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 5].length) (baseStart_1655832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1655832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1655832 prefixEnd_1655832 := by exact prefixLift 1655832
  have htrace : WordTrace (prefixWord ++ tailWord_1655832) baseStart_1655832 baseEnd_1655832 := by
    simpa [prefixWord, tailWord_1655832, baseEnd_1655832] using wordTrace_append hprefix tailTrace_1655832
  have hstable : (prefixWord ++ tailWord_1655832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655832).length < 2 ^ (prefixWord ++ tailWord_1655832).sum := by decide
  have hdescent : baseEnd_1655832 < baseStart_1655832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655877 : List Nat := [1, 3, 1, 1, 1, 3, 6, 1, 4]
def baseStart_1655877 : Nat := 118140960795 + 1655877 * 2 ^ 59
def prefixEnd_1655877 : Nat := 4983230072969 + 3 ^ 40 * 1655877 * 2
def baseEnd_1655877 : Nat := 377893691433388047698785

theorem tailTrace_1655877 : CollatzResearch.WordTrace tailWord_1655877 prefixEnd_1655877 377893691433388047698785 := by
  unfold tailWord_1655877
  simp only [CollatzResearch.WordTrace]
  refine ⟨60394795822047905121749885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40263197214698603414499923 60394795822047905121749885)
  ·
    refine ⟨22648048433267964420656207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60394795822047905121749885 22648048433267964420656207)
    ·
      refine ⟨33972072649901946630984311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22648048433267964420656207 33972072649901946630984311)
      ·
        refine ⟨50958108974852919946476467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33972072649901946630984311 50958108974852919946476467)
        ·
          refine ⟨76437163462279379919714701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50958108974852919946476467 76437163462279379919714701)
          ·
            refine ⟨28663936298354767469893013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76437163462279379919714701 28663936298354767469893013)
            ·
              refine ⟨1343622013985379725151235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28663936298354767469893013 1343622013985379725151235)
              ·
                refine ⟨2015433020978069587726853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1343622013985379725151235 2015433020978069587726853)
                ·
                  refine ⟨377893691433388047698785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2015433020978069587726853 377893691433388047698785)
                  ·
                    rfl

theorem cell21_1655877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_1655877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1655877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1655877 prefixEnd_1655877 := by exact prefixLift 1655877
  have htrace : WordTrace (prefixWord ++ tailWord_1655877) baseStart_1655877 baseEnd_1655877 := by
    simpa [prefixWord, tailWord_1655877, baseEnd_1655877] using wordTrace_append hprefix tailTrace_1655877
  have hstable : (prefixWord ++ tailWord_1655877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655877).length < 2 ^ (prefixWord ++ tailWord_1655877).sum := by decide
  have hdescent : baseEnd_1655877 < baseStart_1655877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655925 : List Nat := [1, 3, 4, 3, 1, 2, 1, 6]
def baseStart_1655925 : Nat := 118140960795 + 1655925 * 2 ^ 59
def prefixEnd_1655925 : Nat := 4983230072969 + 3 ^ 40 * 1655925 * 2
def baseEnd_1655925 : Nat := 125968215229116876966229

theorem tailTrace_1655925 : CollatzResearch.WordTrace tailWord_1655925 prefixEnd_1655925 125968215229116876966229 := by
  unfold tailWord_1655925
  simp only [CollatzResearch.WordTrace]
  refine ⟨60396546525874009319497229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40264364350582672879664819 60396546525874009319497229)
  ·
    refine ⟨22648704947202753494811461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60396546525874009319497229 22648704947202753494811461)
    ·
      refine ⟨4246632177600516280277149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22648704947202753494811461 4246632177600516280277149)
      ·
        refine ⟨1592487066600193605103931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4246632177600516280277149 1592487066600193605103931)
        ·
          refine ⟨2388730599900290407655897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1592487066600193605103931 2388730599900290407655897)
          ·
            refine ⟨1791547949925217805741923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2388730599900290407655897 1791547949925217805741923)
            ·
              refine ⟨2687321924887826708612885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1791547949925217805741923 2687321924887826708612885)
              ·
                refine ⟨125968215229116876966229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2687321924887826708612885 125968215229116876966229)
                ·
                  rfl

theorem cell21_1655925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 6].length) (baseStart_1655925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1655925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1655925 prefixEnd_1655925 := by exact prefixLift 1655925
  have htrace : WordTrace (prefixWord ++ tailWord_1655925) baseStart_1655925 baseEnd_1655925 := by
    simpa [prefixWord, tailWord_1655925, baseEnd_1655925] using wordTrace_append hprefix tailTrace_1655925
  have hstable : (prefixWord ++ tailWord_1655925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655925).length < 2 ^ (prefixWord ++ tailWord_1655925).sum := by decide
  have hdescent : baseEnd_1655925 < baseStart_1655925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655936 : List Nat := [2, 1, 1, 2, 1, 3, 4, 3, 4]
def baseStart_1655936 : Nat := 118140960795 + 1655936 * 2 ^ 59
def prefixEnd_1655936 : Nat := 4983230072969 + 3 ^ 40 * 1655936 * 2
def baseEnd_1655936 : Nat := 377907156037217056215331

theorem tailTrace_1655936 : CollatzResearch.WordTrace tailWord_1655936 prefixEnd_1655936 377907156037217056215331 := by
  unfold tailWord_1655936
  simp only [CollatzResearch.WordTrace]
  refine ⟨30198473864417079099073831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40264631819222772132098441 30198473864417079099073831)
  ·
    refine ⟨45297710796625618648610747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30198473864417079099073831 45297710796625618648610747)
    ·
      refine ⟨67946566194938427972916121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45297710796625618648610747 67946566194938427972916121)
      ·
        refine ⟨50959924646203820979687091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67946566194938427972916121 50959924646203820979687091)
        ·
          refine ⟨76439886969305731469530637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50959924646203820979687091 76439886969305731469530637)
          ·
            refine ⟨28664957613489649301073989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76439886969305731469530637 28664957613489649301073989)
            ·
              refine ⟨5374679552529309243951373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28664957613489649301073989 5374679552529309243951373)
              ·
                refine ⟨2015504832198490966481765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5374679552529309243951373 2015504832198490966481765)
                ·
                  refine ⟨377907156037217056215331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2015504832198490966481765 377907156037217056215331)
                  ·
                    rfl

theorem cell21_1655936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 4].length) (baseStart_1655936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1655936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1655936 prefixEnd_1655936 := by exact prefixLift 1655936
  have htrace : WordTrace (prefixWord ++ tailWord_1655936) baseStart_1655936 baseEnd_1655936 := by
    simpa [prefixWord, tailWord_1655936, baseEnd_1655936] using wordTrace_append hprefix tailTrace_1655936
  have hstable : (prefixWord ++ tailWord_1655936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655936).length < 2 ^ (prefixWord ++ tailWord_1655936).sum := by decide
  have hdescent : baseEnd_1655936 < baseStart_1655936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655967 : List Nat := [1, 1, 2, 6, 2, 1, 8]
def baseStart_1655967 : Nat := 118140960795 + 1655967 * 2 ^ 59
def prefixEnd_1655967 : Nat := 4983230072969 + 3 ^ 40 * 1655967 * 2
def baseEnd_1655967 : Nat := 41990470073285321244289

theorem tailTrace_1655967 : CollatzResearch.WordTrace tailWord_1655967 prefixEnd_1655967 41990470073285321244289 := by
  unfold tailWord_1655967
  simp only [CollatzResearch.WordTrace]
  refine ⟨60398078391721850492526155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40265385594481233661684103 60398078391721850492526155)
  ·
    refine ⟨90597117587582775738789233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60398078391721850492526155 90597117587582775738789233)
    ·
      refine ⟨67947838190687081804091925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90597117587582775738789233 67947838190687081804091925)
      ·
        refine ⟨3185054915188456959566809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67947838190687081804091925 3185054915188456959566809)
        ·
          refine ⟨2388791186391342719675107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3185054915188456959566809 2388791186391342719675107)
          ·
            refine ⟨3583186779587014079512661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2388791186391342719675107 3583186779587014079512661)
            ·
              refine ⟨41990470073285321244289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3583186779587014079512661 41990470073285321244289)
              ·
                rfl

theorem cell21_1655967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 8].length) (baseStart_1655967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1655967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1655967 prefixEnd_1655967 := by exact prefixLift 1655967
  have htrace : WordTrace (prefixWord ++ tailWord_1655967) baseStart_1655967 baseEnd_1655967 := by
    simpa [prefixWord, tailWord_1655967, baseEnd_1655967] using wordTrace_append hprefix tailTrace_1655967
  have hstable : (prefixWord ++ tailWord_1655967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655967).length < 2 ^ (prefixWord ++ tailWord_1655967).sum := by decide
  have hdescent : baseEnd_1655967 < baseStart_1655967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655998 : List Nat := [4, 2, 1, 1, 3, 1, 2, 2, 5]
def baseStart_1655998 : Nat := 118140960795 + 1655998 * 2 ^ 59
def prefixEnd_1655998 : Nat := 4983230072969 + 3 ^ 40 * 1655998 * 2
def baseEnd_1655998 : Nat := 377921305281918726181871

theorem tailTrace_1655998 : CollatzResearch.WordTrace tailWord_1655998 prefixEnd_1655998 377921305281918726181871 := by
  unfold tailWord_1655998
  simp only [CollatzResearch.WordTrace]
  refine ⟨7549901131826192848363081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40266139369739695191269765 7549901131826192848363081)
  ·
    refine ⟨5662425848869644636272311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7549901131826192848363081 5662425848869644636272311)
    ·
      refine ⟨8493638773304466954408467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5662425848869644636272311 8493638773304466954408467)
      ·
        refine ⟨12740458159956700431612701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8493638773304466954408467 12740458159956700431612701)
        ·
          refine ⟨4777671809983762661854763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12740458159956700431612701 4777671809983762661854763)
          ·
            refine ⟨7166507714975643992782145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4777671809983762661854763 7166507714975643992782145)
            ·
              refine ⟨5374880786231732994586609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7166507714975643992782145 5374880786231732994586609)
              ·
                refine ⟨4031160589673799745939957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5374880786231732994586609 4031160589673799745939957)
                ·
                  refine ⟨377921305281918726181871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4031160589673799745939957 377921305281918726181871)
                  ·
                    rfl

theorem cell21_1655998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_1655998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1655998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1655998 prefixEnd_1655998 := by exact prefixLift 1655998
  have htrace : WordTrace (prefixWord ++ tailWord_1655998) baseStart_1655998 baseEnd_1655998 := by
    simpa [prefixWord, tailWord_1655998, baseEnd_1655998] using wordTrace_append hprefix tailTrace_1655998
  have hstable : (prefixWord ++ tailWord_1655998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655998).length < 2 ^ (prefixWord ++ tailWord_1655998).sum := by decide
  have hdescent : baseEnd_1655998 < baseStart_1655998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656001 : List Nat := [1, 2, 6, 1, 1, 3, 2, 5]
def baseStart_1656001 : Nat := 118140960795 + 1656001 * 2 ^ 59
def prefixEnd_1656001 : Nat := 4983230072969 + 3 ^ 40 * 1656001 * 2
def baseEnd_1656001 : Nat := 125973996640930462543955

theorem tailTrace_1656001 : CollatzResearch.WordTrace tailWord_1656001 prefixEnd_1656001 125973996640930462543955 := by
  unfold tailWord_1656001
  simp only [CollatzResearch.WordTrace]
  refine ⟨60399318473598674299263857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40266212315732449532842571 60399318473598674299263857)
  ·
    refine ⟨45299488855199005724447893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60399318473598674299263857 45299488855199005724447893)
    ·
      refine ⟨2123413540087453393333495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45299488855199005724447893 2123413540087453393333495)
      ·
        refine ⟨3185120310131180090000243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2123413540087453393333495 3185120310131180090000243)
        ·
          refine ⟨4777680465196770135000365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3185120310131180090000243 4777680465196770135000365)
          ·
            refine ⟨1791630174448788800625137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4777680465196770135000365 1791630174448788800625137)
            ·
              refine ⟨1343722630836591600468853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1791630174448788800625137 1343722630836591600468853)
              ·
                refine ⟨125973996640930462543955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1343722630836591600468853 125973996640930462543955)
                ·
                  rfl

theorem cell21_1656001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 5].length) (baseStart_1656001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1656001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1656001 prefixEnd_1656001 := by exact prefixLift 1656001
  have htrace : WordTrace (prefixWord ++ tailWord_1656001) baseStart_1656001 baseEnd_1656001 := by
    simpa [prefixWord, tailWord_1656001, baseEnd_1656001] using wordTrace_append hprefix tailTrace_1656001
  have hstable : (prefixWord ++ tailWord_1656001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656001).length < 2 ^ (prefixWord ++ tailWord_1656001).sum := by decide
  have hdescent : baseEnd_1656001 < baseStart_1656001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656074 : List Nat := [3, 1, 2, 2, 1, 1, 1, 7, 3]
def baseStart_1656074 : Nat := 118140960795 + 1656074 * 2 ^ 59
def prefixEnd_1656074 : Nat := 4983230072969 + 3 ^ 40 * 1656074 * 2
def baseEnd_1656074 : Nat := 377938649517359482915049

theorem tailTrace_1656074 : CollatzResearch.WordTrace tailWord_1656074 prefixEnd_1656074 377938649517359482915049 := by
  unfold tailWord_1656074
  simp only [CollatzResearch.WordTrace]
  refine ⟨15100495250583551941667819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40267987334889471844447517 15100495250583551941667819)
  ·
    refine ⟨22650742875875327912501729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15100495250583551941667819 22650742875875327912501729)
    ·
      refine ⟨16988057156906495934376297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22650742875875327912501729 16988057156906495934376297)
      ·
        refine ⟨12741042867679871950782223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16988057156906495934376297 12741042867679871950782223)
        ·
          refine ⟨19111564301519807926173335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12741042867679871950782223 19111564301519807926173335)
          ·
            refine ⟨28667346452279711889260003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19111564301519807926173335 28667346452279711889260003)
            ·
              refine ⟨43001019678419567833890005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28667346452279711889260003 43001019678419567833890005)
              ·
                refine ⟨1007836398712958621106797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 43001019678419567833890005 1007836398712958621106797)
                ·
                  refine ⟨377938649517359482915049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1007836398712958621106797 377938649517359482915049)
                  ·
                    rfl

theorem cell21_1656074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7, 3].length) (baseStart_1656074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1656074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1656074 prefixEnd_1656074 := by exact prefixLift 1656074
  have htrace : WordTrace (prefixWord ++ tailWord_1656074) baseStart_1656074 baseEnd_1656074 := by
    simpa [prefixWord, tailWord_1656074, baseEnd_1656074] using wordTrace_append hprefix tailTrace_1656074
  have hstable : (prefixWord ++ tailWord_1656074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656074).length < 2 ^ (prefixWord ++ tailWord_1656074).sum := by decide
  have hdescent : baseEnd_1656074 < baseStart_1656074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656088 : List Nat := [2, 1, 2, 3, 1, 3, 1, 4, 4]
def baseStart_1656088 : Nat := 118140960795 + 1656088 * 2 ^ 59
def prefixEnd_1656088 : Nat := 4983230072969 + 3 ^ 40 * 1656088 * 2
def baseEnd_1656088 : Nat := 377941844508098569681687

theorem tailTrace_1656088 : CollatzResearch.WordTrace tailWord_1656088 prefixEnd_1656088 377941844508098569681687 := by
  unfold tailWord_1656088
  simp only [CollatzResearch.WordTrace]
  refine ⟨30201245812141744078840459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40268327749522325438453945 30201245812141744078840459)
  ·
    refine ⟨45301868718212616118260689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30201245812141744078840459 45301868718212616118260689)
    ·
      refine ⟨33976401538659462088695517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45301868718212616118260689 33976401538659462088695517)
      ·
        refine ⟨12741150576997298283260819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33976401538659462088695517 12741150576997298283260819)
        ·
          refine ⟨19111725865495947424891229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12741150576997298283260819 19111725865495947424891229)
          ·
            refine ⟨7166897199560980284334211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19111725865495947424891229 7166897199560980284334211)
            ·
              refine ⟨10750345799341470426501317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7166897199560980284334211 10750345799341470426501317)
              ·
                refine ⟨2015689837376525704968997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10750345799341470426501317 2015689837376525704968997)
                ·
                  refine ⟨377941844508098569681687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2015689837376525704968997 377941844508098569681687)
                  ·
                    rfl

theorem cell21_1656088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 4].length) (baseStart_1656088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1656088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1656088 prefixEnd_1656088 := by exact prefixLift 1656088
  have htrace : WordTrace (prefixWord ++ tailWord_1656088) baseStart_1656088 baseEnd_1656088 := by
    simpa [prefixWord, tailWord_1656088, baseEnd_1656088] using wordTrace_append hprefix tailTrace_1656088
  have hstable : (prefixWord ++ tailWord_1656088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656088).length < 2 ^ (prefixWord ++ tailWord_1656088).sum := by decide
  have hdescent : baseEnd_1656088 < baseStart_1656088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656094 : List Nat := [4, 3, 2, 1, 3, 1, 1, 6]
def baseStart_1656094 : Nat := 118140960795 + 1656094 * 2 ^ 59
def prefixEnd_1656094 : Nat := 4983230072969 + 3 ^ 40 * 1656094 * 2
def baseEnd_1656094 : Nat := 125981071263281297527225

theorem tailTrace_1656094 : CollatzResearch.WordTrace tailWord_1656094 prefixEnd_1656094 125981071263281297527225 := by
  unfold tailWord_1656094
  simp only [CollatzResearch.WordTrace]
  refine ⟨7550338807782718897799917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40268473641507834121599557 7550338807782718897799917)
  ·
    refine ⟨2831377052918519586674969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7550338807782718897799917 2831377052918519586674969)
    ·
      refine ⟨2123532789688889690006227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2831377052918519586674969 2123532789688889690006227)
      ·
        refine ⟨3185299184533334535009341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2123532789688889690006227 3185299184533334535009341)
        ·
          refine ⟨1194487194200000450628503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3185299184533334535009341 1194487194200000450628503)
          ·
            refine ⟨1791730791300000675942755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1194487194200000450628503 1791730791300000675942755)
            ·
              refine ⟨2687596186950001013914133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1791730791300000675942755 2687596186950001013914133)
              ·
                refine ⟨125981071263281297527225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2687596186950001013914133 125981071263281297527225)
                ·
                  rfl

theorem cell21_1656094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_1656094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1656094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1656094 prefixEnd_1656094 := by exact prefixLift 1656094
  have htrace : WordTrace (prefixWord ++ tailWord_1656094) baseStart_1656094 baseEnd_1656094 := by
    simpa [prefixWord, tailWord_1656094, baseEnd_1656094] using wordTrace_append hprefix tailTrace_1656094
  have hstable : (prefixWord ++ tailWord_1656094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656094).length < 2 ^ (prefixWord ++ tailWord_1656094).sum := by decide
  have hdescent : baseEnd_1656094 < baseStart_1656094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656147 : List Nat := [1, 1, 1, 2, 1, 1, 7, 1, 6]
def baseStart_1656147 : Nat := 118140960795 + 1656147 * 2 ^ 59
def prefixEnd_1656147 : Nat := 4983230072969 + 3 ^ 40 * 1656147 * 2
def baseEnd_1656147 : Nat := 377955309111927578198233

theorem tailTrace_1656147 : CollatzResearch.WordTrace tailWord_1656147 prefixEnd_1656147 377955309111927578198233 := by
  unfold tailWord_1656147
  simp only [CollatzResearch.WordTrace]
  refine ⟨60404643531069741234078695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40269762354046494156052463 60404643531069741234078695)
  ·
    refine ⟨90606965296604611851118043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60404643531069741234078695 90606965296604611851118043)
    ·
      refine ⟨135910447944906917776677065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90606965296604611851118043 135910447944906917776677065)
      ·
        refine ⟨101932835958680188332507799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135910447944906917776677065 101932835958680188332507799)
        ·
          refine ⟨152899253938020282498761699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101932835958680188332507799 152899253938020282498761699)
          ·
            refine ⟨229348880907030423748142549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152899253938020282498761699 229348880907030423748142549)
            ·
              refine ⟨5375364396258525556597091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 229348880907030423748142549 5375364396258525556597091)
              ·
                refine ⟨8063046594387788334895637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5375364396258525556597091 8063046594387788334895637)
                ·
                  refine ⟨377955309111927578198233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8063046594387788334895637 377955309111927578198233)
                  ·
                    rfl

theorem cell21_1656147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 6].length) (baseStart_1656147 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1656147 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1656147 prefixEnd_1656147 := by exact prefixLift 1656147
  have htrace : WordTrace (prefixWord ++ tailWord_1656147) baseStart_1656147 baseEnd_1656147 := by
    simpa [prefixWord, tailWord_1656147, baseEnd_1656147] using wordTrace_append hprefix tailTrace_1656147
  have hstable : (prefixWord ++ tailWord_1656147).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656147).length < 2 ^ (prefixWord ++ tailWord_1656147).sum := by decide
  have hdescent : baseEnd_1656147 < baseStart_1656147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656178 : List Nat := [3, 2, 1, 2, 1, 2, 3, 7]
def baseStart_1656178 : Nat := 118140960795 + 1656178 * 2 ^ 59
def prefixEnd_1656178 : Nat := 4983230072969 + 3 ^ 40 * 1656178 * 2
def baseEnd_1656178 : Nat := 125987461244759471060501

theorem tailTrace_1656178 : CollatzResearch.WordTrace tailWord_1656178 prefixEnd_1656178 125987461244759471060501 := by
  unfold tailWord_1656178
  simp only [CollatzResearch.WordTrace]
  refine ⟨15101443548489358382114297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40270516129304955685638125 15101443548489358382114297)
  ·
    refine ⟨11326082661367018786585723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15101443548489358382114297 11326082661367018786585723)
    ·
      refine ⟨16989123992050528179878585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11326082661367018786585723 16989123992050528179878585)
      ·
        refine ⟨12741842994037896134908939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16989123992050528179878585 12741842994037896134908939)
        ·
          refine ⟨19112764491056844202363409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12741842994037896134908939 19112764491056844202363409)
          ·
            refine ⟨14334573368292633151772557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19112764491056844202363409 14334573368292633151772557)
            ·
              refine ⟨5375465013109737431914709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14334573368292633151772557 5375465013109737431914709)
              ·
                refine ⟨125987461244759471060501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5375465013109737431914709 125987461244759471060501)
                ·
                  rfl

theorem cell21_1656178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_1656178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1656178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1656178 prefixEnd_1656178 := by exact prefixLift 1656178
  have htrace : WordTrace (prefixWord ++ tailWord_1656178) baseStart_1656178 baseEnd_1656178 := by
    simpa [prefixWord, tailWord_1656178, baseEnd_1656178] using wordTrace_append hprefix tailTrace_1656178
  have hstable : (prefixWord ++ tailWord_1656178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656178).length < 2 ^ (prefixWord ++ tailWord_1656178).sum := by decide
  have hdescent : baseEnd_1656178 < baseStart_1656178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656192 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 7]
def baseStart_1656192 : Nat := 118140960795 + 1656192 * 2 ^ 59
def prefixEnd_1656192 : Nat := 4983230072969 + 3 ^ 40 * 1656192 * 2
def baseEnd_1656192 : Nat := 377965578725017499948141

theorem tailTrace_1656192 : CollatzResearch.WordTrace tailWord_1656192 prefixEnd_1656192 377965578725017499948141 := by
  unfold tailWord_1656192
  simp only [CollatzResearch.WordTrace]
  refine ⟨30203142407953356959733415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40270856543937809279644553 30203142407953356959733415)
  ·
    refine ⟨45304713611930035439600123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30203142407953356959733415 45304713611930035439600123)
    ·
      refine ⟨67957070417895053159400185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45304713611930035439600123 67957070417895053159400185)
      ·
        refine ⟨50967802813421289869550139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67957070417895053159400185 50967802813421289869550139)
        ·
          refine ⟨76451704220131934804325209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50967802813421289869550139 76451704220131934804325209)
          ·
            refine ⟨57338778165098951103243907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76451704220131934804325209 57338778165098951103243907)
            ·
              refine ⟨86008167247648426654865861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57338778165098951103243907 86008167247648426654865861)
              ·
                refine ⟨16126531358934079997787349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86008167247648426654865861 16126531358934079997787349)
                ·
                  refine ⟨377965578725017499948141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16126531358934079997787349 377965578725017499948141)
                  ·
                    rfl

theorem cell21_1656192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_1656192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1656192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1656192 prefixEnd_1656192 := by exact prefixLift 1656192
  have htrace : WordTrace (prefixWord ++ tailWord_1656192) baseStart_1656192 baseEnd_1656192 := by
    simpa [prefixWord, tailWord_1656192, baseEnd_1656192] using wordTrace_append hprefix tailTrace_1656192
  have hstable : (prefixWord ++ tailWord_1656192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656192).length < 2 ^ (prefixWord ++ tailWord_1656192).sum := by decide
  have hdescent : baseEnd_1656192 < baseStart_1656192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656260 : List Nat := [2, 3, 3, 2, 1, 1, 4, 2, 3]
def baseStart_1656260 : Nat := 118140960795 + 1656260 * 2 ^ 59
def prefixEnd_1656260 : Nat := 4983230072969 + 3 ^ 40 * 1656260 * 2
def baseEnd_1656260 : Nat := 377981097251464492814669

theorem tailTrace_1656260 : CollatzResearch.WordTrace tailWord_1656260 prefixEnd_1656260 377981097251464492814669 := by
  unfold tailWord_1656260
  simp only [CollatzResearch.WordTrace]
  refine ⟨30204382489830180766471117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40272509986440241021961489 30204382489830180766471117)
  ·
    refine ⟨11326643433686317787426669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30204382489830180766471117 11326643433686317787426669)
    ·
      refine ⟨4247491287632369170285001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11326643433686317787426669 4247491287632369170285001)
      ·
        refine ⟨3185618465724276877713751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4247491287632369170285001 3185618465724276877713751)
        ·
          refine ⟨4778427698586415316570627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3185618465724276877713751 4778427698586415316570627)
          ·
            refine ⟨7167641547879622974855941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4778427698586415316570627 7167641547879622974855941)
            ·
              refine ⟨1343932790227429307785489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7167641547879622974855941 1343932790227429307785489)
              ·
                refine ⟨1007949592670571980839117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1343932790227429307785489 1007949592670571980839117)
                ·
                  refine ⟨377981097251464492814669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1007949592670571980839117 377981097251464492814669)
                  ·
                    rfl

theorem cell21_1656260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_1656260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1656260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1656260 prefixEnd_1656260 := by exact prefixLift 1656260
  have htrace : WordTrace (prefixWord ++ tailWord_1656260) baseStart_1656260 baseEnd_1656260 := by
    simpa [prefixWord, tailWord_1656260, baseEnd_1656260] using wordTrace_append hprefix tailTrace_1656260
  have hstable : (prefixWord ++ tailWord_1656260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656260).length < 2 ^ (prefixWord ++ tailWord_1656260).sum := by decide
  have hdescent : baseEnd_1656260 < baseStart_1656260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656285 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 7]
def baseStart_1656285 : Nat := 118140960795 + 1656285 * 2 ^ 59
def prefixEnd_1656285 : Nat := 4983230072969 + 3 ^ 40 * 1656285 * 2
def baseEnd_1656285 : Nat := 377986802592070004897951

theorem tailTrace_1656285 : CollatzResearch.WordTrace tailWord_1656285 prefixEnd_1656285 377986802592070004897951 := by
  unfold tailWord_1656285
  simp only [CollatzResearch.WordTrace]
  refine ⟨60409676804569790802602309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40273117869713193868401539 60409676804569790802602309)
  ·
    refine ⟨11326814400856835775487933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60409676804569790802602309 11326814400856835775487933)
    ·
      refine ⟨4247555400321313415807975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11326814400856835775487933 4247555400321313415807975)
      ·
        refine ⟨6371333100481970123711963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4247555400321313415807975 6371333100481970123711963)
        ·
          refine ⟨9556999650722955185567945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6371333100481970123711963 9556999650722955185567945)
          ·
            refine ⟨7167749738042216389175959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9556999650722955185567945 7167749738042216389175959)
            ·
              refine ⟨10751624607063324583763939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7167749738042216389175959 10751624607063324583763939)
              ·
                refine ⟨16127436910594986875645909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10751624607063324583763939 16127436910594986875645909)
                ·
                  refine ⟨377986802592070004897951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16127436910594986875645909 377986802592070004897951)
                  ·
                    rfl

theorem cell21_1656285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_1656285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1656285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1656285 prefixEnd_1656285 := by exact prefixLift 1656285
  have htrace : WordTrace (prefixWord ++ tailWord_1656285) baseStart_1656285 baseEnd_1656285 := by
    simpa [prefixWord, tailWord_1656285, baseEnd_1656285] using wordTrace_append hprefix tailTrace_1656285
  have hstable : (prefixWord ++ tailWord_1656285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656285).length < 2 ^ (prefixWord ++ tailWord_1656285).sum := by decide
  have hdescent : baseEnd_1656285 < baseStart_1656285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656316 : List Nat := [2, 2, 2, 1, 2, 1, 5, 2, 4]
def baseStart_1656316 : Nat := 118140960795 + 1656316 * 2 ^ 59
def prefixEnd_1656316 : Nat := 4983230072969 + 3 ^ 40 * 1656316 * 2
def baseEnd_1656316 : Nat := 377993877214420839881221

theorem tailTrace_1656316 : CollatzResearch.WordTrace tailWord_1656316 prefixEnd_1656316 377993877214420839881221 := by
  unfold tailWord_1656316
  simp only [CollatzResearch.WordTrace]
  refine ⟨30205403733728741548490401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40273871644971655397987201 30205403733728741548490401)
  ·
    refine ⟨22654052800296556161367801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30205403733728741548490401 22654052800296556161367801)
    ·
      refine ⟨16990539600222417121025851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22654052800296556161367801 16990539600222417121025851)
      ·
        refine ⟨25485809400333625681538777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16990539600222417121025851 25485809400333625681538777)
        ·
          refine ⟨19114357050250219261154083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25485809400333625681538777 19114357050250219261154083)
          ·
            refine ⟨28671535575375328891731125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19114357050250219261154083 28671535575375328891731125)
            ·
              refine ⟨2687956460191437083599793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28671535575375328891731125 2687956460191437083599793)
              ·
                refine ⟨2015967345143577812699845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2687956460191437083599793 2015967345143577812699845)
                ·
                  refine ⟨377993877214420839881221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2015967345143577812699845 377993877214420839881221)
                  ·
                    rfl

theorem cell21_1656316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_1656316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1656316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1656316 prefixEnd_1656316 := by exact prefixLift 1656316
  have htrace : WordTrace (prefixWord ++ tailWord_1656316) baseStart_1656316 baseEnd_1656316 := by
    simpa [prefixWord, tailWord_1656316, baseEnd_1656316] using wordTrace_append hprefix tailTrace_1656316
  have hstable : (prefixWord ++ tailWord_1656316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656316).length < 2 ^ (prefixWord ++ tailWord_1656316).sum := by decide
  have hdescent : baseEnd_1656316 < baseStart_1656316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656375 : List Nat := [1, 1, 3, 1, 2, 4, 2, 1, 6]
def baseStart_1656375 : Nat := 118140960795 + 1656375 * 2 ^ 59
def prefixEnd_1656375 : Nat := 4983230072969 + 3 ^ 40 * 1656375 * 2
def baseEnd_1656375 : Nat := 378007341818249848397767

theorem tailTrace_1656375 : CollatzResearch.WordTrace tailWord_1656375 prefixEnd_1656375 378007341818249848397767 := by
  unfold tailWord_1656375
  simp only [CollatzResearch.WordTrace]
  refine ⟨60412959374243736173378579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40275306249495824115585719 60412959374243736173378579)
  ·
    refine ⟨90619439061365604260067869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60412959374243736173378579 90619439061365604260067869)
    ·
      refine ⟨33982289648012101597525451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90619439061365604260067869 33982289648012101597525451)
      ·
        refine ⟨50973434472018152396288177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33982289648012101597525451 50973434472018152396288177)
        ·
          refine ⟨38230075854013614297216133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50973434472018152396288177 38230075854013614297216133)
          ·
            refine ⟨7168139222627552680728025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38230075854013614297216133 7168139222627552680728025)
            ·
              refine ⟨5376104416970664510546019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7168139222627552680728025 5376104416970664510546019)
              ·
                refine ⟨8064156625455996765819029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5376104416970664510546019 8064156625455996765819029)
                ·
                  refine ⟨378007341818249848397767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8064156625455996765819029 378007341818249848397767)
                  ·
                    rfl

theorem cell21_1656375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 6].length) (baseStart_1656375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1656375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1656375 prefixEnd_1656375 := by exact prefixLift 1656375
  have htrace : WordTrace (prefixWord ++ tailWord_1656375) baseStart_1656375 baseEnd_1656375 := by
    simpa [prefixWord, tailWord_1656375, baseEnd_1656375] using wordTrace_append hprefix tailTrace_1656375
  have hstable : (prefixWord ++ tailWord_1656375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656375).length < 2 ^ (prefixWord ++ tailWord_1656375).sum := by decide
  have hdescent : baseEnd_1656375 < baseStart_1656375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656429 : List Nat := [1, 5, 1, 1, 5, 1, 2, 2, 3]
def baseStart_1656429 : Nat := 118140960795 + 1656429 * 2 ^ 59
def prefixEnd_1656429 : Nat := 4983230072969 + 3 ^ 40 * 1656429 * 2
def baseEnd_1656429 : Nat := 378019665353957754497657

theorem tailTrace_1656429 : CollatzResearch.WordTrace tailWord_1656429 prefixEnd_1656429 378019665353957754497657 := by
  unfold tailWord_1656429
  simp only [CollatzResearch.WordTrace]
  refine ⟨60414928916048103395844341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40276619277365402263896227 60414928916048103395844341)
  ·
    refine ⟨5663899585879509693360407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60414928916048103395844341 5663899585879509693360407)
    ·
      refine ⟨8495849378819264540040611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5663899585879509693360407 8495849378819264540040611)
      ·
        refine ⟨12743774068228896810060917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8495849378819264540040611 12743774068228896810060917)
        ·
          refine ⟨1194728818896459075943211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12743774068228896810060917 1194728818896459075943211)
          ·
            refine ⟨1792093228344688613914817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1194728818896459075943211 1792093228344688613914817)
            ·
              refine ⟨1344069921258516460436113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1792093228344688613914817 1344069921258516460436113)
              ·
                refine ⟨1008052440943887345327085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1344069921258516460436113 1008052440943887345327085)
                ·
                  refine ⟨378019665353957754497657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1008052440943887345327085 378019665353957754497657)
                  ·
                    rfl

theorem cell21_1656429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_1656429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1656429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1656429 prefixEnd_1656429 := by exact prefixLift 1656429
  have htrace : WordTrace (prefixWord ++ tailWord_1656429) baseStart_1656429 baseEnd_1656429 := by
    simpa [prefixWord, tailWord_1656429, baseEnd_1656429] using wordTrace_append hprefix tailTrace_1656429
  have hstable : (prefixWord ++ tailWord_1656429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656429).length < 2 ^ (prefixWord ++ tailWord_1656429).sum := by decide
  have hdescent : baseEnd_1656429 < baseStart_1656429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656488 : List Nat := [2, 1, 7, 1, 1, 1, 2, 1, 5]
def baseStart_1656488 : Nat := 118140960795 + 1656488 * 2 ^ 59
def prefixEnd_1656488 : Nat := 4983230072969 + 3 ^ 40 * 1656488 * 2
def baseEnd_1656488 : Nat := 378033129957786763014203

theorem tailTrace_1656488 : CollatzResearch.WordTrace tailWord_1656488 prefixEnd_1656488 378033129957786763014203 := by
  unfold tailWord_1656488
  simp only [CollatzResearch.WordTrace]
  refine ⟨30208540411417178236121059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40278053881889570981494745 30208540411417178236121059)
  ·
    refine ⟨45312810617125767354181589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30208540411417178236121059 45312810617125767354181589)
    ·
      refine ⟨1062018998838885172363631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 45312810617125767354181589 1062018998838885172363631)
      ·
        refine ⟨1593028498258327758545447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1062018998838885172363631 1593028498258327758545447)
        ·
          refine ⟨2389542747387491637818171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1593028498258327758545447 2389542747387491637818171)
          ·
            refine ⟨3584314121081237456727257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2389542747387491637818171 3584314121081237456727257)
            ·
              refine ⟨2688235590810928092545443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3584314121081237456727257 2688235590810928092545443)
              ·
                refine ⟨4032353386216392138818165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2688235590810928092545443 4032353386216392138818165)
                ·
                  refine ⟨378033129957786763014203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4032353386216392138818165 378033129957786763014203)
                  ·
                    rfl

theorem cell21_1656488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 5].length) (baseStart_1656488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1656488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1656488 prefixEnd_1656488 := by exact prefixLift 1656488
  have htrace : WordTrace (prefixWord ++ tailWord_1656488) baseStart_1656488 baseEnd_1656488 := by
    simpa [prefixWord, tailWord_1656488, baseEnd_1656488] using wordTrace_append hprefix tailTrace_1656488
  have hstable : (prefixWord ++ tailWord_1656488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656488).length < 2 ^ (prefixWord ++ tailWord_1656488).sum := by decide
  have hdescent : baseEnd_1656488 < baseStart_1656488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656496 : List Nat := [2, 1, 1, 1, 2, 1, 5, 3, 5]
def baseStart_1656496 : Nat := 118140960795 + 1656496 * 2 ^ 59
def prefixEnd_1656496 : Nat := 4983230072969 + 3 ^ 40 * 1656496 * 2
def baseEnd_1656496 : Nat := 378034955666780526880853

theorem tailTrace_1656496 : CollatzResearch.WordTrace tailWord_1656496 prefixEnd_1656496 378034955666780526880853 := by
  unfold tailWord_1656496
  simp only [CollatzResearch.WordTrace]
  refine ⟨30208686303402686919266671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40278248404536915892355561 30208686303402686919266671)
  ·
    refine ⟨45313029455104030378900007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30208686303402686919266671 45313029455104030378900007)
    ·
      refine ⟨67969544182656045568350011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45313029455104030378900007 67969544182656045568350011)
      ·
        refine ⟨101954316273984068352525017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67969544182656045568350011 101954316273984068352525017)
        ·
          refine ⟨76465737205488051264393763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101954316273984068352525017 76465737205488051264393763)
          ·
            refine ⟨114698605808232076896590645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76465737205488051264393763 114698605808232076896590645)
            ·
              refine ⟨10752994294521757209055373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114698605808232076896590645 10752994294521757209055373)
              ·
                refine ⟨4032372860445658953395765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10752994294521757209055373 4032372860445658953395765)
                ·
                  refine ⟨378034955666780526880853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4032372860445658953395765 378034955666780526880853)
                  ·
                    rfl

theorem cell21_1656496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 5].length) (baseStart_1656496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1656496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1656496 prefixEnd_1656496 := by exact prefixLift 1656496
  have htrace : WordTrace (prefixWord ++ tailWord_1656496) baseStart_1656496 baseEnd_1656496 := by
    simpa [prefixWord, tailWord_1656496, baseEnd_1656496] using wordTrace_append hprefix tailTrace_1656496
  have hstable : (prefixWord ++ tailWord_1656496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656496).length < 2 ^ (prefixWord ++ tailWord_1656496).sum := by decide
  have hdescent : baseEnd_1656496 < baseStart_1656496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656547 : List Nat := [1, 1, 1, 7, 3, 1, 1, 1, 5]
def baseStart_1656547 : Nat := 118140960795 + 1656547 * 2 ^ 59
def prefixEnd_1656547 : Nat := 4983230072969 + 3 ^ 40 * 1656547 * 2
def baseEnd_1656547 : Nat := 378046594561615771530749

theorem tailTrace_1656547 : CollatzResearch.WordTrace tailWord_1656547 prefixEnd_1656547 378046594561615771530749 := by
  unfold tailWord_1656547
  simp only [CollatzResearch.WordTrace]
  refine ⟨60419232729620609548639895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40279488486413739699093263 60419232729620609548639895)
  ·
    refine ⟨90628849094430914322959843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60419232729620609548639895 90628849094430914322959843)
    ·
      refine ⟨135943273641646371484439765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90628849094430914322959843 135943273641646371484439765)
      ·
        refine ⟨3186170475976086831666557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 135943273641646371484439765 3186170475976086831666557)
        ·
          refine ⟨1194813928491032561874959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3186170475976086831666557 1194813928491032561874959)
          ·
            refine ⟨1792220892736548842812439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1194813928491032561874959 1792220892736548842812439)
            ·
              refine ⟨2688331339104823264218659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1792220892736548842812439 2688331339104823264218659)
              ·
                refine ⟨4032497008657234896327989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2688331339104823264218659 4032497008657234896327989)
                ·
                  refine ⟨378046594561615771530749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4032497008657234896327989 378046594561615771530749)
                  ·
                    rfl

theorem cell21_1656547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 5].length) (baseStart_1656547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1656547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1656547 prefixEnd_1656547 := by exact prefixLift 1656547
  have htrace : WordTrace (prefixWord ++ tailWord_1656547) baseStart_1656547 baseEnd_1656547 := by
    simpa [prefixWord, tailWord_1656547, baseEnd_1656547] using wordTrace_append hprefix tailTrace_1656547
  have hstable : (prefixWord ++ tailWord_1656547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656547).length < 2 ^ (prefixWord ++ tailWord_1656547).sum := by decide
  have hdescent : baseEnd_1656547 < baseStart_1656547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656558 : List Nat := [4, 1, 2, 1, 1, 2, 4, 6]
def baseStart_1656558 : Nat := 118140960795 + 1656558 * 2 ^ 59
def prefixEnd_1656558 : Nat := 4983230072969 + 3 ^ 40 * 1656558 * 2
def baseEnd_1656558 : Nat := 126016368303827398949131

theorem tailTrace_1656558 : CollatzResearch.WordTrace tailWord_1656558 prefixEnd_1656558 126016368303827398949131 := by
  unfold tailWord_1656558
  simp only [CollatzResearch.WordTrace]
  refine ⟨7552454241572594803411291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40279755955053838951526885 7552454241572594803411291)
  ·
    refine ⟨11328681362358892205116937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7552454241572594803411291 11328681362358892205116937)
    ·
      refine ⟨8496511021769169153837703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11328681362358892205116937 8496511021769169153837703)
      ·
        refine ⟨12744766532653753730756555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8496511021769169153837703 12744766532653753730756555)
        ·
          refine ⟨19117149798980630596134833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12744766532653753730756555 19117149798980630596134833)
          ·
            refine ⟨14337862349235472947101125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19117149798980630596134833 14337862349235472947101125)
            ·
              refine ⟨2688349190481651177581461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14337862349235472947101125 2688349190481651177581461)
              ·
                refine ⟨126016368303827398949131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2688349190481651177581461 126016368303827398949131)
                ·
                  rfl

theorem cell21_1656558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_1656558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1656558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1656558 prefixEnd_1656558 := by exact prefixLift 1656558
  have htrace : WordTrace (prefixWord ++ tailWord_1656558) baseStart_1656558 baseEnd_1656558 := by
    simpa [prefixWord, tailWord_1656558, baseEnd_1656558] using wordTrace_append hprefix tailTrace_1656558
  have hstable : (prefixWord ++ tailWord_1656558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656558).length < 2 ^ (prefixWord ++ tailWord_1656558).sum := by decide
  have hdescent : baseEnd_1656558 < baseStart_1656558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656561 : List Nat := [1, 2, 2, 2, 2, 5, 2, 1, 4]
def baseStart_1656561 : Nat := 118140960795 + 1656561 * 2 ^ 59
def prefixEnd_1656561 : Nat := 4983230072969 + 3 ^ 40 * 1656561 * 2
def baseEnd_1656561 : Nat := 378049789552354858297387

theorem tailTrace_1656561 : CollatzResearch.WordTrace tailWord_1656561 prefixEnd_1656561 378049789552354858297387 := by
  unfold tailWord_1656561
  simp only [CollatzResearch.WordTrace]
  refine ⟨60419743351569889939649537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40279828901046593293099691 60419743351569889939649537)
  ·
    refine ⟨45314807513677417454737153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60419743351569889939649537 45314807513677417454737153)
    ·
      refine ⟨33986105635258063091052865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45314807513677417454737153 33986105635258063091052865)
      ·
        refine ⟨25489579226443547318289649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33986105635258063091052865 25489579226443547318289649)
        ·
          refine ⟨19117184419832660488717237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25489579226443547318289649 19117184419832660488717237)
          ·
            refine ⟨1792236039359311920817241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19117184419832660488717237 1792236039359311920817241)
            ·
              refine ⟨1344177029519483940612931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1792236039359311920817241 1344177029519483940612931)
              ·
                refine ⟨2016265544279225910919397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1344177029519483940612931 2016265544279225910919397)
                ·
                  refine ⟨378049789552354858297387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2016265544279225910919397 378049789552354858297387)
                  ·
                    rfl

theorem cell21_1656561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 4].length) (baseStart_1656561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1656561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1656561 prefixEnd_1656561 := by exact prefixLift 1656561
  have htrace : WordTrace (prefixWord ++ tailWord_1656561) baseStart_1656561 baseEnd_1656561 := by
    simpa [prefixWord, tailWord_1656561, baseEnd_1656561] using wordTrace_append hprefix tailTrace_1656561
  have hstable : (prefixWord ++ tailWord_1656561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656561).length < 2 ^ (prefixWord ++ tailWord_1656561).sum := by decide
  have hdescent : baseEnd_1656561 < baseStart_1656561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656572 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 7]
def baseStart_1656572 : Nat := 118140960795 + 1656572 * 2 ^ 59
def prefixEnd_1656572 : Nat := 4983230072969 + 3 ^ 40 * 1656572 * 2
def baseEnd_1656572 : Nat := 378052299902221283614031

theorem tailTrace_1656572 : CollatzResearch.WordTrace tailWord_1656572 prefixEnd_1656572 378052299902221283614031 := by
  unfold tailWord_1656572
  simp only [CollatzResearch.WordTrace]
  refine ⟨30210072277265019409149985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40280096369686692545533313 30210072277265019409149985)
  ·
    refine ⟨22657554207948764556862489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30210072277265019409149985 22657554207948764556862489)
    ·
      refine ⟨16993165655961573417646867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22657554207948764556862489 16993165655961573417646867)
      ·
        refine ⟨25489748483942360126470301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16993165655961573417646867 25489748483942360126470301)
        ·
          refine ⟨9558655681478385047426363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25489748483942360126470301 9558655681478385047426363)
          ·
            refine ⟨14337983522217577571139545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9558655681478385047426363 14337983522217577571139545)
            ·
              refine ⟨10753487641663183178354659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14337983522217577571139545 10753487641663183178354659)
              ·
                refine ⟨16130231462494774767531989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10753487641663183178354659 16130231462494774767531989)
                ·
                  refine ⟨378052299902221283614031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16130231462494774767531989 378052299902221283614031)
                  ·
                    rfl

theorem cell21_1656572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_1656572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1656572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1656572 prefixEnd_1656572 := by exact prefixLift 1656572
  have htrace : WordTrace (prefixWord ++ tailWord_1656572) baseStart_1656572 baseEnd_1656572 := by
    simpa [prefixWord, tailWord_1656572, baseEnd_1656572] using wordTrace_append hprefix tailTrace_1656572
  have hstable : (prefixWord ++ tailWord_1656572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656572).length < 2 ^ (prefixWord ++ tailWord_1656572).sum := by decide
  have hdescent : baseEnd_1656572 < baseStart_1656572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656665 : List Nat := [1, 2, 1, 2, 2, 3, 1, 6, 3]
def baseStart_1656665 : Nat := 118140960795 + 1656665 * 2 ^ 59
def prefixEnd_1656665 : Nat := 4983230072969 + 3 ^ 40 * 1656665 * 2
def baseEnd_1656665 : Nat := 378073523769273788563841

theorem tailTrace_1656665 : CollatzResearch.WordTrace tailWord_1656665 prefixEnd_1656665 378073523769273788563841 := by
  unfold tailWord_1656665
  simp only [CollatzResearch.WordTrace]
  refine ⟨60423536543193115701435449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40282357695462077134290299 60423536543193115701435449)
  ·
    refine ⟨45317652407394836776076587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60423536543193115701435449 45317652407394836776076587)
    ·
      refine ⟨67976478611092255164114881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45317652407394836776076587 67976478611092255164114881)
      ·
        refine ⟨50982358958319191373086161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67976478611092255164114881 50982358958319191373086161)
        ·
          refine ⟨38236769218739393529814621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50982358958319191373086161 38236769218739393529814621)
          ·
            refine ⟨14338788457027272573680483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38236769218739393529814621 14338788457027272573680483)
            ·
              refine ⟨21508182685540908860520725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14338788457027272573680483 21508182685540908860520725)
              ·
                refine ⟨1008196063384730102836909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21508182685540908860520725 1008196063384730102836909)
                ·
                  refine ⟨378073523769273788563841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1008196063384730102836909 378073523769273788563841)
                  ·
                    rfl

theorem cell21_1656665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6, 3].length) (baseStart_1656665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1656665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1656665 prefixEnd_1656665 := by exact prefixLift 1656665
  have htrace : WordTrace (prefixWord ++ tailWord_1656665) baseStart_1656665 baseEnd_1656665 := by
    simpa [prefixWord, tailWord_1656665, baseEnd_1656665] using wordTrace_append hprefix tailTrace_1656665
  have hstable : (prefixWord ++ tailWord_1656665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656665).length < 2 ^ (prefixWord ++ tailWord_1656665).sum := by decide
  have hdescent : baseEnd_1656665 < baseStart_1656665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656859 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 7]
def baseStart_1656859 : Nat := 118140960795 + 1656859 * 2 ^ 59
def prefixEnd_1656859 : Nat := 4983230072969 + 3 ^ 40 * 1656859 * 2
def baseEnd_1656859 : Nat := 378117797212372562330111

theorem tailTrace_1656859 : CollatzResearch.WordTrace tailWord_1656859 prefixEnd_1656859 378117797212372562330111 := by
  unfold tailWord_1656859
  simp only [CollatzResearch.WordTrace]
  refine ⟨60430612304490286833997631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40287074869660191222665087 60430612304490286833997631)
  ·
    refine ⟨90645918456735430250996447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60430612304490286833997631 90645918456735430250996447)
    ·
      refine ⟨135968877685103145376494671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90645918456735430250996447 135968877685103145376494671)
      ·
        refine ⟨203953316527654718064742007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135968877685103145376494671 203953316527654718064742007)
        ·
          refine ⟨305929974791482077097113011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203953316527654718064742007 305929974791482077097113011)
          ·
            refine ⟨458894962187223115645669517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305929974791482077097113011 458894962187223115645669517)
            ·
              refine ⟨172085610820208668367126069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 458894962187223115645669517 172085610820208668367126069)
              ·
                refine ⟨16133026014394562659418069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 172085610820208668367126069 16133026014394562659418069)
                ·
                  refine ⟨378117797212372562330111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16133026014394562659418069 378117797212372562330111)
                  ·
                    rfl

theorem cell21_1656859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 7].length) (baseStart_1656859 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1656859 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1656859 prefixEnd_1656859 := by exact prefixLift 1656859
  have htrace : WordTrace (prefixWord ++ tailWord_1656859) baseStart_1656859 baseEnd_1656859 := by
    simpa [prefixWord, tailWord_1656859, baseEnd_1656859] using wordTrace_append hprefix tailTrace_1656859
  have hstable : (prefixWord ++ tailWord_1656859).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656859).length < 2 ^ (prefixWord ++ tailWord_1656859).sum := by decide
  have hdescent : baseEnd_1656859 < baseStart_1656859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656868 : List Nat := [2, 3, 1, 4, 3, 1, 1, 3, 3]
def baseStart_1656868 : Nat := 118140960795 + 1656868 * 2 ^ 59
def prefixEnd_1656868 : Nat := 4983230072969 + 3 ^ 40 * 1656868 * 2
def baseEnd_1656868 : Nat := 378119851134990546680093

theorem tailTrace_1656868 : CollatzResearch.WordTrace tailWord_1656868 prefixEnd_1656868 378119851134990546680093 := by
  unfold tailWord_1656868
  simp only [CollatzResearch.WordTrace]
  refine ⟨30215470280728840685537629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40287293707638454247383505 30215470280728840685537629)
  ·
    refine ⟨11330801355273315257076611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30215470280728840685537629 11330801355273315257076611)
    ·
      refine ⟨16996202032909972885614917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11330801355273315257076611 16996202032909972885614917)
      ·
        refine ⟨3186787881170619916052797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16996202032909972885614917 3186787881170619916052797)
        ·
          refine ⟨1195045455438982468519799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3186787881170619916052797 1195045455438982468519799)
          ·
            refine ⟨1792568183158473702779699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1195045455438982468519799 1792568183158473702779699)
            ·
              refine ⟨2688852274737710554169549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1792568183158473702779699 2688852274737710554169549)
              ·
                refine ⟨1008319603026641457813581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2688852274737710554169549 1008319603026641457813581)
                ·
                  refine ⟨378119851134990546680093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1008319603026641457813581 378119851134990546680093)
                  ·
                    rfl

theorem cell21_1656868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_1656868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1656868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1656868 prefixEnd_1656868 := by exact prefixLift 1656868
  have htrace : WordTrace (prefixWord ++ tailWord_1656868) baseStart_1656868 baseEnd_1656868 := by
    simpa [prefixWord, tailWord_1656868, baseEnd_1656868] using wordTrace_append hprefix tailTrace_1656868
  have hstable : (prefixWord ++ tailWord_1656868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656868).length < 2 ^ (prefixWord ++ tailWord_1656868).sum := by decide
  have hdescent : baseEnd_1656868 < baseStart_1656868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656938 : List Nat := [3, 1, 3, 2, 4, 8]
def baseStart_1656938 : Nat := 118140960795 + 1656938 * 2 ^ 59
def prefixEnd_1656938 : Nat := 4983230072969 + 3 ^ 40 * 1656938 * 2
def baseEnd_1656938 : Nat := 14005030595877258537529

theorem tailTrace_1656938 : CollatzResearch.WordTrace tailWord_1656938 prefixEnd_1656938 14005030595877258537529 := by
  unfold tailWord_1656938
  simp only [CollatzResearch.WordTrace]
  refine ⟨15108373417801020831530867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40288995780802722217415645 15108373417801020831530867)
  ·
    refine ⟨22662560126701531247296301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15108373417801020831530867 22662560126701531247296301)
    ·
      refine ⟨8498460047513074217736113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22662560126701531247296301 8498460047513074217736113)
      ·
        refine ⟨6373845035634805663302085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8498460047513074217736113 6373845035634805663302085)
        ·
          refine ⟨1195095944181526061869141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6373845035634805663302085 1195095944181526061869141)
          ·
            refine ⟨14005030595877258537529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1195095944181526061869141 14005030595877258537529)
            ·
              rfl

theorem cell21_1656938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 8].length) (baseStart_1656938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1656938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1656938 prefixEnd_1656938 := by exact prefixLift 1656938
  have htrace : WordTrace (prefixWord ++ tailWord_1656938) baseStart_1656938 baseEnd_1656938 := by
    simpa [prefixWord, tailWord_1656938, baseEnd_1656938] using wordTrace_append hprefix tailTrace_1656938
  have hstable : (prefixWord ++ tailWord_1656938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656938).length < 2 ^ (prefixWord ++ tailWord_1656938).sum := by decide
  have hdescent : baseEnd_1656938 < baseStart_1656938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657087 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 7]
def baseStart_1657087 : Nat := 118140960795 + 1657087 * 2 ^ 59
def prefixEnd_1657087 : Nat := 4983230072969 + 3 ^ 40 * 1657087 * 2
def baseEnd_1657087 : Nat := 378169829918694832529645

theorem tailTrace_1657087 : CollatzResearch.WordTrace tailWord_1657087 prefixEnd_1657087 378169829918694832529645 := by
  unfold tailWord_1657087
  simp only [CollatzResearch.WordTrace]
  refine ⟨60438928147664281773297515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40292618765109521182198343 60438928147664281773297515)
  ·
    refine ⟨90658392221496422659946273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60438928147664281773297515 90658392221496422659946273)
    ·
      refine ⟨67993794166122316994959705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90658392221496422659946273 67993794166122316994959705)
      ·
        refine ⟨50995345624591737746219779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67993794166122316994959705 50995345624591737746219779)
        ·
          refine ⟨76493018436887606619329669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50995345624591737746219779 76493018436887606619329669)
          ·
            refine ⟨14342440956916426241124313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76493018436887606619329669 14342440956916426241124313)
            ·
              refine ⟨10756830717687319680843235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14342440956916426241124313 10756830717687319680843235)
              ·
                refine ⟨16135246076530979521264853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10756830717687319680843235 16135246076530979521264853)
                ·
                  refine ⟨378169829918694832529645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16135246076530979521264853 378169829918694832529645)
                  ·
                    rfl

theorem cell21_1657087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 7].length) (baseStart_1657087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1657087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1657087 prefixEnd_1657087 := by exact prefixLift 1657087
  have htrace : WordTrace (prefixWord ++ tailWord_1657087) baseStart_1657087 baseEnd_1657087 := by
    simpa [prefixWord, tailWord_1657087, baseEnd_1657087] using wordTrace_append hprefix tailTrace_1657087
  have hstable : (prefixWord ++ tailWord_1657087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657087).length < 2 ^ (prefixWord ++ tailWord_1657087).sum := by decide
  have hdescent : baseEnd_1657087 < baseStart_1657087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657090 : List Nat := [3, 4, 1, 1, 2, 1, 2, 7]
def baseStart_1657090 : Nat := 118140960795 + 1657090 * 2 ^ 59
def prefixEnd_1657090 : Nat := 4983230072969 + 3 ^ 40 * 1657090 * 2
def baseEnd_1657090 : Nat := 126056838186522497993213

theorem tailTrace_1657090 : CollatzResearch.WordTrace tailWord_1657090 prefixEnd_1657090 126056838186522497993213 := by
  unfold tailWord_1657090
  simp only [CollatzResearch.WordTrace]
  refine ⟨15109759391663353321414181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40292691711102275523771149 15109759391663353321414181)
  ·
    refine ⟨2833079885936878747765159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15109759391663353321414181 2833079885936878747765159)
    ·
      refine ⟨4249619828905318121647739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2833079885936878747765159 4249619828905318121647739)
      ·
        refine ⟨6374429743357977182471609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4249619828905318121647739 6374429743357977182471609)
        ·
          refine ⟨4780822307518482886853707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6374429743357977182471609 4780822307518482886853707)
          ·
            refine ⟨7171233461277724330280561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4780822307518482886853707 7171233461277724330280561)
            ·
              refine ⟨5378425095958293247710421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7171233461277724330280561 5378425095958293247710421)
              ·
                refine ⟨126056838186522497993213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5378425095958293247710421 126056838186522497993213)
                ·
                  rfl

theorem cell21_1657090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 7].length) (baseStart_1657090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1657090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1657090 prefixEnd_1657090 := by exact prefixLift 1657090
  have htrace : WordTrace (prefixWord ++ tailWord_1657090) baseStart_1657090 baseEnd_1657090 := by
    simpa [prefixWord, tailWord_1657090, baseEnd_1657090] using wordTrace_append hprefix tailTrace_1657090
  have hstable : (prefixWord ++ tailWord_1657090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657090).length < 2 ^ (prefixWord ++ tailWord_1657090).sum := by decide
  have hdescent : baseEnd_1657090 < baseStart_1657090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657225 : List Nat := [1, 2, 1, 1, 6, 3, 7]
def baseStart_1657225 : Nat := 118140960795 + 1657225 * 2 ^ 59
def prefixEnd_1657225 : Nat := 4983230072969 + 3 ^ 40 * 1657225 * 2
def baseEnd_1657225 : Nat := 42022369266537473247707

theorem tailTrace_1657225 : CollatzResearch.WordTrace tailWord_1657225 prefixEnd_1657225 42022369266537473247707 := by
  unfold tailWord_1657225
  simp only [CollatzResearch.WordTrace]
  refine ⟨60443961421164331341821129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40295974280776220894547419 60443961421164331341821129)
  ·
    refine ⟨45332971065873248506365847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60443961421164331341821129 45332971065873248506365847)
    ·
      refine ⟨67999456598809872759548771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45332971065873248506365847 67999456598809872759548771)
      ·
        refine ⟨101999184898214809139323157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67999456598809872759548771 101999184898214809139323157)
        ·
          refine ⟨4781211792103819178405773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 101999184898214809139323157 4781211792103819178405773)
          ·
            refine ⟨1792954422038932191902165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4781211792103819178405773 1792954422038932191902165)
            ·
              refine ⟨42022369266537473247707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1792954422038932191902165 42022369266537473247707)
              ·
                rfl

theorem cell21_1657225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 7].length) (baseStart_1657225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1657225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1657225 prefixEnd_1657225 := by exact prefixLift 1657225
  have htrace : WordTrace (prefixWord ++ tailWord_1657225) baseStart_1657225 baseEnd_1657225 := by
    simpa [prefixWord, tailWord_1657225, baseEnd_1657225] using wordTrace_append hprefix tailTrace_1657225
  have hstable : (prefixWord ++ tailWord_1657225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657225).length < 2 ^ (prefixWord ++ tailWord_1657225).sum := by decide
  have hdescent : baseEnd_1657225 < baseStart_1657225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657245 : List Nat := [1, 4, 2, 1, 4, 2, 2, 1, 4]
def baseStart_1657245 : Nat := 118140960795 + 1657245 * 2 ^ 59
def prefixEnd_1657245 : Nat := 4983230072969 + 3 ^ 40 * 1657245 * 2
def baseEnd_1657245 : Nat := 378205887671321668895989

theorem tailTrace_1657245 : CollatzResearch.WordTrace tailWord_1657245 prefixEnd_1657245 378205887671321668895989 := by
  unfold tailWord_1657245
  simp only [CollatzResearch.WordTrace]
  refine ⟨60444690881091874757549189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40296460587394583171699459 60444690881091874757549189)
  ·
    refine ⟨11333379540204726517040473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60444690881091874757549189 11333379540204726517040473)
    ·
      refine ⟨8500034655153544887780355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11333379540204726517040473 8500034655153544887780355)
      ·
        refine ⟨12750051982730317331670533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8500034655153544887780355 12750051982730317331670533)
        ·
          refine ⟨2390634746761934499688225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12750051982730317331670533 2390634746761934499688225)
          ·
            refine ⟨1792976060071450874766169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2390634746761934499688225 1792976060071450874766169)
            ·
              refine ⟨1344732045053588156074627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1792976060071450874766169 1344732045053588156074627)
              ·
                refine ⟨2017098067580382234111941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1344732045053588156074627 2017098067580382234111941)
                ·
                  refine ⟨378205887671321668895989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2017098067580382234111941 378205887671321668895989)
                  ·
                    rfl

theorem cell21_1657245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_1657245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1657245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1657245 prefixEnd_1657245 := by exact prefixLift 1657245
  have htrace : WordTrace (prefixWord ++ tailWord_1657245) baseStart_1657245 baseEnd_1657245 := by
    simpa [prefixWord, tailWord_1657245, baseEnd_1657245] using wordTrace_append hprefix tailTrace_1657245
  have hstable : (prefixWord ++ tailWord_1657245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657245).length < 2 ^ (prefixWord ++ tailWord_1657245).sum := by decide
  have hdescent : baseEnd_1657245 < baseStart_1657245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657287 : List Nat := [1, 1, 4, 1, 1, 5, 2, 2, 4]
def baseStart_1657287 : Nat := 118140960795 + 1657287 * 2 ^ 59
def prefixEnd_1657287 : Nat := 4983230072969 + 3 ^ 40 * 1657287 * 2
def baseEnd_1657287 : Nat := 378215472643538929195903

theorem tailTrace_1657287 : CollatzResearch.WordTrace tailWord_1657287 prefixEnd_1657287 378215472643538929195903 := by
  unfold tailWord_1657287
  simp only [CollatzResearch.WordTrace]
  refine ⟨60446222746939715930578115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40297481831293143953718743 60446222746939715930578115)
  ·
    refine ⟨90669334120409573895867173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60446222746939715930578115 90669334120409573895867173)
    ·
      refine ⟨17000500147576795105475095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90669334120409573895867173 17000500147576795105475095)
      ·
        refine ⟨25500750221365192658212643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17000500147576795105475095 25500750221365192658212643)
        ·
          refine ⟨38251125332047788987318965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25500750221365192658212643 38251125332047788987318965)
          ·
            refine ⟨3586042999879480217561153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38251125332047788987318965 3586042999879480217561153)
            ·
              refine ⟨2689532249909610163170865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3586042999879480217561153 2689532249909610163170865)
              ·
                refine ⟨2017149187432207622378149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2689532249909610163170865 2017149187432207622378149)
                ·
                  refine ⟨378215472643538929195903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2017149187432207622378149 378215472643538929195903)
                  ·
                    rfl

theorem cell21_1657287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 4].length) (baseStart_1657287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1657287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1657287 prefixEnd_1657287 := by exact prefixLift 1657287
  have htrace : WordTrace (prefixWord ++ tailWord_1657287) baseStart_1657287 baseEnd_1657287 := by
    simpa [prefixWord, tailWord_1657287, baseEnd_1657287] using wordTrace_append hprefix tailTrace_1657287
  have hstable : (prefixWord ++ tailWord_1657287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657287).length < 2 ^ (prefixWord ++ tailWord_1657287).sum := by decide
  have hdescent : baseEnd_1657287 < baseStart_1657287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657301 : List Nat := [1, 3, 2, 3, 1, 2, 3, 6]
def baseStart_1657301 : Nat := 118140960795 + 1657301 * 2 ^ 59
def prefixEnd_1657301 : Nat := 4983230072969 + 3 ^ 40 * 1657301 * 2
def baseEnd_1657301 : Nat := 126072889211426005320847

theorem tailTrace_1657301 : CollatzResearch.WordTrace tailWord_1657301 prefixEnd_1657301 126072889211426005320847 := by
  unfold tailWord_1657301
  simp only [CollatzResearch.WordTrace]
  refine ⟨60446733368888996321587757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40297822245925997547725171 60446733368888996321587757)
  ·
    refine ⟨22667525013333373620595409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60446733368888996321587757 22667525013333373620595409)
    ·
      refine ⟨17000643760000030215446557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22667525013333373620595409 17000643760000030215446557)
      ·
        refine ⟨6375241410000011330792459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17000643760000030215446557 6375241410000011330792459)
        ·
          refine ⟨9562862115000016996188689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6375241410000011330792459 9562862115000016996188689)
          ·
            refine ⟨7172146586250012747141517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9562862115000016996188689 7172146586250012747141517)
            ·
              refine ⟨2689554969843754780178069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7172146586250012747141517 2689554969843754780178069)
              ·
                refine ⟨126072889211426005320847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2689554969843754780178069 126072889211426005320847)
                ·
                  rfl

theorem cell21_1657301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 6].length) (baseStart_1657301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1657301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1657301 prefixEnd_1657301 := by exact prefixLift 1657301
  have htrace : WordTrace (prefixWord ++ tailWord_1657301) baseStart_1657301 baseEnd_1657301 := by
    simpa [prefixWord, tailWord_1657301, baseEnd_1657301] using wordTrace_append hprefix tailTrace_1657301
  have hstable : (prefixWord ++ tailWord_1657301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657301).length < 2 ^ (prefixWord ++ tailWord_1657301).sum := by decide
  have hdescent : baseEnd_1657301 < baseStart_1657301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657363 : List Nat := [1, 1, 1, 2, 1, 5, 5, 1, 4]
def baseStart_1657363 : Nat := 118140960795 + 1657363 * 2 ^ 59
def prefixEnd_1657363 : Nat := 4983230072969 + 3 ^ 40 * 1657363 * 2
def baseEnd_1657363 : Nat := 378232816878979685929081

theorem tailTrace_1657363 : CollatzResearch.WordTrace tailWord_1657363 prefixEnd_1657363 378232816878979685929081 := by
  unfold tailWord_1657363
  simp only [CollatzResearch.WordTrace]
  refine ⟨60448994694664380910344743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40299329796442920606896495 60448994694664380910344743)
  ·
    refine ⟨90673492041996571365517115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60448994694664380910344743 90673492041996571365517115)
    ·
      refine ⟨136010238062994857048275673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90673492041996571365517115 136010238062994857048275673)
      ·
        refine ⟨102007678547246142786206755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136010238062994857048275673 102007678547246142786206755)
        ·
          refine ⟨153011517820869214179310133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102007678547246142786206755 153011517820869214179310133)
          ·
            refine ⟨14344829795706488829310325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 153011517820869214179310133 14344829795706488829310325)
            ·
              refine ⟨1344827793347483327747843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14344829795706488829310325 1344827793347483327747843)
              ·
                refine ⟨2017241690021224991621765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1344827793347483327747843 2017241690021224991621765)
                ·
                  refine ⟨378232816878979685929081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2017241690021224991621765 378232816878979685929081)
                  ·
                    rfl

theorem cell21_1657363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 4].length) (baseStart_1657363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1657363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1657363 prefixEnd_1657363 := by exact prefixLift 1657363
  have htrace : WordTrace (prefixWord ++ tailWord_1657363) baseStart_1657363 baseEnd_1657363 := by
    simpa [prefixWord, tailWord_1657363, baseEnd_1657363] using wordTrace_append hprefix tailTrace_1657363
  have hstable : (prefixWord ++ tailWord_1657363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657363).length < 2 ^ (prefixWord ++ tailWord_1657363).sum := by decide
  have hdescent : baseEnd_1657363 < baseStart_1657363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657408 : List Nat := [2, 1, 1, 2, 2, 2, 2, 6, 3]
def baseStart_1657408 : Nat := 118140960795 + 1657408 * 2 ^ 59
def prefixEnd_1657408 : Nat := 4983230072969 + 3 ^ 40 * 1657408 * 2
def baseEnd_1657408 : Nat := 378243086492069607678989

theorem tailTrace_1657408 : CollatzResearch.WordTrace tailWord_1657408 prefixEnd_1657408 378243086492069607678989 := by
  unfold tailWord_1657408
  simp only [CollatzResearch.WordTrace]
  refine ⟨30225317989750676797866439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40300423986334235730488585 30225317989750676797866439)
  ·
    refine ⟨45337976984626015196799659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30225317989750676797866439 45337976984626015196799659)
    ·
      refine ⟨68006965476939022795199489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45337976984626015196799659 68006965476939022795199489)
      ·
        refine ⟨51005224107704267096399617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68006965476939022795199489 51005224107704267096399617)
        ·
          refine ⟨38253918080778200322299713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51005224107704267096399617 38253918080778200322299713)
          ·
            refine ⟨28690438560583650241724785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38253918080778200322299713 28690438560583650241724785)
            ·
              refine ⟨21517828920437737681293589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28690438560583650241724785 21517828920437737681293589)
              ·
                refine ⟨1008648230645518953810637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21517828920437737681293589 1008648230645518953810637)
                ·
                  refine ⟨378243086492069607678989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1008648230645518953810637 378243086492069607678989)
                  ·
                    rfl

theorem cell21_1657408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6, 3].length) (baseStart_1657408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1657408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1657408 prefixEnd_1657408 := by exact prefixLift 1657408
  have htrace : WordTrace (prefixWord ++ tailWord_1657408) baseStart_1657408 baseEnd_1657408 := by
    simpa [prefixWord, tailWord_1657408, baseEnd_1657408] using wordTrace_append hprefix tailTrace_1657408
  have hstable : (prefixWord ++ tailWord_1657408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657408).length < 2 ^ (prefixWord ++ tailWord_1657408).sum := by decide
  have hdescent : baseEnd_1657408 < baseStart_1657408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657414 : List Nat := [6, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_1657414 : Nat := 118140960795 + 1657414 * 2 ^ 59
def prefixEnd_1657414 : Nat := 4983230072969 + 3 ^ 40 * 1657414 * 2
def baseEnd_1657414 : Nat := 378244455773814930578977

theorem tailTrace_1657414 : CollatzResearch.WordTrace tailWord_1657414 prefixEnd_1657414 378244455773814930578977 := by
  unfold tailWord_1657414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1889089213046238019389103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40300569878319744413634197 1889089213046238019389103)
  ·
    refine ⟨2833633819569357029083655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1889089213046238019389103 2833633819569357029083655)
    ·
      refine ⟨4250450729354035543625483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2833633819569357029083655 4250450729354035543625483)
      ·
        refine ⟨6375676094031053315438225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4250450729354035543625483 6375676094031053315438225)
        ·
          refine ⟨4781757070523289986578669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6375676094031053315438225 4781757070523289986578669)
          ·
            refine ⟨1793158901446233744967001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4781757070523289986578669 1793158901446233744967001)
            ·
              refine ⟨1344869176084675308725251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1793158901446233744967001 1344869176084675308725251)
              ·
                refine ⟨2017303764127012963087877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1344869176084675308725251 2017303764127012963087877)
                ·
                  refine ⟨378244455773814930578977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2017303764127012963087877 378244455773814930578977)
                  ·
                    rfl

theorem cell21_1657414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_1657414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1657414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1657414 prefixEnd_1657414 := by exact prefixLift 1657414
  have htrace : WordTrace (prefixWord ++ tailWord_1657414) baseStart_1657414 baseEnd_1657414 := by
    simpa [prefixWord, tailWord_1657414, baseEnd_1657414] using wordTrace_append hprefix tailTrace_1657414
  have hstable : (prefixWord ++ tailWord_1657414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657414).length < 2 ^ (prefixWord ++ tailWord_1657414).sum := by decide
  have hdescent : baseEnd_1657414 < baseStart_1657414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657481 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 8]
def baseStart_1657481 : Nat := 118140960795 + 1657481 * 2 ^ 59
def prefixEnd_1657481 : Nat := 4983230072969 + 3 ^ 40 * 1657481 * 2
def baseEnd_1657481 : Nat := 378259746086637702962173

theorem tailTrace_1657481 : CollatzResearch.WordTrace tailWord_1657481 prefixEnd_1657481 378259746086637702962173 := by
  unfold tailWord_1657481
  simp only [CollatzResearch.WordTrace]
  refine ⟨60453298508236887063140297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40302199005491258042093531 60453298508236887063140297)
  ·
    refine ⟨45339973881177665297355223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60453298508236887063140297 45339973881177665297355223)
    ·
      refine ⟨68009960821766497946032835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45339973881177665297355223 68009960821766497946032835)
      ·
        refine ⟨102014941232649746919049253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68009960821766497946032835 102014941232649746919049253)
        ·
          refine ⟨19127801481121827547321735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102014941232649746919049253 19127801481121827547321735)
          ·
            refine ⟨28691702221682741320982603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19127801481121827547321735 28691702221682741320982603)
            ·
              refine ⟨43037553332524111981473905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28691702221682741320982603 43037553332524111981473905)
              ·
                refine ⟨32278164999393083986105429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43037553332524111981473905 32278164999393083986105429)
                ·
                  refine ⟨378259746086637702962173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32278164999393083986105429 378259746086637702962173)
                  ·
                    rfl

theorem cell21_1657481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_1657481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1657481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1657481 prefixEnd_1657481 := by exact prefixLift 1657481
  have htrace : WordTrace (prefixWord ++ tailWord_1657481) baseStart_1657481 baseEnd_1657481 := by
    simpa [prefixWord, tailWord_1657481, baseEnd_1657481] using wordTrace_append hprefix tailTrace_1657481
  have hstable : (prefixWord ++ tailWord_1657481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657481).length < 2 ^ (prefixWord ++ tailWord_1657481).sum := by decide
  have hdescent : baseEnd_1657481 < baseStart_1657481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657518 : List Nat := [4, 1, 4, 1, 1, 1, 2, 4, 3]
def baseStart_1657518 : Nat := 118140960795 + 1657518 * 2 ^ 59
def prefixEnd_1657518 : Nat := 4983230072969 + 3 ^ 40 * 1657518 * 2
def baseEnd_1657518 : Nat := 378268189990733860845431

theorem tailTrace_1657518 : CollatzResearch.WordTrace tailWord_1657518 prefixEnd_1657518 378268189990733860845431 := by
  unfold tailWord_1657518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7556831001137855297779651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40303098672735228254824805 7556831001137855297779651)
  ·
    refine ⟨11335246501706782946669477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7556831001137855297779651 11335246501706782946669477)
    ·
      refine ⟨2125358719070021802500527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11335246501706782946669477 2125358719070021802500527)
      ·
        refine ⟨3188038078605032703750791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2125358719070021802500527 3188038078605032703750791)
        ·
          refine ⟨4782057117907549055626187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3188038078605032703750791 4782057117907549055626187)
          ·
            refine ⟨7173085676861323583439281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4782057117907549055626187 7173085676861323583439281)
            ·
              refine ⟨5379814257645992687579461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7173085676861323583439281 5379814257645992687579461)
              ·
                refine ⟨1008715173308623628921149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5379814257645992687579461 1008715173308623628921149)
                ·
                  refine ⟨378268189990733860845431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1008715173308623628921149 378268189990733860845431)
                  ·
                    rfl

theorem cell21_1657518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_1657518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1657518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1657518 prefixEnd_1657518 := by exact prefixLift 1657518
  have htrace : WordTrace (prefixWord ++ tailWord_1657518) baseStart_1657518 baseEnd_1657518 := by
    simpa [prefixWord, tailWord_1657518, baseEnd_1657518] using wordTrace_append hprefix tailTrace_1657518
  have hstable : (prefixWord ++ tailWord_1657518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657518).length < 2 ^ (prefixWord ++ tailWord_1657518).sum := by decide
  have hdescent : baseEnd_1657518 < baseStart_1657518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657546 : List Nat := [3, 1, 2, 1, 4, 3, 2, 5]
def baseStart_1657546 : Nat := 118140960795 + 1657546 * 2 ^ 59
def prefixEnd_1657546 : Nat := 4983230072969 + 3 ^ 40 * 1657546 * 2
def baseEnd_1657546 : Nat := 126091526657404011459569

theorem tailTrace_1657546 : CollatzResearch.WordTrace tailWord_1657546 prefixEnd_1657546 126091526657404011459569 := by
  unfold tailWord_1657546
  simp only [CollatzResearch.WordTrace]
  refine ⟨15113917313250350791064123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40303779502000935442837661 15113917313250350791064123)
  ·
    refine ⟨22670875969875526186596185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15113917313250350791064123 22670875969875526186596185)
    ·
      refine ⟨17003156977406644639947139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22670875969875526186596185 17003156977406644639947139)
      ·
        refine ⟨25504735466109966959920709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17003156977406644639947139 25504735466109966959920709)
        ·
          refine ⟨4782137899895618804985133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25504735466109966959920709 4782137899895618804985133)
          ·
            refine ⟨1793301712460857051869425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4782137899895618804985133 1793301712460857051869425)
            ·
              refine ⟨1344976284345642788902069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1793301712460857051869425 1344976284345642788902069)
              ·
                refine ⟨126091526657404011459569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1344976284345642788902069 126091526657404011459569)
                ·
                  rfl

theorem cell21_1657546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 5].length) (baseStart_1657546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1657546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1657546 prefixEnd_1657546 := by exact prefixLift 1657546
  have htrace : WordTrace (prefixWord ++ tailWord_1657546) baseStart_1657546 baseEnd_1657546 := by
    simpa [prefixWord, tailWord_1657546, baseEnd_1657546] using wordTrace_append hprefix tailTrace_1657546
  have hstable : (prefixWord ++ tailWord_1657546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657546).length < 2 ^ (prefixWord ++ tailWord_1657546).sum := by decide
  have hdescent : baseEnd_1657546 < baseStart_1657546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657650 : List Nat := [3, 2, 1, 1, 3, 1, 1, 5, 4]
def baseStart_1657650 : Nat := 118140960795 + 1657650 * 2 ^ 59
def prefixEnd_1657650 : Nat := 4983230072969 + 3 ^ 40 * 1657650 * 2
def baseEnd_1657650 : Nat := 378298314189130964645161

theorem tailTrace_1657650 : CollatzResearch.WordTrace tailWord_1657650 prefixEnd_1657650 378298314189130964645161 := by
  unfold tailWord_1657650
  simp only [CollatzResearch.WordTrace]
  refine ⟨15114865611156157231510601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40306308296416419284028269 15114865611156157231510601)
  ·
    refine ⟨11336149208367117923632951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15114865611156157231510601 11336149208367117923632951)
    ·
      refine ⟨17004223812550676885449427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11336149208367117923632951 17004223812550676885449427)
      ·
        refine ⟨25506335718826015328174141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17004223812550676885449427 25506335718826015328174141)
        ·
          refine ⟨9564875894559755748065303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25506335718826015328174141 9564875894559755748065303)
          ·
            refine ⟨14347313841839633622097955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9564875894559755748065303 14347313841839633622097955)
            ·
              refine ⟨21520970762759450433146933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14347313841839633622097955 21520970762759450433146933)
              ·
                refine ⟨2017591009008698478107525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21520970762759450433146933 2017591009008698478107525)
                ·
                  refine ⟨378298314189130964645161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2017591009008698478107525 378298314189130964645161)
                  ·
                    rfl

theorem cell21_1657650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_1657650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1657650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1657650 prefixEnd_1657650 := by exact prefixLift 1657650
  have htrace : WordTrace (prefixWord ++ tailWord_1657650) baseStart_1657650 baseEnd_1657650 := by
    simpa [prefixWord, tailWord_1657650, baseEnd_1657650] using wordTrace_append hprefix tailTrace_1657650
  have hstable : (prefixWord ++ tailWord_1657650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657650).length < 2 ^ (prefixWord ++ tailWord_1657650).sum := by decide
  have hdescent : baseEnd_1657650 < baseStart_1657650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657684 : List Nat := [2, 4, 1, 1, 4, 2, 1, 2, 4]
def baseStart_1657684 : Nat := 118140960795 + 1657684 * 2 ^ 59
def prefixEnd_1657684 : Nat := 4983230072969 + 3 ^ 40 * 1657684 * 2
def baseEnd_1657684 : Nat := 378306073452354461078425

theorem tailTrace_1657684 : CollatzResearch.WordTrace tailWord_1657684 prefixEnd_1657684 378306073452354461078425 := by
  unfold tailWord_1657684
  simp only [CollatzResearch.WordTrace]
  refine ⟨30230351263250726366390053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40307135017667635155186737 30230351263250726366390053)
  ·
    refine ⟨5668190861859511193698135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30230351263250726366390053 5668190861859511193698135)
    ·
      refine ⟨8502286292789266790547203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5668190861859511193698135 8502286292789266790547203)
      ·
        refine ⟨12753429439183900185820805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8502286292789266790547203 12753429439183900185820805)
        ·
          refine ⟨2391268019846981284841401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12753429439183900185820805 2391268019846981284841401)
          ·
            refine ⟨1793451014885235963631051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2391268019846981284841401 1793451014885235963631051)
            ·
              refine ⟨2690176522327853945446577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1793451014885235963631051 2690176522327853945446577)
              ·
                refine ⟨2017632391745890459084933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2690176522327853945446577 2017632391745890459084933)
                ·
                  refine ⟨378306073452354461078425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2017632391745890459084933 378306073452354461078425)
                  ·
                    rfl

theorem cell21_1657684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_1657684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1657684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1657684 prefixEnd_1657684 := by exact prefixLift 1657684
  have htrace : WordTrace (prefixWord ++ tailWord_1657684) baseStart_1657684 baseEnd_1657684 := by
    simpa [prefixWord, tailWord_1657684, baseEnd_1657684] using wordTrace_append hprefix tailTrace_1657684
  have hstable : (prefixWord ++ tailWord_1657684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657684).length < 2 ^ (prefixWord ++ tailWord_1657684).sum := by decide
  have hdescent : baseEnd_1657684 < baseStart_1657684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657695 : List Nat := [1, 1, 2, 3, 1, 3, 4, 1, 5]
def baseStart_1657695 : Nat := 118140960795 + 1657695 * 2 ^ 59
def prefixEnd_1657695 : Nat := 4983230072969 + 3 ^ 40 * 1657695 * 2
def baseEnd_1657695 : Nat := 378308583802220886395069

theorem tailTrace_1657695 : CollatzResearch.WordTrace tailWord_1657695 prefixEnd_1657695 378308583802220886395069 := by
  unfold tailWord_1657695
  simp only [CollatzResearch.WordTrace]
  refine ⟨60461103729461601611430539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40307402486307734407620359 60461103729461601611430539)
  ·
    refine ⟨90691655594192402417145809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60461103729461601611430539 90691655594192402417145809)
    ·
      refine ⟨68018741695644301812859357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90691655594192402417145809 68018741695644301812859357)
      ·
        refine ⟨25507028135866613179822259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68018741695644301812859357 25507028135866613179822259)
        ·
          refine ⟨38260542203799919769733389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25507028135866613179822259 38260542203799919769733389)
          ·
            refine ⟨14347703326424969913650021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38260542203799919769733389 14347703326424969913650021)
            ·
              refine ⟨2690194373704681858809379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14347703326424969913650021 2690194373704681858809379)
              ·
                refine ⟨4035291560557022788214069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2690194373704681858809379 4035291560557022788214069)
                ·
                  refine ⟨378308583802220886395069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4035291560557022788214069 378308583802220886395069)
                  ·
                    rfl

theorem cell21_1657695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 5].length) (baseStart_1657695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1657695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1657695 prefixEnd_1657695 := by exact prefixLift 1657695
  have htrace : WordTrace (prefixWord ++ tailWord_1657695) baseStart_1657695 baseEnd_1657695 := by
    simpa [prefixWord, tailWord_1657695, baseEnd_1657695] using wordTrace_append hprefix tailTrace_1657695
  have hstable : (prefixWord ++ tailWord_1657695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657695).length < 2 ^ (prefixWord ++ tailWord_1657695).sum := by decide
  have hdescent : baseEnd_1657695 < baseStart_1657695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
