import V185TrunkScan23Chunk0076

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_456878 : List Nat := [4, 1, 4, 2, 1, 1, 3, 1, 2, 4]
def baseStart_456878 : Nat := 118140960795 + 456878 * 2 ^ 59
def prefixEnd_456878 : Nat := 4983230072969 + 3 ^ 40 * 456878 * 2
def baseEnd_456878 : Nat := 78199338154989565474621

theorem tailTrace_456878 : CollatzResearch.WordTrace tailWord_456878 prefixEnd_456878 78199338154989565474621 := by
  unfold tailWord_456878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2082963704852063674417411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11109139759211006263559525 2082963704852063674417411)
  ·
    refine ⟨3124445557278095511626117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2082963704852063674417411 3124445557278095511626117)
    ·
      refine ⟨585833541989642908429897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3124445557278095511626117 585833541989642908429897)
      ·
        refine ⟨439375156492232181322423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 585833541989642908429897 439375156492232181322423)
        ·
          refine ⟨659062734738348271983635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439375156492232181322423 659062734738348271983635)
          ·
            refine ⟨988594102107522407975453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659062734738348271983635 988594102107522407975453)
            ·
              refine ⟨370722788290320902990795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 988594102107522407975453 370722788290320902990795)
              ·
                refine ⟨556084182435481354486193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370722788290320902990795 556084182435481354486193)
                ·
                  refine ⟨417063136826611015864645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 556084182435481354486193 417063136826611015864645)
                  ·
                    refine ⟨78199338154989565474621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 417063136826611015864645 78199338154989565474621)
                    ·
                      rfl

theorem cell23_456878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_456878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456878 prefixEnd_456878 := by exact prefixLift 456878
  have htrace : WordTrace (prefixWord ++ tailWord_456878) baseStart_456878 baseEnd_456878 := by
    simpa [prefixWord, tailWord_456878, baseEnd_456878] using wordTrace_append hprefix tailTrace_456878
  have hstable : (prefixWord ++ tailWord_456878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456878).length < 2 ^ (prefixWord ++ tailWord_456878).sum := by decide
  have hdescent : baseEnd_456878 < baseStart_456878 := by decide
  rcases family_descends (prefixWord ++ tailWord_456878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456907 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 6, 2, 2]
def baseStart_456907 : Nat := 118140960795 + 456907 * 2 ^ 59
def prefixEnd_456907 : Nat := 4983230072969 + 3 ^ 40 * 456907 * 2
def baseEnd_456907 : Nat := 234612905403949082961229

theorem tailTrace_456907 : CollatzResearch.WordTrace tailWord_456907 prefixEnd_456907 234612905403949082961229 := by
  unfold tailWord_456907
  simp only [CollatzResearch.WordTrace]
  refine ⟨16664767355711447348144975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11109844903807631565429983 16664767355711447348144975)
  ·
    refine ⟨24997151033567171022217463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16664767355711447348144975 24997151033567171022217463)
    ·
      refine ⟨37495726550350756533326195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24997151033567171022217463 37495726550350756533326195)
      ·
        refine ⟨56243589825526134799989293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37495726550350756533326195 56243589825526134799989293)
        ·
          refine ⟨21091346184572300549995985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56243589825526134799989293 21091346184572300549995985)
          ·
            refine ⟨15818509638429225412496989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21091346184572300549995985 15818509638429225412496989)
            ·
              refine ⟨5931941114410959529686371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15818509638429225412496989 5931941114410959529686371)
              ·
                refine ⟨8897911671616439294529557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5931941114410959529686371 8897911671616439294529557)
                ·
                  refine ⟨417089609607020591931073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8897911671616439294529557 417089609607020591931073)
                  ·
                    refine ⟨312817207205265443948305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 417089609607020591931073 312817207205265443948305)
                    ·
                      refine ⟨234612905403949082961229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 312817207205265443948305 234612905403949082961229)
                      ·
                        rfl

theorem cell23_456907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6, 2, 2].length) (baseStart_456907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456907 prefixEnd_456907 := by exact prefixLift 456907
  have htrace : WordTrace (prefixWord ++ tailWord_456907) baseStart_456907 baseEnd_456907 := by
    simpa [prefixWord, tailWord_456907, baseEnd_456907] using wordTrace_append hprefix tailTrace_456907
  have hstable : (prefixWord ++ tailWord_456907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456907).length < 2 ^ (prefixWord ++ tailWord_456907).sum := by decide
  have hdescent : baseEnd_456907 < baseStart_456907 := by decide
  rcases family_descends (prefixWord ++ tailWord_456907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456910 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5]
def baseStart_456910 : Nat := 118140960795 + 456910 * 2 ^ 59
def prefixEnd_456910 : Nat := 4983230072969 + 3 ^ 40 * 456910 * 2
def baseEnd_456910 : Nat := 234614445845912571223715

theorem tailTrace_456910 : CollatzResearch.WordTrace tailWord_456910 prefixEnd_456910 234614445845912571223715 := by
  unfold tailWord_456910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2083109596837572357563023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11109917849800385907002789 2083109596837572357563023)
  ·
    refine ⟨3124664395256358536344535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2083109596837572357563023 3124664395256358536344535)
    ·
      refine ⟨4686996592884537804516803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3124664395256358536344535 4686996592884537804516803)
      ·
        refine ⟨7030494889326806706775205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4686996592884537804516803 7030494889326806706775205)
        ·
          refine ⟨1318217791748776257520351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7030494889326806706775205 1318217791748776257520351)
          ·
            refine ⟨1977326687623164386280527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1318217791748776257520351 1977326687623164386280527)
            ·
              refine ⟨2965990031434746579420791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1977326687623164386280527 2965990031434746579420791)
              ·
                refine ⟨4448985047152119869131187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2965990031434746579420791 4448985047152119869131187)
                ·
                  refine ⟨6673477570728179803696781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4448985047152119869131187 6673477570728179803696781)
                  ·
                    refine ⟨2502554089023067426386293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6673477570728179803696781 2502554089023067426386293)
                    ·
                      refine ⟨234614445845912571223715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2502554089023067426386293 234614445845912571223715)
                      ·
                        rfl

theorem cell23_456910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_456910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456910 prefixEnd_456910 := by exact prefixLift 456910
  have htrace : WordTrace (prefixWord ++ tailWord_456910) baseStart_456910 baseEnd_456910 := by
    simpa [prefixWord, tailWord_456910, baseEnd_456910] using wordTrace_append hprefix tailTrace_456910
  have hstable : (prefixWord ++ tailWord_456910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456910).length < 2 ^ (prefixWord ++ tailWord_456910).sum := by decide
  have hdescent : baseEnd_456910 < baseStart_456910 := by decide
  rcases family_descends (prefixWord ++ tailWord_456910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456913 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 9]
def baseStart_456913 : Nat := 118140960795 + 456913 * 2 ^ 59
def prefixEnd_456913 : Nat := 4983230072969 + 3 ^ 40 * 456913 * 2
def baseEnd_456913 : Nat := 26068442920875117720689

theorem tailTrace_456913 : CollatzResearch.WordTrace tailWord_456913 prefixEnd_456913 26068442920875117720689 := by
  unfold tailWord_456913
  simp only [CollatzResearch.WordTrace]
  refine ⟨16664986193689710372863393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11109990795793140248575595 16664986193689710372863393)
  ·
    refine ⟨12498739645267282779647545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16664986193689710372863393 12498739645267282779647545)
    ·
      refine ⟨9374054733950462084735659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12498739645267282779647545 9374054733950462084735659)
      ·
        refine ⟨14061082100925693127103489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9374054733950462084735659 14061082100925693127103489)
        ·
          refine ⟨10545811575694269845327617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14061082100925693127103489 10545811575694269845327617)
          ·
            refine ⟨7909358681770702383995713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10545811575694269845327617 7909358681770702383995713)
            ·
              refine ⟨5932019011328026787996785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7909358681770702383995713 5932019011328026787996785)
              ·
                refine ⟨4449014258496020090997589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5932019011328026787996785 4449014258496020090997589)
                ·
                  refine ⟨26068442920875117720689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4449014258496020090997589 26068442920875117720689)
                  ·
                    rfl

theorem cell23_456913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 9].length) (baseStart_456913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456913 prefixEnd_456913 := by exact prefixLift 456913
  have htrace : WordTrace (prefixWord ++ tailWord_456913) baseStart_456913 baseEnd_456913 := by
    simpa [prefixWord, tailWord_456913, baseEnd_456913] using wordTrace_append hprefix tailTrace_456913
  have hstable : (prefixWord ++ tailWord_456913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456913).length < 2 ^ (prefixWord ++ tailWord_456913).sum := by decide
  have hdescent : baseEnd_456913 < baseStart_456913 := by decide
  rcases family_descends (prefixWord ++ tailWord_456913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456940 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 3]
def baseStart_456940 : Nat := 118140960795 + 456940 * 2 ^ 59
def prefixEnd_456940 : Nat := 4983230072969 + 3 ^ 40 * 456940 * 2
def baseEnd_456940 : Nat := 234629850265547453848577

theorem tailTrace_456940 : CollatzResearch.WordTrace tailWord_456940 prefixEnd_456940 234629850265547453848577 := by
  unfold tailWord_456940
  simp only [CollatzResearch.WordTrace]
  refine ⟨8332985482295946992048137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11110647309727929322730849 8332985482295946992048137)
  ·
    refine ⟨6249739111721960244036103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8332985482295946992048137 6249739111721960244036103)
    ·
      refine ⟨9374608667582940366054155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6249739111721960244036103 9374608667582940366054155)
      ·
        refine ⟨14061913001374410549081233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9374608667582940366054155 14061913001374410549081233)
        ·
          refine ⟨10546434751030807911810925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14061913001374410549081233 10546434751030807911810925)
          ·
            refine ⟨3954913031636552966929097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10546434751030807911810925 3954913031636552966929097)
            ·
              refine ⟨2966184773727414725196823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3954913031636552966929097 2966184773727414725196823)
              ·
                refine ⟨4449277160591122087795235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2966184773727414725196823 4449277160591122087795235)
                ·
                  refine ⟨6673915740886683131692853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4449277160591122087795235 6673915740886683131692853)
                  ·
                    refine ⟨625679600708126543596205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6673915740886683131692853 625679600708126543596205)
                    ·
                      refine ⟨234629850265547453848577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 625679600708126543596205 234629850265547453848577)
                      ·
                        rfl

theorem cell23_456940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 3].length) (baseStart_456940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456940 prefixEnd_456940 := by exact prefixLift 456940
  have htrace : WordTrace (prefixWord ++ tailWord_456940) baseStart_456940 baseEnd_456940 := by
    simpa [prefixWord, tailWord_456940, baseEnd_456940] using wordTrace_append hprefix tailTrace_456940
  have hstable : (prefixWord ++ tailWord_456940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456940).length < 2 ^ (prefixWord ++ tailWord_456940).sum := by decide
  have hdescent : baseEnd_456940 < baseStart_456940 := by decide
  rcases family_descends (prefixWord ++ tailWord_456940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456960 : List Nat := [2, 1, 1, 2, 1, 1, 5, 3, 2, 5]
def baseStart_456960 : Nat := 118140960795 + 456960 * 2 ^ 59
def prefixEnd_456960 : Nat := 4983230072969 + 3 ^ 40 * 456960 * 2
def baseEnd_456960 : Nat := 78213373292879125199495

theorem tailTrace_456960 : CollatzResearch.WordTrace tailWord_456960 prefixEnd_456960 78213373292879125199495 := by
  unfold tailWord_456960
  simp only [CollatzResearch.WordTrace]
  refine ⟨8333350212259718699912167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11111133616346291599882889 8333350212259718699912167)
  ·
    refine ⟨12500025318389578049868251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8333350212259718699912167 12500025318389578049868251)
    ·
      refine ⟨18750037977584367074802377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12500025318389578049868251 18750037977584367074802377)
      ·
        refine ⟨14062528483188275306101783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18750037977584367074802377 14062528483188275306101783)
        ·
          refine ⟨21093792724782412959152675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14062528483188275306101783 21093792724782412959152675)
          ·
            refine ⟨31640689087173619438729013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21093792724782412959152675 31640689087173619438729013)
            ·
              refine ⟨2966314601922526822380845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31640689087173619438729013 2966314601922526822380845)
              ·
                refine ⟨1112367975720947558392817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2966314601922526822380845 1112367975720947558392817)
                ·
                  refine ⟨834275981790710668794613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1112367975720947558392817 834275981790710668794613)
                  ·
                    refine ⟨78213373292879125199495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 834275981790710668794613 78213373292879125199495)
                    ·
                      rfl

theorem cell23_456960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 2, 5].length) (baseStart_456960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456960 prefixEnd_456960 := by exact prefixLift 456960
  have htrace : WordTrace (prefixWord ++ tailWord_456960) baseStart_456960 baseEnd_456960 := by
    simpa [prefixWord, tailWord_456960, baseEnd_456960] using wordTrace_append hprefix tailTrace_456960
  have hstable : (prefixWord ++ tailWord_456960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456960).length < 2 ^ (prefixWord ++ tailWord_456960).sum := by decide
  have hdescent : baseEnd_456960 < baseStart_456960 := by decide
  rcases family_descends (prefixWord ++ tailWord_456960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456970 : List Nat := [3, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5]
def baseStart_456970 : Nat := 118140960795 + 456970 * 2 ^ 59
def prefixEnd_456970 : Nat := 4983230072969 + 3 ^ 40 * 456970 * 2
def baseEnd_456970 : Nat := 234645254685182336473439

theorem tailTrace_456970 : CollatzResearch.WordTrace tailWord_456970 prefixEnd_456970 234645254685182336473439 := by
  unfold tailWord_456970
  simp only [CollatzResearch.WordTrace]
  refine ⟨4166766288620802276922091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11111376769655472738458909 4166766288620802276922091)
  ·
    refine ⟨6250149432931203415383137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4166766288620802276922091 6250149432931203415383137)
    ·
      refine ⟨4687612074698402561537353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6250149432931203415383137 4687612074698402561537353)
      ·
        refine ⟨3515709056023801921153015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4687612074698402561537353 3515709056023801921153015)
        ·
          refine ⟨5273563584035702881729523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3515709056023801921153015 5273563584035702881729523)
          ·
            refine ⟨7910345376053554322594285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5273563584035702881729523 7910345376053554322594285)
            ·
              refine ⟨2966379516020082870972857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7910345376053554322594285 2966379516020082870972857)
              ·
                refine ⟨2224784637015062153229643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2966379516020082870972857 2224784637015062153229643)
                ·
                  refine ⟨3337176955522593229844465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2224784637015062153229643 3337176955522593229844465)
                  ·
                    refine ⟨2502882716641944922383349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3337176955522593229844465 2502882716641944922383349)
                    ·
                      refine ⟨234645254685182336473439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2502882716641944922383349 234645254685182336473439)
                      ·
                        rfl

theorem cell23_456970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_456970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_456970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_456970 prefixEnd_456970 := by exact prefixLift 456970
  have htrace : WordTrace (prefixWord ++ tailWord_456970) baseStart_456970 baseEnd_456970 := by
    simpa [prefixWord, tailWord_456970, baseEnd_456970] using wordTrace_append hprefix tailTrace_456970
  have hstable : (prefixWord ++ tailWord_456970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456970).length < 2 ^ (prefixWord ++ tailWord_456970).sum := by decide
  have hdescent : baseEnd_456970 < baseStart_456970 := by decide
  rcases family_descends (prefixWord ++ tailWord_456970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457020 : List Nat := [2, 2, 2, 2, 1, 2, 2, 2, 8]
def baseStart_457020 : Nat := 118140960795 + 457020 * 2 ^ 59
def prefixEnd_457020 : Nat := 4983230072969 + 3 ^ 40 * 457020 * 2
def baseEnd_457020 : Nat := 26074547635323015649801

theorem tailTrace_457020 : CollatzResearch.WordTrace tailWord_457020 prefixEnd_457020 26074547635323015649801 := by
  unfold tailWord_457020
  simp only [CollatzResearch.WordTrace]
  refine ⟨8334444402151033823504257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11112592536201378431339009 8334444402151033823504257)
  ·
    refine ⟨6250833301613275367628193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8334444402151033823504257 6250833301613275367628193)
    ·
      refine ⟨4688124976209956525721145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6250833301613275367628193 4688124976209956525721145)
      ·
        refine ⟨3516093732157467394290859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4688124976209956525721145 3516093732157467394290859)
        ·
          refine ⟨5274140598236201091436289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3516093732157467394290859 5274140598236201091436289)
          ·
            refine ⟨3955605448677150818577217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5274140598236201091436289 3955605448677150818577217)
            ·
              refine ⟨2966704086507863113932913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3955605448677150818577217 2966704086507863113932913)
              ·
                refine ⟨2225028064880897335449685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2966704086507863113932913 2225028064880897335449685)
                ·
                  refine ⟨26074547635323015649801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2225028064880897335449685 26074547635323015649801)
                  ·
                    rfl

theorem cell23_457020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 8].length) (baseStart_457020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457020 prefixEnd_457020 := by exact prefixLift 457020
  have htrace : WordTrace (prefixWord ++ tailWord_457020) baseStart_457020 baseEnd_457020 := by
    simpa [prefixWord, tailWord_457020, baseEnd_457020] using wordTrace_append hprefix tailTrace_457020
  have hstable : (prefixWord ++ tailWord_457020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457020).length < 2 ^ (prefixWord ++ tailWord_457020).sum := by decide
  have hdescent : baseEnd_457020 < baseStart_457020 := by decide
  rcases family_descends (prefixWord ++ tailWord_457020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457040 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 6]
def baseStart_457040 : Nat := 118140960795 + 457040 * 2 ^ 59
def prefixEnd_457040 : Nat := 4983230072969 + 3 ^ 40 * 457040 * 2
def baseEnd_457040 : Nat := 234681198330997062598117

theorem tailTrace_457040 : CollatzResearch.WordTrace tailWord_457040 prefixEnd_457040 234681198330997062598117 := by
  unfold tailWord_457040
  simp only [CollatzResearch.WordTrace]
  refine ⟨8334809132114805531368287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11113078842819740708491049 8334809132114805531368287)
  ·
    refine ⟨12502213698172208297052431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8334809132114805531368287 12502213698172208297052431)
    ·
      refine ⟨18753320547258312445578647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12502213698172208297052431 18753320547258312445578647)
      ·
        refine ⟨28129980820887468668367971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18753320547258312445578647 28129980820887468668367971)
        ·
          refine ⟨42194971231331203002551957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28129980820887468668367971 42194971231331203002551957)
          ·
            refine ⟨1977889276468650140744623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42194971231331203002551957 1977889276468650140744623)
            ·
              refine ⟨2966833914702975211116935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1977889276468650140744623 2966833914702975211116935)
              ·
                refine ⟨4450250872054462816675403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2966833914702975211116935 4450250872054462816675403)
                ·
                  refine ⟨6675376308081694225013105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4450250872054462816675403 6675376308081694225013105)
                  ·
                    refine ⟨5006532231061270668759829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6675376308081694225013105 5006532231061270668759829)
                    ·
                      refine ⟨234681198330997062598117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5006532231061270668759829 234681198330997062598117)
                      ·
                        rfl

theorem cell23_457040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 6].length) (baseStart_457040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457040 prefixEnd_457040 := by exact prefixLift 457040
  have htrace : WordTrace (prefixWord ++ tailWord_457040) baseStart_457040 baseEnd_457040 := by
    simpa [prefixWord, tailWord_457040, baseEnd_457040] using wordTrace_append hprefix tailTrace_457040
  have hstable : (prefixWord ++ tailWord_457040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457040).length < 2 ^ (prefixWord ++ tailWord_457040).sum := by decide
  have hdescent : baseEnd_457040 < baseStart_457040 := by decide
  rcases family_descends (prefixWord ++ tailWord_457040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457074 : List Nat := [3, 2, 1, 2, 1, 3, 2, 1, 1, 5, 2]
def baseStart_457074 : Nat := 118140960795 + 457074 * 2 ^ 59
def prefixEnd_457074 : Nat := 4983230072969 + 3 ^ 40 * 457074 * 2
def baseEnd_457074 : Nat := 234698656673249929572961

theorem tailTrace_457074 : CollatzResearch.WordTrace tailWord_457074 prefixEnd_457074 234698656673249929572961 := by
  unfold tailWord_457074
  simp only [CollatzResearch.WordTrace]
  refine ⟨4167714586526608717368569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11113905564070956579649517 4167714586526608717368569)
  ·
    refine ⟨3125785939894956538026427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4167714586526608717368569 3125785939894956538026427)
    ·
      refine ⟨4688678909842434807039641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3125785939894956538026427 4688678909842434807039641)
      ·
        refine ⟨3516509182381826105279731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4688678909842434807039641 3516509182381826105279731)
        ·
          refine ⟨5274763773572739157919597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3516509182381826105279731 5274763773572739157919597)
          ·
            refine ⟨1978036415089777184219849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5274763773572739157919597 1978036415089777184219849)
            ·
              refine ⟨1483527311317332888164887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1978036415089777184219849 1483527311317332888164887)
              ·
                refine ⟨2225290966975999332247331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1483527311317332888164887 2225290966975999332247331)
                ·
                  refine ⟨3337936450463998998370997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2225290966975999332247331 3337936450463998998370997)
                  ·
                    refine ⟨312931542230999906097281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3337936450463998998370997 312931542230999906097281)
                    ·
                      refine ⟨234698656673249929572961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 312931542230999906097281 234698656673249929572961)
                      ·
                        rfl

theorem cell23_457074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_457074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457074 prefixEnd_457074 := by exact prefixLift 457074
  have htrace : WordTrace (prefixWord ++ tailWord_457074) baseStart_457074 baseEnd_457074 := by
    simpa [prefixWord, tailWord_457074, baseEnd_457074] using wordTrace_append hprefix tailTrace_457074
  have hstable : (prefixWord ++ tailWord_457074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457074).length < 2 ^ (prefixWord ++ tailWord_457074).sum := by decide
  have hdescent : baseEnd_457074 < baseStart_457074 := by decide
  rcases family_descends (prefixWord ++ tailWord_457074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457087 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 1, 8, 2]
def baseStart_457087 : Nat := 118140960795 + 457087 * 2 ^ 59
def prefixEnd_457087 : Nat := 4983230072969 + 3 ^ 40 * 457087 * 2
def baseEnd_457087 : Nat := 234705331921758378710401

theorem tailTrace_457087 : CollatzResearch.WordTrace tailWord_457087 prefixEnd_457087 234705331921758378710401 := by
  unfold tailWord_457087
  simp only [CollatzResearch.WordTrace]
  refine ⟨16671332495059338089697515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11114221663372892059798343 16671332495059338089697515)
  ·
    refine ⟨25006998742589007134546273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16671332495059338089697515 25006998742589007134546273)
    ·
      refine ⟨18755249056941755350909705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25006998742589007134546273 18755249056941755350909705)
      ·
        refine ⟨14066436792706316513182279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18755249056941755350909705 14066436792706316513182279)
        ·
          refine ⟨21099655189059474769773419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14066436792706316513182279 21099655189059474769773419)
          ·
            refine ⟨31649482783589212154660129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21099655189059474769773419 31649482783589212154660129)
            ·
              refine ⟨23737112087691909115995097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31649482783589212154660129 23737112087691909115995097)
              ·
                refine ⟨17802834065768931836996323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23737112087691909115995097 17802834065768931836996323)
                ·
                  refine ⟨26704251098653397755494485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17802834065768931836996323 26704251098653397755494485)
                  ·
                    refine ⟨312940442562344504947201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26704251098653397755494485 312940442562344504947201)
                    ·
                      refine ⟨234705331921758378710401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 312940442562344504947201 234705331921758378710401)
                      ·
                        rfl

theorem cell23_457087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 8, 2].length) (baseStart_457087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457087 prefixEnd_457087 := by exact prefixLift 457087
  have htrace : WordTrace (prefixWord ++ tailWord_457087) baseStart_457087 baseEnd_457087 := by
    simpa [prefixWord, tailWord_457087, baseEnd_457087] using wordTrace_append hprefix tailTrace_457087
  have hstable : (prefixWord ++ tailWord_457087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457087).length < 2 ^ (prefixWord ++ tailWord_457087).sum := by decide
  have hdescent : baseEnd_457087 < baseStart_457087 := by decide
  rcases family_descends (prefixWord ++ tailWord_457087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457091 : List Nat := [1, 1, 1, 3, 6, 1, 1, 2, 2, 3, 2]
def baseStart_457091 : Nat := 118140960795 + 457091 * 2 ^ 59
def prefixEnd_457091 : Nat := 4983230072969 + 3 ^ 40 * 457091 * 2
def baseEnd_457091 : Nat := 234707385844376363060383

theorem tailTrace_457091 : CollatzResearch.WordTrace tailWord_457091 prefixEnd_457091 234707385844376363060383 := by
  unfold tailWord_457091
  simp only [CollatzResearch.WordTrace]
  refine ⟨16671478387044846772843127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11114318924696564515228751 16671478387044846772843127)
  ·
    refine ⟨25007217580567270159264691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16671478387044846772843127 25007217580567270159264691)
    ·
      refine ⟨37510826370850905238897037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25007217580567270159264691 37510826370850905238897037)
      ·
        refine ⟨14066559889069089464586389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37510826370850905238897037 14066559889069089464586389)
        ·
          refine ⟨659369994800113568652487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14066559889069089464586389 659369994800113568652487)
          ·
            refine ⟨989054992200170352978731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659369994800113568652487 989054992200170352978731)
            ·
              refine ⟨1483582488300255529468097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 989054992200170352978731 1483582488300255529468097)
              ·
                refine ⟨1112686866225191647101073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1483582488300255529468097 1112686866225191647101073)
                ·
                  refine ⟨834515149668893735325805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1112686866225191647101073 834515149668893735325805)
                  ·
                    refine ⟨312943181125835150747177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 834515149668893735325805 312943181125835150747177)
                    ·
                      refine ⟨234707385844376363060383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 312943181125835150747177 234707385844376363060383)
                      ·
                        rfl

theorem cell23_457091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 3, 2].length) (baseStart_457091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457091 prefixEnd_457091 := by exact prefixLift 457091
  have htrace : WordTrace (prefixWord ++ tailWord_457091) baseStart_457091 baseEnd_457091 := by
    simpa [prefixWord, tailWord_457091, baseEnd_457091] using wordTrace_append hprefix tailTrace_457091
  have hstable : (prefixWord ++ tailWord_457091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457091).length < 2 ^ (prefixWord ++ tailWord_457091).sum := by decide
  have hdescent : baseEnd_457091 < baseStart_457091 := by decide
  rcases family_descends (prefixWord ++ tailWord_457091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457104 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 9, 2, 2]
def baseStart_457104 : Nat := 118140960795 + 457104 * 2 ^ 59
def prefixEnd_457104 : Nat := 4983230072969 + 3 ^ 40 * 457104 * 2
def baseEnd_457104 : Nat := 234714061092884812197823

theorem tailTrace_457104 : CollatzResearch.WordTrace tailWord_457104 prefixEnd_457104 234714061092884812197823 := by
  unfold tailWord_457104
  simp only [CollatzResearch.WordTrace]
  refine ⟨8335976267998874996533183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11114635023998499995377577 8335976267998874996533183)
  ·
    refine ⟨12503964401998312494799775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8335976267998874996533183 12503964401998312494799775)
    ·
      refine ⟨18755946602997468742199663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12503964401998312494799775 18755946602997468742199663)
      ·
        refine ⟨28133919904496203113299495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18755946602997468742199663 28133919904496203113299495)
        ·
          refine ⟨42200879856744304669949243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28133919904496203113299495 42200879856744304669949243)
          ·
            refine ⟨63301319785116457004923865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42200879856744304669949243 63301319785116457004923865)
            ·
              refine ⟨47475989838837342753692899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63301319785116457004923865 47475989838837342753692899)
              ·
                refine ⟨71213984758256014130539349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47475989838837342753692899 71213984758256014130539349)
                ·
                  refine ⟨417269441942906332796129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71213984758256014130539349 417269441942906332796129)
                  ·
                    refine ⟨312952081457179749597097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 417269441942906332796129 312952081457179749597097)
                    ·
                      refine ⟨234714061092884812197823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 312952081457179749597097 234714061092884812197823)
                      ·
                        rfl

theorem cell23_457104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 9, 2, 2].length) (baseStart_457104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457104 prefixEnd_457104 := by exact prefixLift 457104
  have htrace : WordTrace (prefixWord ++ tailWord_457104) baseStart_457104 baseEnd_457104 := by
    simpa [prefixWord, tailWord_457104, baseEnd_457104] using wordTrace_append hprefix tailTrace_457104
  have hstable : (prefixWord ++ tailWord_457104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457104).length < 2 ^ (prefixWord ++ tailWord_457104).sum := by decide
  have hdescent : baseEnd_457104 < baseStart_457104 := by decide
  rcases family_descends (prefixWord ++ tailWord_457104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457118 : List Nat := [4, 3, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_457118 : Nat := 118140960795 + 457118 * 2 ^ 59
def prefixEnd_457118 : Nat := 4983230072969 + 3 ^ 40 * 457118 * 2
def baseEnd_457118 : Nat := 78240416607349252474253

theorem tailTrace_457118 : CollatzResearch.WordTrace tailWord_457118 prefixEnd_457118 78240416607349252474253 := by
  unfold tailWord_457118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2084057894743378798009501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11114975438631353589384005 2084057894743378798009501)
  ·
    refine ⟨781521710528767049253563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2084057894743378798009501 781521710528767049253563)
    ·
      refine ⟨1172282565793150573880345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 781521710528767049253563 1172282565793150573880345)
      ·
        refine ⟨879211924344862930410259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1172282565793150573880345 879211924344862930410259)
        ·
          refine ⟨1318817886517294395615389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879211924344862930410259 1318817886517294395615389)
          ·
            refine ⟨494556707443985398355771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1318817886517294395615389 494556707443985398355771)
            ·
              refine ⟨741835061165978097533657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494556707443985398355771 741835061165978097533657)
              ·
                refine ⟨556376295874483573150243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 741835061165978097533657 556376295874483573150243)
                ·
                  refine ⟨834564443811725359725365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 556376295874483573150243 834564443811725359725365)
                  ·
                    refine ⟨78240416607349252474253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 834564443811725359725365 78240416607349252474253)
                    ·
                      rfl

theorem cell23_457118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_457118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457118 prefixEnd_457118 := by exact prefixLift 457118
  have htrace : WordTrace (prefixWord ++ tailWord_457118) baseStart_457118 baseEnd_457118 := by
    simpa [prefixWord, tailWord_457118, baseEnd_457118] using wordTrace_append hprefix tailTrace_457118
  have hstable : (prefixWord ++ tailWord_457118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457118).length < 2 ^ (prefixWord ++ tailWord_457118).sum := by decide
  have hdescent : baseEnd_457118 < baseStart_457118 := by decide
  rcases family_descends (prefixWord ++ tailWord_457118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457121 : List Nat := [1, 2, 3, 5, 1, 1, 1, 1, 3, 1, 4]
def baseStart_457121 : Nat := 118140960795 + 457121 * 2 ^ 59
def prefixEnd_457121 : Nat := 4983230072969 + 3 ^ 40 * 457121 * 2
def baseEnd_457121 : Nat := 234722790264011245685245

theorem tailTrace_457121 : CollatzResearch.WordTrace tailWord_457121 prefixEnd_457121 234722790264011245685245 := by
  unfold tailWord_457121
  simp only [CollatzResearch.WordTrace]
  refine ⟨16672572576936161896435217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11115048384624107930956811 16672572576936161896435217)
  ·
    refine ⟨12504429432702121422326413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16672572576936161896435217 12504429432702121422326413)
    ·
      refine ⟨4689161037263295533372405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12504429432702121422326413 4689161037263295533372405)
      ·
        refine ⟨439608847243433956253663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4689161037263295533372405 439608847243433956253663)
        ·
          refine ⟨659413270865150934380495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439608847243433956253663 659413270865150934380495)
          ·
            refine ⟨989119906297726401570743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659413270865150934380495 989119906297726401570743)
            ·
              refine ⟨1483679859446589602356115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 989119906297726401570743 1483679859446589602356115)
              ·
                refine ⟨2225519789169884403534173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1483679859446589602356115 2225519789169884403534173)
                ·
                  refine ⟨834569920938706651325315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2225519789169884403534173 834569920938706651325315)
                  ·
                    refine ⟨1251854881408059976987973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 834569920938706651325315 1251854881408059976987973)
                    ·
                      refine ⟨234722790264011245685245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1251854881408059976987973 234722790264011245685245)
                      ·
                        rfl

theorem cell23_457121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_457121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457121 prefixEnd_457121 := by exact prefixLift 457121
  have htrace : WordTrace (prefixWord ++ tailWord_457121) baseStart_457121 baseEnd_457121 := by
    simpa [prefixWord, tailWord_457121, baseEnd_457121] using wordTrace_append hprefix tailTrace_457121
  have hstable : (prefixWord ++ tailWord_457121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457121).length < 2 ^ (prefixWord ++ tailWord_457121).sum := by decide
  have hdescent : baseEnd_457121 < baseStart_457121 := by decide
  rcases family_descends (prefixWord ++ tailWord_457121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457127 : List Nat := [1, 1, 6, 1, 1, 2, 2, 9]
def baseStart_457127 : Nat := 118140960795 + 457127 * 2 ^ 59
def prefixEnd_457127 : Nat := 4983230072969 + 3 ^ 40 * 457127 * 2
def baseEnd_457127 : Nat := 8693550783256971192971

theorem tailTrace_457127 : CollatzResearch.WordTrace tailWord_457127 prefixEnd_457127 8693550783256971192971 := by
  unfold tailWord_457127
  simp only [CollatzResearch.WordTrace]
  refine ⟨16672791414914424921153635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11115194276609616614102423 16672791414914424921153635)
  ·
    refine ⟨25009187122371637381730453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16672791414914424921153635 25009187122371637381730453)
    ·
      refine ⟨1172305646361170502268615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25009187122371637381730453 1172305646361170502268615)
      ·
        refine ⟨1758458469541755753402923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1172305646361170502268615 1758458469541755753402923)
        ·
          refine ⟨2637687704312633630104385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1758458469541755753402923 2637687704312633630104385)
          ·
            refine ⟨1978265778234475222578289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2637687704312633630104385 1978265778234475222578289)
            ·
              refine ⟨1483699333675856416933717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1978265778234475222578289 1483699333675856416933717)
              ·
                refine ⟨8693550783256971192971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1483699333675856416933717 8693550783256971192971)
                ·
                  rfl

theorem cell23_457127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 9].length) (baseStart_457127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457127 prefixEnd_457127 := by exact prefixLift 457127
  have htrace : WordTrace (prefixWord ++ tailWord_457127) baseStart_457127 baseEnd_457127 := by
    simpa [prefixWord, tailWord_457127, baseEnd_457127] using wordTrace_append hprefix tailTrace_457127
  have hstable : (prefixWord ++ tailWord_457127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457127).length < 2 ^ (prefixWord ++ tailWord_457127).sum := by decide
  have hdescent : baseEnd_457127 < baseStart_457127 := by decide
  rcases family_descends (prefixWord ++ tailWord_457127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457138 : List Nat := [3, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2]
def baseStart_457138 : Nat := 118140960795 + 457138 * 2 ^ 59
def prefixEnd_457138 : Nat := 4983230072969 + 3 ^ 40 * 457138 * 2
def baseEnd_457138 : Nat := 234731519435137679172667

theorem tailTrace_457138 : CollatzResearch.WordTrace tailWord_457138 prefixEnd_457138 234731519435137679172667 := by
  unfold tailWord_457138
  simp only [CollatzResearch.WordTrace]
  refine ⟨4168298154468643449951017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11115461745249715866536045 4168298154468643449951017)
  ·
    refine ⟨3126223615851482587463263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4168298154468643449951017 3126223615851482587463263)
    ·
      refine ⟨4689335423777223881194895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3126223615851482587463263 4689335423777223881194895)
      ·
        refine ⟨7034003135665835821792343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4689335423777223881194895 7034003135665835821792343)
        ·
          refine ⟨10551004703498753732688515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7034003135665835821792343 10551004703498753732688515)
          ·
            refine ⟨15826507055248130599032773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10551004703498753732688515 15826507055248130599032773)
            ·
              refine ⟨2967470072859024487318645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15826507055248130599032773 2967470072859024487318645)
              ·
                refine ⟨278200319330533545686123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2967470072859024487318645 278200319330533545686123)
                ·
                  refine ⟨417300478995800318529185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278200319330533545686123 417300478995800318529185)
                  ·
                    refine ⟨312975359246850238896889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 417300478995800318529185 312975359246850238896889)
                    ·
                      refine ⟨234731519435137679172667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 312975359246850238896889 234731519435137679172667)
                      ·
                        rfl

theorem cell23_457138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2].length) (baseStart_457138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457138 prefixEnd_457138 := by exact prefixLift 457138
  have htrace : WordTrace (prefixWord ++ tailWord_457138) baseStart_457138 baseEnd_457138 := by
    simpa [prefixWord, tailWord_457138, baseEnd_457138] using wordTrace_append hprefix tailTrace_457138
  have hstable : (prefixWord ++ tailWord_457138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457138).length < 2 ^ (prefixWord ++ tailWord_457138).sum := by decide
  have hdescent : baseEnd_457138 < baseStart_457138 := by decide
  rcases family_descends (prefixWord ++ tailWord_457138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457141 : List Nat := [1, 3, 3, 2, 3, 2, 1, 1, 1, 1, 5]
def baseStart_457141 : Nat := 118140960795 + 457141 * 2 ^ 59
def prefixEnd_457141 : Nat := 4983230072969 + 3 ^ 40 * 457141 * 2
def baseEnd_457141 : Nat := 234733059877101167435153

theorem tailTrace_457141 : CollatzResearch.WordTrace tailWord_457141 prefixEnd_457141 234733059877101167435153 := by
  unfold tailWord_457141
  simp only [CollatzResearch.WordTrace]
  refine ⟨16673302036863705312163277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11115534691242470208108851 16673302036863705312163277)
  ·
    refine ⟨6252488263823889492061229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16673302036863705312163277 6252488263823889492061229)
    ·
      refine ⟨2344683098933958559522961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6252488263823889492061229 2344683098933958559522961)
      ·
        refine ⟨1758512324200468919642221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2344683098933958559522961 1758512324200468919642221)
        ·
          refine ⟨659442121575175844865833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1758512324200468919642221 659442121575175844865833)
          ·
            refine ⟨494581591181381883649375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 659442121575175844865833 494581591181381883649375)
            ·
              refine ⟨741872386772072825474063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494581591181381883649375 741872386772072825474063)
              ·
                refine ⟨1112808580158109238211095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 741872386772072825474063 1112808580158109238211095)
                ·
                  refine ⟨1669212870237163857316643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1112808580158109238211095 1669212870237163857316643)
                  ·
                    refine ⟨2503819305355745785974965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1669212870237163857316643 2503819305355745785974965)
                    ·
                      refine ⟨234733059877101167435153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2503819305355745785974965 234733059877101167435153)
                      ·
                        rfl

theorem cell23_457141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_457141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457141 prefixEnd_457141 := by exact prefixLift 457141
  have htrace : WordTrace (prefixWord ++ tailWord_457141) baseStart_457141 baseEnd_457141 := by
    simpa [prefixWord, tailWord_457141, baseEnd_457141] using wordTrace_append hprefix tailTrace_457141
  have hstable : (prefixWord ++ tailWord_457141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457141).length < 2 ^ (prefixWord ++ tailWord_457141).sum := by decide
  have hdescent : baseEnd_457141 < baseStart_457141 := by decide
  rcases family_descends (prefixWord ++ tailWord_457141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457174 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_457174 : Nat := 118140960795 + 457174 * 2 ^ 59
def prefixEnd_457174 : Nat := 4983230072969 + 3 ^ 40 * 457174 * 2
def baseEnd_457174 : Nat := 78250001579566512774167

theorem tailTrace_457174 : CollatzResearch.WordTrace tailWord_457174 prefixEnd_457174 78250001579566512774167 := by
  unfold tailWord_457174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1042156602859009496757161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11116337097162767965409717 1042156602859009496757161)
  ·
    refine ⟨781617452144257122567871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1042156602859009496757161 781617452144257122567871)
    ·
      refine ⟨1172426178216385683851807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 781617452144257122567871 1172426178216385683851807)
      ·
        refine ⟨1758639267324578525777711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1172426178216385683851807 1758639267324578525777711)
        ·
          refine ⟨2637958900986867788666567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1758639267324578525777711 2637958900986867788666567)
          ·
            refine ⟨3956938351480301682999851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2637958900986867788666567 3956938351480301682999851)
            ·
              refine ⟨5935407527220452524499777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3956938351480301682999851 5935407527220452524499777)
              ·
                refine ⟨4451555645415339393374833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5935407527220452524499777 4451555645415339393374833)
                ·
                  refine ⟨3338666734061504545031125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4451555645415339393374833 3338666734061504545031125)
                  ·
                    refine ⟨78250001579566512774167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3338666734061504545031125 78250001579566512774167)
                    ·
                      rfl

theorem cell23_457174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_457174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457174 prefixEnd_457174 := by exact prefixLift 457174
  have htrace : WordTrace (prefixWord ++ tailWord_457174) baseStart_457174 baseEnd_457174 := by
    simpa [prefixWord, tailWord_457174, baseEnd_457174] using wordTrace_append hprefix tailTrace_457174
  have hstable : (prefixWord ++ tailWord_457174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457174).length < 2 ^ (prefixWord ++ tailWord_457174).sum := by decide
  have hdescent : baseEnd_457174 < baseStart_457174 := by decide
  rcases family_descends (prefixWord ++ tailWord_457174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457177 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 2, 3, 4]
def baseStart_457177 : Nat := 118140960795 + 457177 * 2 ^ 59
def prefixEnd_457177 : Nat := 4983230072969 + 3 ^ 40 * 457177 * 2
def baseEnd_457177 : Nat := 234751545180663026584987

theorem tailTrace_457177 : CollatzResearch.WordTrace tailWord_457177 prefixEnd_457177 234751545180663026584987 := by
  unfold tailWord_457177
  simp only [CollatzResearch.WordTrace]
  refine ⟨16674615064733283460473785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11116410043155522306982523 16674615064733283460473785)
  ·
    refine ⟨12505961298549962595355339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16674615064733283460473785 12505961298549962595355339)
    ·
      refine ⟨18758941947824943893033009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12505961298549962595355339 18758941947824943893033009)
      ·
        refine ⟨14069206460868707919774757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18758941947824943893033009 14069206460868707919774757)
        ·
          refine ⟨2637976211412882734957767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14069206460868707919774757 2637976211412882734957767)
          ·
            refine ⟨3956964317119324102436651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2637976211412882734957767 3956964317119324102436651)
            ·
              refine ⟨5935446475678986153654977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3956964317119324102436651 5935446475678986153654977)
              ·
                refine ⟨4451584856759239615241233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5935446475678986153654977 4451584856759239615241233)
                ·
                  refine ⟨3338688642569429711430925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4451584856759239615241233 3338688642569429711430925)
                  ·
                    refine ⟨1252008240963536141786597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3338688642569429711430925 1252008240963536141786597)
                    ·
                      refine ⟨234751545180663026584987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1252008240963536141786597 234751545180663026584987)
                      ·
                        rfl

theorem cell23_457177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_457177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457177 prefixEnd_457177 := by exact prefixLift 457177
  have htrace : WordTrace (prefixWord ++ tailWord_457177) baseStart_457177 baseEnd_457177 := by
    simpa [prefixWord, tailWord_457177, baseEnd_457177] using wordTrace_append hprefix tailTrace_457177
  have hstable : (prefixWord ++ tailWord_457177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457177).length < 2 ^ (prefixWord ++ tailWord_457177).sum := by decide
  have hdescent : baseEnd_457177 < baseStart_457177 := by decide
  rcases family_descends (prefixWord ++ tailWord_457177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457181 : List Nat := [1, 4, 3, 1, 1, 1, 1, 3, 3, 3, 2]
def baseStart_457181 : Nat := 118140960795 + 457181 * 2 ^ 59
def prefixEnd_457181 : Nat := 4983230072969 + 3 ^ 40 * 457181 * 2
def baseEnd_457181 : Nat := 234753599103281010934969

theorem tailTrace_457181 : CollatzResearch.WordTrace tailWord_457181 prefixEnd_457181 234753599103281010934969 := by
  unfold tailWord_457181
  simp only [CollatzResearch.WordTrace]
  refine ⟨16674760956718792143619397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11116507304479194762412931 16674760956718792143619397)
  ·
    refine ⟨3126517679384773526928637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16674760956718792143619397 3126517679384773526928637)
    ·
      refine ⟨1172444129769290072598239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3126517679384773526928637 1172444129769290072598239)
      ·
        refine ⟨1758666194653935108897359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1172444129769290072598239 1758666194653935108897359)
        ·
          refine ⟨2637999291980902663346039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1758666194653935108897359 2637999291980902663346039)
          ·
            refine ⟨3956998937971353995019059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2637999291980902663346039 3956998937971353995019059)
            ·
              refine ⟨5935498406957030992528589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3956998937971353995019059 5935498406957030992528589)
              ·
                refine ⟨2225811902608886622198221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5935498406957030992528589 2225811902608886622198221)
                ·
                  refine ⟨834679463478332483324333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2225811902608886622198221 834679463478332483324333)
                  ·
                    refine ⟨313004798804374681246625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 834679463478332483324333 313004798804374681246625)
                    ·
                      refine ⟨234753599103281010934969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 313004798804374681246625 234753599103281010934969)
                      ·
                        rfl

theorem cell23_457181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_457181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457181 prefixEnd_457181 := by exact prefixLift 457181
  have htrace : WordTrace (prefixWord ++ tailWord_457181) baseStart_457181 baseEnd_457181 := by
    simpa [prefixWord, tailWord_457181, baseEnd_457181] using wordTrace_append hprefix tailTrace_457181
  have hstable : (prefixWord ++ tailWord_457181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457181).length < 2 ^ (prefixWord ++ tailWord_457181).sum := by decide
  have hdescent : baseEnd_457181 < baseStart_457181 := by decide
  rcases family_descends (prefixWord ++ tailWord_457181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457198 : List Nat := [4, 1, 2, 1, 2, 3, 1, 3, 1, 3, 2]
def baseStart_457198 : Nat := 118140960795 + 457198 * 2 ^ 59
def prefixEnd_457198 : Nat := 4983230072969 + 3 ^ 40 * 457198 * 2
def baseEnd_457198 : Nat := 234762328274407444422391

theorem tailTrace_457198 : CollatzResearch.WordTrace tailWord_457198 prefixEnd_457198 234762328274407444422391 := by
  unfold tailWord_457198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2084422624707150505873531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11116920665104802697992165 2084422624707150505873531)
  ·
    refine ⟨3126633937060725758810297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2084422624707150505873531 3126633937060725758810297)
    ·
      refine ⟨2344975452795544319107723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3126633937060725758810297 2344975452795544319107723)
      ·
        refine ⟨3517463179193316478661585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2344975452795544319107723 3517463179193316478661585)
        ·
          refine ⟨2638097384394987358996189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3517463179193316478661585 2638097384394987358996189)
          ·
            refine ⟨989286519148120259623571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2638097384394987358996189 989286519148120259623571)
            ·
              refine ⟨1483929778722180389435357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 989286519148120259623571 1483929778722180389435357)
              ·
                refine ⟨556473667020817646038259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1483929778722180389435357 556473667020817646038259)
                ·
                  refine ⟨834710500531226469057389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 556473667020817646038259 834710500531226469057389)
                  ·
                    refine ⟨313016437699209925896521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 834710500531226469057389 313016437699209925896521)
                    ·
                      refine ⟨234762328274407444422391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 313016437699209925896521 234762328274407444422391)
                      ·
                        rfl

theorem cell23_457198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_457198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457198 prefixEnd_457198 := by exact prefixLift 457198
  have htrace : WordTrace (prefixWord ++ tailWord_457198) baseStart_457198 baseEnd_457198 := by
    simpa [prefixWord, tailWord_457198, baseEnd_457198] using wordTrace_append hprefix tailTrace_457198
  have hstable : (prefixWord ++ tailWord_457198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457198).length < 2 ^ (prefixWord ++ tailWord_457198).sum := by decide
  have hdescent : baseEnd_457198 < baseStart_457198 := by decide
  rcases family_descends (prefixWord ++ tailWord_457198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457222 : List Nat := [6, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_457222 : Nat := 118140960795 + 457222 * 2 ^ 59
def prefixEnd_457222 : Nat := 4983230072969 + 3 ^ 40 * 457222 * 2
def baseEnd_457222 : Nat := 234774651810115350522281

theorem tailTrace_457222 : CollatzResearch.WordTrace tailWord_457222 prefixEnd_457222 234774651810115350522281 := by
  unfold tailWord_457222
  simp only [CollatzResearch.WordTrace]
  refine ⟨521133010924070504558185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11117504233046837430574613 521133010924070504558185)
  ·
    refine ⟨390849758193052878418639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 521133010924070504558185 390849758193052878418639)
    ·
      refine ⟨586274637289579317627959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390849758193052878418639 586274637289579317627959)
      ·
        refine ⟨879411955934368976441939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586274637289579317627959 879411955934368976441939)
        ·
          refine ⟨1319117933901553464662909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879411955934368976441939 1319117933901553464662909)
          ·
            refine ⟨494669225213082549248591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1319117933901553464662909 494669225213082549248591)
            ·
              refine ⟨742003837819623823872887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494669225213082549248591 742003837819623823872887)
              ·
                refine ⟨1113005756729435735809331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 742003837819623823872887 1113005756729435735809331)
                ·
                  refine ⟨1669508635094153603713997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1113005756729435735809331 1669508635094153603713997)
                  ·
                    refine ⟨626065738160307601392749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1669508635094153603713997 626065738160307601392749)
                    ·
                      refine ⟨234774651810115350522281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 626065738160307601392749 234774651810115350522281)
                      ·
                        rfl

theorem cell23_457222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_457222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457222 prefixEnd_457222 := by exact prefixLift 457222
  have htrace : WordTrace (prefixWord ++ tailWord_457222) baseStart_457222 baseEnd_457222 := by
    simpa [prefixWord, tailWord_457222, baseEnd_457222] using wordTrace_append hprefix tailTrace_457222
  have hstable : (prefixWord ++ tailWord_457222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457222).length < 2 ^ (prefixWord ++ tailWord_457222).sum := by decide
  have hdescent : baseEnd_457222 < baseStart_457222 := by decide
  rcases family_descends (prefixWord ++ tailWord_457222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457228 : List Nat := [2, 2, 1, 2, 4, 3, 1, 1, 1, 4, 2]
def baseStart_457228 : Nat := 118140960795 + 457228 * 2 ^ 59
def prefixEnd_457228 : Nat := 4983230072969 + 3 ^ 40 * 457228 * 2
def baseEnd_457228 : Nat := 234777732694042327047253

theorem tailTrace_457228 : CollatzResearch.WordTrace tailWord_457228 prefixEnd_457228 234777732694042327047253 := by
  unfold tailWord_457228
  simp only [CollatzResearch.WordTrace]
  refine ⟨8338237593774259585290169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11117650125032346113720225 8338237593774259585290169)
  ·
    refine ⟨6253678195330694688967627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8338237593774259585290169 6253678195330694688967627)
    ·
      refine ⟨9380517292996042033451441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6253678195330694688967627 9380517292996042033451441)
      ·
        refine ⟨7035387969747031525088581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9380517292996042033451441 7035387969747031525088581)
        ·
          refine ⟨1319135244327568410954109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7035387969747031525088581 1319135244327568410954109)
          ·
            refine ⟨494675716622838154107791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1319135244327568410954109 494675716622838154107791)
            ·
              refine ⟨742013574934257231161687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494675716622838154107791 742013574934257231161687)
              ·
                refine ⟨1113020362401385846742531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 742013574934257231161687 1113020362401385846742531)
                ·
                  refine ⟨1669530543602078770113797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1113020362401385846742531 1669530543602078770113797)
                  ·
                    refine ⟨313036976925389769396337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1669530543602078770113797 313036976925389769396337)
                    ·
                      refine ⟨234777732694042327047253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 313036976925389769396337 234777732694042327047253)
                      ·
                        rfl

theorem cell23_457228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 1, 4, 2].length) (baseStart_457228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457228 prefixEnd_457228 := by exact prefixLift 457228
  have htrace : WordTrace (prefixWord ++ tailWord_457228) baseStart_457228 baseEnd_457228 := by
    simpa [prefixWord, tailWord_457228, baseEnd_457228] using wordTrace_append hprefix tailTrace_457228
  have hstable : (prefixWord ++ tailWord_457228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457228).length < 2 ^ (prefixWord ++ tailWord_457228).sum := by decide
  have hdescent : baseEnd_457228 < baseStart_457228 := by decide
  rcases family_descends (prefixWord ++ tailWord_457228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457251 : List Nat := [1, 1, 1, 4, 4, 1, 3, 3, 5]
def baseStart_457251 : Nat := 118140960795 + 457251 * 2 ^ 59
def prefixEnd_457251 : Nat := 4983230072969 + 3 ^ 40 * 457251 * 2
def baseEnd_457251 : Nat := 26087726972121748562183

theorem tailTrace_457251 : CollatzResearch.WordTrace tailWord_457251 prefixEnd_457251 26087726972121748562183 := by
  unfold tailWord_457251
  simp only [CollatzResearch.WordTrace]
  refine ⟨16677314066465194098667607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11118209377643462732445071 16677314066465194098667607)
  ·
    refine ⟨25015971099697791148001411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16677314066465194098667607 25015971099697791148001411)
    ·
      refine ⟨37523956649546686722002117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25015971099697791148001411 37523956649546686722002117)
      ·
        refine ⟨7035741871790003760375397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37523956649546686722002117 7035741871790003760375397)
        ·
          refine ⟨1319201600960625705070387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7035741871790003760375397 1319201600960625705070387)
          ·
            refine ⟨1978802401440938557605581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1319201600960625705070387 1978802401440938557605581)
            ·
              refine ⟨742050900540351959102093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1978802401440938557605581 742050900540351959102093)
              ·
                refine ⟨278269087702631984663285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 742050900540351959102093 278269087702631984663285)
                ·
                  refine ⟨26087726972121748562183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 278269087702631984663285 26087726972121748562183)
                  ·
                    rfl

theorem cell23_457251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3, 5].length) (baseStart_457251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457251 prefixEnd_457251 := by exact prefixLift 457251
  have htrace : WordTrace (prefixWord ++ tailWord_457251) baseStart_457251 baseEnd_457251 := by
    simpa [prefixWord, tailWord_457251, baseEnd_457251] using wordTrace_append hprefix tailTrace_457251
  have hstable : (prefixWord ++ tailWord_457251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457251).length < 2 ^ (prefixWord ++ tailWord_457251).sum := by decide
  have hdescent : baseEnd_457251 < baseStart_457251 := by decide
  rcases family_descends (prefixWord ++ tailWord_457251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457274 : List Nat := [3, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5]
def baseStart_457274 : Nat := 118140960795 + 457274 * 2 ^ 59
def prefixEnd_457274 : Nat := 4983230072969 + 3 ^ 40 * 457274 * 2
def baseEnd_457274 : Nat := 234801352804149147072041

theorem tailTrace_457274 : CollatzResearch.WordTrace tailWord_457274 prefixEnd_457274 234801352804149147072041 := by
  unfold tailWord_457274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4169538236345467256688719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11118768630254579351169917 4169538236345467256688719)
  ·
    refine ⟨6254307354518200885033079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4169538236345467256688719 6254307354518200885033079)
    ·
      refine ⟨9381461031777301327549619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6254307354518200885033079 9381461031777301327549619)
      ·
        refine ⟨14072191547665951991324429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9381461031777301327549619 14072191547665951991324429)
        ·
          refine ⟨5277071830374731996746661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14072191547665951991324429 5277071830374731996746661)
          ·
            refine ⟨989450968195262249389999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5277071830374731996746661 989450968195262249389999)
            ·
              refine ⟨1484176452292893374084999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 989450968195262249389999 1484176452292893374084999)
              ·
                refine ⟨2226264678439340061127499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1484176452292893374084999 2226264678439340061127499)
                ·
                  refine ⟨3339397017659010091691249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2226264678439340061127499 3339397017659010091691249)
                  ·
                    refine ⟨2504547763244257568768437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3339397017659010091691249 2504547763244257568768437)
                    ·
                      refine ⟨234801352804149147072041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2504547763244257568768437 234801352804149147072041)
                      ·
                        rfl

theorem cell23_457274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_457274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457274 prefixEnd_457274 := by exact prefixLift 457274
  have htrace : WordTrace (prefixWord ++ tailWord_457274) baseStart_457274 baseEnd_457274 := by
    simpa [prefixWord, tailWord_457274, baseEnd_457274] using wordTrace_append hprefix tailTrace_457274
  have hstable : (prefixWord ++ tailWord_457274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457274).length < 2 ^ (prefixWord ++ tailWord_457274).sum := by decide
  have hdescent : baseEnd_457274 < baseStart_457274 := by decide
  rcases family_descends (prefixWord ++ tailWord_457274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457304 : List Nat := [2, 1, 2, 2, 1, 2, 2, 3, 1, 4, 3]
def baseStart_457304 : Nat := 118140960795 + 457304 * 2 ^ 59
def prefixEnd_457304 : Nat := 4983230072969 + 3 ^ 40 * 457304 * 2
def baseEnd_457304 : Nat := 234816757223784029696903

theorem tailTrace_457304 : CollatzResearch.WordTrace tailWord_457304 prefixEnd_457304 234816757223784029696903 := by
  unfold tailWord_457304
  simp only [CollatzResearch.WordTrace]
  refine ⟨8339623567636592075173483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11119498090182122766897977 8339623567636592075173483)
  ·
    refine ⟨12509435351454888112760225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8339623567636592075173483 12509435351454888112760225)
    ·
      refine ⟨9382076513591166084570169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12509435351454888112760225 9382076513591166084570169)
      ·
        refine ⟨7036557385193374563427627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9382076513591166084570169 7036557385193374563427627)
        ·
          refine ⟨10554836077790061845141441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7036557385193374563427627 10554836077790061845141441)
          ·
            refine ⟨7916127058342546383856081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10554836077790061845141441 7916127058342546383856081)
            ·
              refine ⟨5937095293756909787892061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7916127058342546383856081 5937095293756909787892061)
              ·
                refine ⟨2226410735158841170459523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5937095293756909787892061 2226410735158841170459523)
                ·
                  refine ⟨3339616102738261755689285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2226410735158841170459523 3339616102738261755689285)
                  ·
                    refine ⟨626178019263424079191741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3339616102738261755689285 626178019263424079191741)
                    ·
                      refine ⟨234816757223784029696903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 626178019263424079191741 234816757223784029696903)
                      ·
                        rfl

theorem cell23_457304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_457304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457304 prefixEnd_457304 := by exact prefixLift 457304
  have htrace : WordTrace (prefixWord ++ tailWord_457304) baseStart_457304 baseEnd_457304 := by
    simpa [prefixWord, tailWord_457304, baseEnd_457304] using wordTrace_append hprefix tailTrace_457304
  have hstable : (prefixWord ++ tailWord_457304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457304).length < 2 ^ (prefixWord ++ tailWord_457304).sum := by decide
  have hdescent : baseEnd_457304 < baseStart_457304 := by decide
  rcases family_descends (prefixWord ++ tailWord_457304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457324 : List Nat := [2, 2, 1, 1, 3, 1, 3, 4, 6]
def baseStart_457324 : Nat := 118140960795 + 457324 * 2 ^ 59
def prefixEnd_457324 : Nat := 4983230072969 + 3 ^ 40 * 457324 * 2
def baseEnd_457324 : Nat := 26091891870763772382979

theorem tailTrace_457324 : CollatzResearch.WordTrace tailWord_457324 prefixEnd_457324 26091891870763772382979 := by
  unfold tailWord_457324
  simp only [CollatzResearch.WordTrace]
  refine ⟨8339988297600363783037513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11119984396800485044050017 8339988297600363783037513)
  ·
    refine ⟨6254991223200272837278135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8339988297600363783037513 6254991223200272837278135)
    ·
      refine ⟨9382486834800409255917203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6254991223200272837278135 9382486834800409255917203)
      ·
        refine ⟨14073730252200613883875805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9382486834800409255917203 14073730252200613883875805)
        ·
          refine ⟨5277648844575230206453427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14073730252200613883875805 5277648844575230206453427)
          ·
            refine ⟨7916473266862845309680141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5277648844575230206453427 7916473266862845309680141)
            ·
              refine ⟨2968677475073566991130053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7916473266862845309680141 2968677475073566991130053)
              ·
                refine ⟨556627026576293810836885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2968677475073566991130053 556627026576293810836885)
                ·
                  refine ⟨26091891870763772382979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 556627026576293810836885 26091891870763772382979)
                  ·
                    rfl

theorem cell23_457324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 6].length) (baseStart_457324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457324 prefixEnd_457324 := by exact prefixLift 457324
  have htrace : WordTrace (prefixWord ++ tailWord_457324) baseStart_457324 baseEnd_457324 := by
    simpa [prefixWord, tailWord_457324, baseEnd_457324] using wordTrace_append hprefix tailTrace_457324
  have hstable : (prefixWord ++ tailWord_457324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457324).length < 2 ^ (prefixWord ++ tailWord_457324).sum := by decide
  have hdescent : baseEnd_457324 < baseStart_457324 := by decide
  rcases family_descends (prefixWord ++ tailWord_457324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457408 : List Nat := [2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 4]
def baseStart_457408 : Nat := 118140960795 + 457408 * 2 ^ 59
def prefixEnd_457408 : Nat := 4983230072969 + 3 ^ 40 * 457408 * 2
def baseEnd_457408 : Nat := 234870159211851622796425

theorem tailTrace_457408 : CollatzResearch.WordTrace tailWord_457408 prefixEnd_457408 234870159211851622796425 := by
  unfold tailWord_457408
  simp only [CollatzResearch.WordTrace]
  refine ⟨8341520163448204956066439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11122026884597606608088585 8341520163448204956066439)
  ·
    refine ⟨12512280245172307434099659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8341520163448204956066439 12512280245172307434099659)
    ·
      refine ⟨18768420367758461151149489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12512280245172307434099659 18768420367758461151149489)
      ·
        refine ⟨14076315275818845863362117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18768420367758461151149489 14076315275818845863362117)
        ·
          refine ⟨2639309114216033599380397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14076315275818845863362117 2639309114216033599380397)
          ·
            refine ⟨989740917831012599767649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2639309114216033599380397 989740917831012599767649)
            ·
              refine ⟨742305688373259449825737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 989740917831012599767649 742305688373259449825737)
              ·
                refine ⟨556729266279944587369303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 742305688373259449825737 556729266279944587369303)
                ·
                  refine ⟨835093899419916881053955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 556729266279944587369303 835093899419916881053955)
                  ·
                    refine ⟨1252640849129875321580933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 835093899419916881053955 1252640849129875321580933)
                    ·
                      refine ⟨234870159211851622796425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1252640849129875321580933 234870159211851622796425)
                      ·
                        rfl

theorem cell23_457408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 4].length) (baseStart_457408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457408 prefixEnd_457408 := by exact prefixLift 457408
  have htrace : WordTrace (prefixWord ++ tailWord_457408) baseStart_457408 baseEnd_457408 := by
    simpa [prefixWord, tailWord_457408, baseEnd_457408] using wordTrace_append hprefix tailTrace_457408
  have hstable : (prefixWord ++ tailWord_457408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457408).length < 2 ^ (prefixWord ++ tailWord_457408).sum := by decide
  have hdescent : baseEnd_457408 < baseStart_457408 := by decide
  rcases family_descends (prefixWord ++ tailWord_457408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457451 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 2, 7, 2]
def baseStart_457451 : Nat := 118140960795 + 457451 * 2 ^ 59
def prefixEnd_457451 : Nat := 4983230072969 + 3 ^ 40 * 457451 * 2
def baseEnd_457451 : Nat := 234892238879994954558727

theorem tailTrace_457451 : CollatzResearch.WordTrace tailWord_457451 prefixEnd_457451 234892238879994954558727 := by
  unfold tailWord_457451
  simp only [CollatzResearch.WordTrace]
  refine ⟨16684608665740628255948207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11123072443827085503965471 16684608665740628255948207)
  ·
    refine ⟨25026912998610942383922311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16684608665740628255948207 25026912998610942383922311)
    ·
      refine ⟨37540369497916413575883467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25026912998610942383922311 37540369497916413575883467)
      ·
        refine ⟨56310554246874620363825201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37540369497916413575883467 56310554246874620363825201)
        ·
          refine ⟨42232915685155965272868901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56310554246874620363825201 42232915685155965272868901)
          ·
            refine ⟨7918671690966743488662919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42232915685155965272868901 7918671690966743488662919)
            ·
              refine ⟨11878007536450115232994379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7918671690966743488662919 11878007536450115232994379)
              ·
                refine ⟨17817011304675172849491569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11878007536450115232994379 17817011304675172849491569)
                ·
                  refine ⟨13362758478506379637118677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17817011304675172849491569 13362758478506379637118677)
                  ·
                    refine ⟨313189651839993272744969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13362758478506379637118677 313189651839993272744969)
                    ·
                      refine ⟨234892238879994954558727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 313189651839993272744969 234892238879994954558727)
                      ·
                        rfl

theorem cell23_457451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 7, 2].length) (baseStart_457451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457451 prefixEnd_457451 := by exact prefixLift 457451
  have htrace : WordTrace (prefixWord ++ tailWord_457451) baseStart_457451 baseEnd_457451 := by
    simpa [prefixWord, tailWord_457451, baseEnd_457451] using wordTrace_append hprefix tailTrace_457451
  have hstable : (prefixWord ++ tailWord_457451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457451).length < 2 ^ (prefixWord ++ tailWord_457451).sum := by decide
  have hdescent : baseEnd_457451 < baseStart_457451 := by decide
  rcases family_descends (prefixWord ++ tailWord_457451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457498 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2]
def baseStart_457498 : Nat := 118140960795 + 457498 * 2 ^ 59
def prefixEnd_457498 : Nat := 4983230072969 + 3 ^ 40 * 457498 * 2
def baseEnd_457498 : Nat := 234916372470756270671011

theorem tailTrace_457498 : CollatzResearch.WordTrace tailWord_457498 prefixEnd_457498 234916372470756270671011 := by
  unfold tailWord_457498
  simp only [CollatzResearch.WordTrace]
  refine ⟨4171580724142588820727287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11124215264380236855272765 4171580724142588820727287)
  ·
    refine ⟨6257371086213883231090931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4171580724142588820727287 6257371086213883231090931)
    ·
      refine ⟨9386056629320824846636397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6257371086213883231090931 9386056629320824846636397)
      ·
        refine ⟨3519771235995309317488649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9386056629320824846636397 3519771235995309317488649)
        ·
          refine ⟨2639828426996481988116487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3519771235995309317488649 2639828426996481988116487)
          ·
            refine ⟨3959742640494722982174731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2639828426996481988116487 3959742640494722982174731)
            ·
              refine ⟨5939613960742084473262097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3959742640494722982174731 5939613960742084473262097)
              ·
                refine ⟨4454710470556563354946573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5939613960742084473262097 4454710470556563354946573)
                ·
                  refine ⟨1670516426458711258104965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4454710470556563354946573 1670516426458711258104965)
                  ·
                    refine ⟨313221829961008360894681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1670516426458711258104965 313221829961008360894681)
                    ·
                      refine ⟨234916372470756270671011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 313221829961008360894681 234916372470756270671011)
                      ·
                        rfl

theorem cell23_457498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_457498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457498 prefixEnd_457498 := by exact prefixLift 457498
  have htrace : WordTrace (prefixWord ++ tailWord_457498) baseStart_457498 baseEnd_457498 := by
    simpa [prefixWord, tailWord_457498, baseEnd_457498] using wordTrace_append hprefix tailTrace_457498
  have hstable : (prefixWord ++ tailWord_457498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457498).length < 2 ^ (prefixWord ++ tailWord_457498).sum := by decide
  have hdescent : baseEnd_457498 < baseStart_457498 := by decide
  rcases family_descends (prefixWord ++ tailWord_457498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457508 : List Nat := [2, 3, 1, 3, 3, 1, 1, 1, 2, 6]
def baseStart_457508 : Nat := 118140960795 + 457508 * 2 ^ 59
def prefixEnd_457508 : Nat := 4983230072969 + 3 ^ 40 * 457508 * 2
def baseEnd_457508 : Nat := 78307169092433743848655

theorem tailTrace_457508 : CollatzResearch.WordTrace tailWord_457508 prefixEnd_457508 78307169092433743848655 := by
  unfold tailWord_457508
  simp only [CollatzResearch.WordTrace]
  refine ⟨8343343813267063495386589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11124458417689417993848785 8343343813267063495386589)
  ·
    refine ⟨3128753929975148810769971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8343343813267063495386589 3128753929975148810769971)
    ·
      refine ⟨4693130894962723216154957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3128753929975148810769971 4693130894962723216154957)
      ·
        refine ⟨1759924085611021206058109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4693130894962723216154957 1759924085611021206058109)
        ·
          refine ⟨659971532104132952271791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1759924085611021206058109 659971532104132952271791)
          ·
            refine ⟨989957298156199428407687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659971532104132952271791 989957298156199428407687)
            ·
              refine ⟨1484935947234299142611531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 989957298156199428407687 1484935947234299142611531)
              ·
                refine ⟨2227403920851448713917297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1484935947234299142611531 2227403920851448713917297)
                ·
                  refine ⟨1670552940638586535437973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2227403920851448713917297 1670552940638586535437973)
                  ·
                    refine ⟨78307169092433743848655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1670552940638586535437973 78307169092433743848655)
                    ·
                      rfl

theorem cell23_457508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_457508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457508 prefixEnd_457508 := by exact prefixLift 457508
  have htrace : WordTrace (prefixWord ++ tailWord_457508) baseStart_457508 baseEnd_457508 := by
    simpa [prefixWord, tailWord_457508, baseEnd_457508] using wordTrace_append hprefix tailTrace_457508
  have hstable : (prefixWord ++ tailWord_457508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457508).length < 2 ^ (prefixWord ++ tailWord_457508).sum := by decide
  have hdescent : baseEnd_457508 < baseStart_457508 := by decide
  rcases family_descends (prefixWord ++ tailWord_457508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457521 : List Nat := [1, 2, 2, 3, 2, 1, 3, 2, 7]
def baseStart_457521 : Nat := 118140960795 + 457521 * 2 ^ 59
def prefixEnd_457521 : Nat := 4983230072969 + 3 ^ 40 * 457521 * 2
def baseEnd_457521 : Nat := 26103131391756631187045

theorem tailTrace_457521 : CollatzResearch.WordTrace tailWord_457521 prefixEnd_457521 26103131391756631187045 := by
  unfold tailWord_457521
  simp only [CollatzResearch.WordTrace]
  refine ⟨16687161775487030210996417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11124774516991353473997611 16687161775487030210996417)
  ·
    refine ⟨12515371331615272658247313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16687161775487030210996417 12515371331615272658247313)
    ·
      refine ⟨9386528498711454493685485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12515371331615272658247313 9386528498711454493685485)
      ·
        refine ⟨3519948187016795435132057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9386528498711454493685485 3519948187016795435132057)
        ·
          refine ⟨2639961140262596576349043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3519948187016795435132057 2639961140262596576349043)
          ·
            refine ⟨3959941710393894864523565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2639961140262596576349043 3959941710393894864523565)
            ·
              refine ⟨1484978141397710574196337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3959941710393894864523565 1484978141397710574196337)
              ·
                refine ⟨1113733606048282930647253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1484978141397710574196337 1113733606048282930647253)
                ·
                  refine ⟨26103131391756631187045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1113733606048282930647253 26103131391756631187045)
                  ·
                    rfl

theorem cell23_457521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 7].length) (baseStart_457521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457521 prefixEnd_457521 := by exact prefixLift 457521
  have htrace : WordTrace (prefixWord ++ tailWord_457521) baseStart_457521 baseEnd_457521 := by
    simpa [prefixWord, tailWord_457521, baseEnd_457521] using wordTrace_append hprefix tailTrace_457521
  have hstable : (prefixWord ++ tailWord_457521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457521).length < 2 ^ (prefixWord ++ tailWord_457521).sum := by decide
  have hdescent : baseEnd_457521 < baseStart_457521 := by decide
  rcases family_descends (prefixWord ++ tailWord_457521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457548 : List Nat := [2, 2, 1, 3, 3, 1, 1, 2, 2, 3, 3]
def baseStart_457548 : Nat := 118140960795 + 457548 * 2 ^ 59
def prefixEnd_457548 : Nat := 4983230072969 + 3 ^ 40 * 457548 * 2
def baseEnd_457548 : Nat := 234942046503481075045781

theorem tailTrace_457548 : CollatzResearch.WordTrace tailWord_457548 prefixEnd_457548 234942046503481075045781 := by
  unfold tailWord_457548
  simp only [CollatzResearch.WordTrace]
  refine ⟨8344073273194606911114649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11125431030926142548152865 8344073273194606911114649)
  ·
    refine ⟨6258054954895955183335987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8344073273194606911114649 6258054954895955183335987)
    ·
      refine ⟨9387082432343932775003981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6258054954895955183335987 9387082432343932775003981)
      ·
        refine ⟨3520155912128974790626493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9387082432343932775003981 3520155912128974790626493)
        ·
          refine ⟨1320058467048365546484935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3520155912128974790626493 1320058467048365546484935)
          ·
            refine ⟨1980087700572548319727403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1320058467048365546484935 1980087700572548319727403)
            ·
              refine ⟨2970131550858822479591105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1980087700572548319727403 2970131550858822479591105)
              ·
                refine ⟨2227598663144116859693329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2970131550858822479591105 2227598663144116859693329)
                ·
                  refine ⟨1670698997358087644769997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2227598663144116859693329 1670698997358087644769997)
                  ·
                    refine ⟨626512124009282866788749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1670698997358087644769997 626512124009282866788749)
                    ·
                      refine ⟨234942046503481075045781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 626512124009282866788749 234942046503481075045781)
                      ·
                        rfl

theorem cell23_457548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_457548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457548 prefixEnd_457548 := by exact prefixLift 457548
  have htrace : WordTrace (prefixWord ++ tailWord_457548) baseStart_457548 baseEnd_457548 := by
    simpa [prefixWord, tailWord_457548, baseEnd_457548] using wordTrace_append hprefix tailTrace_457548
  have hstable : (prefixWord ++ tailWord_457548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457548).length < 2 ^ (prefixWord ++ tailWord_457548).sum := by decide
  have hdescent : baseEnd_457548 < baseStart_457548 := by decide
  rcases family_descends (prefixWord ++ tailWord_457548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457549 : List Nat := [1, 6, 1, 2, 2, 1, 1, 1, 4, 2, 2]
def baseStart_457549 : Nat := 118140960795 + 457549 * 2 ^ 59
def prefixEnd_457549 : Nat := 4983230072969 + 3 ^ 40 * 457549 * 2
def baseEnd_457549 : Nat := 234942559984135571133277

theorem tailTrace_457549 : CollatzResearch.WordTrace tailWord_457549 prefixEnd_457549 234942559984135571133277 := by
  unfold tailWord_457549
  simp only [CollatzResearch.WordTrace]
  refine ⟨16688183019385590993015701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11125455346257060662010467 16688183019385590993015701)
  ·
    refine ⟨782258579033699577797611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16688183019385590993015701 782258579033699577797611)
    ·
      refine ⟨1173387868550549366696417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 782258579033699577797611 1173387868550549366696417)
      ·
        refine ⟨880040901412912025022313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1173387868550549366696417 880040901412912025022313)
        ·
          refine ⟨660030676059684018766735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 880040901412912025022313 660030676059684018766735)
          ·
            refine ⟨990046014089526028150103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660030676059684018766735 990046014089526028150103)
            ·
              refine ⟨1485069021134289042225155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990046014089526028150103 1485069021134289042225155)
              ·
                refine ⟨2227603531701433563337733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1485069021134289042225155 2227603531701433563337733)
                ·
                  refine ⟨417675662194018793125825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2227603531701433563337733 417675662194018793125825)
                  ·
                    refine ⟨313256746645514094844369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 417675662194018793125825 313256746645514094844369)
                    ·
                      refine ⟨234942559984135571133277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 313256746645514094844369 234942559984135571133277)
                      ·
                        rfl

theorem cell23_457549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_457549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457549 prefixEnd_457549 := by exact prefixLift 457549
  have htrace : WordTrace (prefixWord ++ tailWord_457549) baseStart_457549 baseEnd_457549 := by
    simpa [prefixWord, tailWord_457549, baseEnd_457549] using wordTrace_append hprefix tailTrace_457549
  have hstable : (prefixWord ++ tailWord_457549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457549).length < 2 ^ (prefixWord ++ tailWord_457549).sum := by decide
  have hdescent : baseEnd_457549 < baseStart_457549 := by decide
  rcases family_descends (prefixWord ++ tailWord_457549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457581 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 1, 10]
def baseStart_457581 : Nat := 118140960795 + 457581 * 2 ^ 59
def prefixEnd_457581 : Nat := 4983230072969 + 3 ^ 40 * 457581 * 2
def baseEnd_457581 : Nat := 78319663788359815311043

theorem tailTrace_457581 : CollatzResearch.WordTrace tailWord_457581 prefixEnd_457581 78319663788359815311043 := by
  unfold tailWord_457581
  simp only [CollatzResearch.WordTrace]
  refine ⟨16689350155269660458180597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11126233436846440305453731 16689350155269660458180597)
  ·
    refine ⟨1564626577056530667954431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16689350155269660458180597 1564626577056530667954431)
    ·
      refine ⟨2346939865584796001931647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1564626577056530667954431 2346939865584796001931647)
      ·
        refine ⟨3520409798377194002897471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2346939865584796001931647 3520409798377194002897471)
        ·
          refine ⟨5280614697565791004346207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3520409798377194002897471 5280614697565791004346207)
          ·
            refine ⟨7920922046348686506519311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5280614697565791004346207 7920922046348686506519311)
            ·
              refine ⟨11881383069523029759778967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7920922046348686506519311 11881383069523029759778967)
              ·
                refine ⟨17822074604284544639668451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11881383069523029759778967 17822074604284544639668451)
                ·
                  refine ⟨26733111906426816959502677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17822074604284544639668451 26733111906426816959502677)
                  ·
                    refine ⟨78319663788359815311043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 26733111906426816959502677 78319663788359815311043)
                    ·
                      rfl

theorem cell23_457581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_457581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457581 prefixEnd_457581 := by exact prefixLift 457581
  have htrace : WordTrace (prefixWord ++ tailWord_457581) baseStart_457581 baseEnd_457581 := by
    simpa [prefixWord, tailWord_457581, baseEnd_457581] using wordTrace_append hprefix tailTrace_457581
  have hstable : (prefixWord ++ tailWord_457581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457581).length < 2 ^ (prefixWord ++ tailWord_457581).sum := by decide
  have hdescent : baseEnd_457581 < baseStart_457581 := by decide
  rcases family_descends (prefixWord ++ tailWord_457581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457611 : List Nat := [1, 1, 1, 1, 4, 2, 4, 1, 8]
def baseStart_457611 : Nat := 118140960795 + 457611 * 2 ^ 59
def prefixEnd_457611 : Nat := 4983230072969 + 3 ^ 40 * 457611 * 2
def baseEnd_457611 : Nat := 26108266198301592061999

theorem tailTrace_457611 : CollatzResearch.WordTrace tailWord_457611 prefixEnd_457611 26108266198301592061999 := by
  unfold tailWord_457611
  simp only [CollatzResearch.WordTrace]
  refine ⟨16690444345160975581772687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11126962896773983721181791 16690444345160975581772687)
  ·
    refine ⟨25035666517741463372659031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16690444345160975581772687 25035666517741463372659031)
    ·
      refine ⟨37553499776612195058988547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25035666517741463372659031 37553499776612195058988547)
      ·
        refine ⟨56330249664918292588482821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37553499776612195058988547 56330249664918292588482821)
        ·
          refine ⟨10561921812172179860340529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56330249664918292588482821 10561921812172179860340529)
          ·
            refine ⟨7921441359129134895255397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10561921812172179860340529 7921441359129134895255397)
            ·
              refine ⟨1485270254836712792860387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7921441359129134895255397 1485270254836712792860387)
              ·
                refine ⟨2227905382255069189290581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1485270254836712792860387 2227905382255069189290581)
                ·
                  refine ⟨26108266198301592061999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2227905382255069189290581 26108266198301592061999)
                  ·
                    rfl

theorem cell23_457611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 8].length) (baseStart_457611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457611 prefixEnd_457611 := by exact prefixLift 457611
  have htrace : WordTrace (prefixWord ++ tailWord_457611) baseStart_457611 baseEnd_457611 := by
    simpa [prefixWord, tailWord_457611, baseEnd_457611] using wordTrace_append hprefix tailTrace_457611
  have hstable : (prefixWord ++ tailWord_457611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457611).length < 2 ^ (prefixWord ++ tailWord_457611).sum := by decide
  have hdescent : baseEnd_457611 < baseStart_457611 := by decide
  rcases family_descends (prefixWord ++ tailWord_457611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457651 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 5]
def baseStart_457651 : Nat := 118140960795 + 457651 * 2 ^ 59
def prefixEnd_457651 : Nat := 4983230072969 + 3 ^ 40 * 457651 * 2
def baseEnd_457651 : Nat := 234994935010894172057807

theorem tailTrace_457651 : CollatzResearch.WordTrace tailWord_457651 prefixEnd_457651 234994935010894172057807 := by
  unfold tailWord_457651
  simp only [CollatzResearch.WordTrace]
  refine ⟨16691903265016062413228807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11127935510010708275485871 16691903265016062413228807)
  ·
    refine ⟨25037854897524093619843211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16691903265016062413228807 25037854897524093619843211)
    ·
      refine ⟨37556782346286140429764817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25037854897524093619843211 37556782346286140429764817)
      ·
        refine ⟨28167586759714605322323613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37556782346286140429764817 28167586759714605322323613)
        ·
          refine ⟨10562845034892976995871355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28167586759714605322323613 10562845034892976995871355)
          ·
            refine ⟨15844267552339465493807033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10562845034892976995871355 15844267552339465493807033)
            ·
              refine ⟨11883200664254599120355275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15844267552339465493807033 11883200664254599120355275)
              ·
                refine ⟨17824800996381898680532913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11883200664254599120355275 17824800996381898680532913)
                ·
                  refine ⟨13368600747286424010399685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17824800996381898680532913 13368600747286424010399685)
                  ·
                    refine ⟨2506612640116204501949941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13368600747286424010399685 2506612640116204501949941)
                    ·
                      refine ⟨234994935010894172057807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2506612640116204501949941 234994935010894172057807)
                      ·
                        rfl

theorem cell23_457651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 5].length) (baseStart_457651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457651 prefixEnd_457651 := by exact prefixLift 457651
  have htrace : WordTrace (prefixWord ++ tailWord_457651) baseStart_457651 baseEnd_457651 := by
    simpa [prefixWord, tailWord_457651, baseEnd_457651] using wordTrace_append hprefix tailTrace_457651
  have hstable : (prefixWord ++ tailWord_457651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457651).length < 2 ^ (prefixWord ++ tailWord_457651).sum := by decide
  have hdescent : baseEnd_457651 < baseStart_457651 := by decide
  rcases family_descends (prefixWord ++ tailWord_457651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457688 : List Nat := [2, 1, 2, 2, 2, 3, 1, 3, 1, 6]
def baseStart_457688 : Nat := 118140960795 + 457688 * 2 ^ 59
def prefixEnd_457688 : Nat := 4983230072969 + 3 ^ 40 * 457688 * 2
def baseEnd_457688 : Nat := 78337977931703509098379

theorem tailTrace_457688 : CollatzResearch.WordTrace tailWord_457688 prefixEnd_457688 78337977931703509098379 := by
  unfold tailWord_457688
  simp only [CollatzResearch.WordTrace]
  refine ⟨8346626382941008866162859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11128835177254678488217145 8346626382941008866162859)
  ·
    refine ⟨12519939574411513299244289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8346626382941008866162859 12519939574411513299244289)
    ·
      refine ⟨9389954680808634974433217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12519939574411513299244289 9389954680808634974433217)
      ·
        refine ⟨7042466010606476230824913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9389954680808634974433217 7042466010606476230824913)
        ·
          refine ⟨5281849507954857173118685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7042466010606476230824913 5281849507954857173118685)
          ·
            refine ⟨1980693565483071439919507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5281849507954857173118685 1980693565483071439919507)
            ·
              refine ⟨2971040348224607159879261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1980693565483071439919507 2971040348224607159879261)
              ·
                refine ⟨1114140130584227684954723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2971040348224607159879261 1114140130584227684954723)
                ·
                  refine ⟨1671210195876341527432085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1114140130584227684954723 1671210195876341527432085)
                  ·
                    refine ⟨78337977931703509098379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1671210195876341527432085 78337977931703509098379)
                    ·
                      rfl

theorem cell23_457688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 1, 6].length) (baseStart_457688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457688 prefixEnd_457688 := by exact prefixLift 457688
  have htrace : WordTrace (prefixWord ++ tailWord_457688) baseStart_457688 baseEnd_457688 := by
    simpa [prefixWord, tailWord_457688, baseEnd_457688] using wordTrace_append hprefix tailTrace_457688
  have hstable : (prefixWord ++ tailWord_457688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457688).length < 2 ^ (prefixWord ++ tailWord_457688).sum := by decide
  have hdescent : baseEnd_457688 < baseStart_457688 := by decide
  rcases family_descends (prefixWord ++ tailWord_457688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457691 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 6]
def baseStart_457691 : Nat := 118140960795 + 457691 * 2 ^ 59
def prefixEnd_457691 : Nat := 4983230072969 + 3 ^ 40 * 457691 * 2
def baseEnd_457691 : Nat := 235015474237074015557623

theorem tailTrace_457691 : CollatzResearch.WordTrace tailWord_457691 prefixEnd_457691 235015474237074015557623 := by
  unfold tailWord_457691
  simp only [CollatzResearch.WordTrace]
  refine ⟨16693362184871149244684927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11128908123247432829789951 16693362184871149244684927)
  ·
    refine ⟨25040043277306723867027391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16693362184871149244684927 25040043277306723867027391)
    ·
      refine ⟨37560064915960085800541087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25040043277306723867027391 37560064915960085800541087)
      ·
        refine ⟨56340097373940128700811631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37560064915960085800541087 56340097373940128700811631)
        ·
          refine ⟨84510146060910193051217447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56340097373940128700811631 84510146060910193051217447)
          ·
            refine ⟨126765219091365289576826171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84510146060910193051217447 126765219091365289576826171)
            ·
              refine ⟨190147828637047934365239257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126765219091365289576826171 190147828637047934365239257)
              ·
                refine ⟨142610871477785950773929443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190147828637047934365239257 142610871477785950773929443)
                ·
                  refine ⟨213916307216678926160894165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142610871477785950773929443 213916307216678926160894165)
                  ·
                    refine ⟨5013663450390912331895957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 213916307216678926160894165 5013663450390912331895957)
                    ·
                      refine ⟨235015474237074015557623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5013663450390912331895957 235015474237074015557623)
                      ·
                        rfl

theorem cell23_457691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 6].length) (baseStart_457691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457691 prefixEnd_457691 := by exact prefixLift 457691
  have htrace : WordTrace (prefixWord ++ tailWord_457691) baseStart_457691 baseEnd_457691 := by
    simpa [prefixWord, tailWord_457691, baseEnd_457691] using wordTrace_append hprefix tailTrace_457691
  have hstable : (prefixWord ++ tailWord_457691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457691).length < 2 ^ (prefixWord ++ tailWord_457691).sum := by decide
  have hdescent : baseEnd_457691 < baseStart_457691 := by decide
  rcases family_descends (prefixWord ++ tailWord_457691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457729 : List Nat := [1, 2, 4, 1, 2, 3, 2, 1, 3, 2, 2]
def baseStart_457729 : Nat := 118140960795 + 457729 * 2 ^ 59
def prefixEnd_457729 : Nat := 4983230072969 + 3 ^ 40 * 457729 * 2
def baseEnd_457729 : Nat := 235034986501944866882449

theorem tailTrace_457729 : CollatzResearch.WordTrace tailWord_457729 prefixEnd_457729 235034986501944866882449 := by
  unfold tailWord_457729
  simp only [CollatzResearch.WordTrace]
  refine ⟨16694748158733481734568241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11129832105822321156378827 16694748158733481734568241)
  ·
    refine ⟨12521061119050111300926181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16694748158733481734568241 12521061119050111300926181)
    ·
      refine ⟨2347698959821895868923659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12521061119050111300926181 2347698959821895868923659)
      ·
        refine ⟨3521548439732843803385489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2347698959821895868923659 3521548439732843803385489)
        ·
          refine ⟨2641161329799632852539117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3521548439732843803385489 2641161329799632852539117)
          ·
            refine ⟨990435498674862319702169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2641161329799632852539117 990435498674862319702169)
            ·
              refine ⟨742826624006146739776627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 990435498674862319702169 742826624006146739776627)
              ·
                refine ⟨1114239936009220109664941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 742826624006146739776627 1114239936009220109664941)
                ·
                  refine ⟨417839976003457541124353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1114239936009220109664941 417839976003457541124353)
                  ·
                    refine ⟨313379982002593155843265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 417839976003457541124353 313379982002593155843265)
                    ·
                      refine ⟨235034986501944866882449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 313379982002593155843265 235034986501944866882449)
                      ·
                        rfl

theorem cell23_457729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_457729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457729 prefixEnd_457729 := by exact prefixLift 457729
  have htrace : WordTrace (prefixWord ++ tailWord_457729) baseStart_457729 baseEnd_457729 := by
    simpa [prefixWord, tailWord_457729, baseEnd_457729] using wordTrace_append hprefix tailTrace_457729
  have hstable : (prefixWord ++ tailWord_457729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457729).length < 2 ^ (prefixWord ++ tailWord_457729).sum := by decide
  have hdescent : baseEnd_457729 < baseStart_457729 := by decide
  rcases family_descends (prefixWord ++ tailWord_457729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457742 : List Nat := [4, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4]
def baseStart_457742 : Nat := 118140960795 + 457742 * 2 ^ 59
def prefixEnd_457742 : Nat := 4983230072969 + 3 ^ 40 * 457742 * 2
def baseEnd_457742 : Nat := 235041661750453316019889

theorem tailTrace_457742 : CollatzResearch.WordTrace tailWord_457742 prefixEnd_457742 235041661750453316019889 := by
  unfold tailWord_457742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2086902788460798119348935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11130148205124256636527653 2086902788460798119348935)
  ·
    refine ⟨3130354182691197179023403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2086902788460798119348935 3130354182691197179023403)
    ·
      refine ⟨4695531274036795768535105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3130354182691197179023403 4695531274036795768535105)
      ·
        refine ⟨3521648455527596826401329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4695531274036795768535105 3521648455527596826401329)
        ·
          refine ⟨2641236341645697619800997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3521648455527596826401329 2641236341645697619800997)
          ·
            refine ⟨495231814058568303712687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2641236341645697619800997 495231814058568303712687)
            ·
              refine ⟨742847721087852455569031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495231814058568303712687 742847721087852455569031)
              ·
                refine ⟨1114271581631778683353547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 742847721087852455569031 1114271581631778683353547)
                ·
                  refine ⟨1671407372447668025030321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1114271581631778683353547 1671407372447668025030321)
                  ·
                    refine ⟨1253555529335751018772741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1671407372447668025030321 1253555529335751018772741)
                    ·
                      refine ⟨235041661750453316019889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1253555529335751018772741 235041661750453316019889)
                      ·
                        rfl

theorem cell23_457742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_457742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457742 prefixEnd_457742 := by exact prefixLift 457742
  have htrace : WordTrace (prefixWord ++ tailWord_457742) baseStart_457742 baseEnd_457742 := by
    simpa [prefixWord, tailWord_457742, baseEnd_457742] using wordTrace_append hprefix tailTrace_457742
  have hstable : (prefixWord ++ tailWord_457742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457742).length < 2 ^ (prefixWord ++ tailWord_457742).sum := by decide
  have hdescent : baseEnd_457742 < baseStart_457742 := by decide
  rcases family_descends (prefixWord ++ tailWord_457742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457755 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 7, 3, 2]
def baseStart_457755 : Nat := 118140960795 + 457755 * 2 ^ 59
def prefixEnd_457755 : Nat := 4983230072969 + 3 ^ 40 * 457755 * 2
def baseEnd_457755 : Nat := 235048336998961765157329

theorem tailTrace_457755 : CollatzResearch.WordTrace tailWord_457755 prefixEnd_457755 235048336998961765157329 := by
  unfold tailWord_457755
  simp only [CollatzResearch.WordTrace]
  refine ⟨16695696456639288175014719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11130464304426192116676479 16695696456639288175014719)
  ·
    refine ⟨25043544684958932262522079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16695696456639288175014719 25043544684958932262522079)
    ·
      refine ⟨37565317027438398393783119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25043544684958932262522079 37565317027438398393783119)
      ·
        refine ⟨56347975541157597590674679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37565317027438398393783119 56347975541157597590674679)
        ·
          refine ⟨84521963311736396386012019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56347975541157597590674679 84521963311736396386012019)
          ·
            refine ⟨126782944967604594579018029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84521963311736396386012019 126782944967604594579018029)
            ·
              refine ⟨47543604362851722967131761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126782944967604594579018029 47543604362851722967131761)
              ·
                refine ⟨35657703272138792225348821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47543604362851722967131761 35657703272138792225348821)
                ·
                  refine ⟨835727420440752942781613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 35657703272138792225348821 835727420440752942781613)
                  ·
                    refine ⟨313397782665282353543105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 835727420440752942781613 313397782665282353543105)
                    ·
                      refine ⟨235048336998961765157329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 313397782665282353543105 235048336998961765157329)
                      ·
                        rfl

theorem cell23_457755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 3, 2].length) (baseStart_457755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457755 prefixEnd_457755 := by exact prefixLift 457755
  have htrace : WordTrace (prefixWord ++ tailWord_457755) baseStart_457755 baseEnd_457755 := by
    simpa [prefixWord, tailWord_457755, baseEnd_457755] using wordTrace_append hprefix tailTrace_457755
  have hstable : (prefixWord ++ tailWord_457755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457755).length < 2 ^ (prefixWord ++ tailWord_457755).sum := by decide
  have hdescent : baseEnd_457755 < baseStart_457755 := by decide
  rcases family_descends (prefixWord ++ tailWord_457755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457762 : List Nat := [3, 3, 1, 1, 1, 3, 1, 2, 4, 1, 3]
def baseStart_457762 : Nat := 118140960795 + 457762 * 2 ^ 59
def prefixEnd_457762 : Nat := 4983230072969 + 3 ^ 40 * 457762 * 2
def baseEnd_457762 : Nat := 235051931363543237769797

theorem tailTrace_457762 : CollatzResearch.WordTrace tailWord_457762 prefixEnd_457762 235051931363543237769797 := by
  unfold tailWord_457762
  simp only [CollatzResearch.WordTrace]
  refine ⟨4173987941903482092629885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11130634511742618913679693 4173987941903482092629885)
  ·
    refine ⟨1565245478213805784736207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4173987941903482092629885 1565245478213805784736207)
    ·
      refine ⟨2347868217320708677104311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1565245478213805784736207 2347868217320708677104311)
      ·
        refine ⟨3521802325981063015656467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2347868217320708677104311 3521802325981063015656467)
        ·
          refine ⟨5282703488971594523484701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3521802325981063015656467 5282703488971594523484701)
          ·
            refine ⟨1981013808364347946306763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5282703488971594523484701 1981013808364347946306763)
            ·
              refine ⟨2971520712546521919460145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1981013808364347946306763 2971520712546521919460145)
              ·
                refine ⟨2228640534409891439595109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2971520712546521919460145 2228640534409891439595109)
                ·
                  refine ⟨417870100201854644924083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2228640534409891439595109 417870100201854644924083)
                  ·
                    refine ⟨626805150302781967386125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 417870100201854644924083 626805150302781967386125)
                    ·
                      refine ⟨235051931363543237769797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 626805150302781967386125 235051931363543237769797)
                      ·
                        rfl

theorem cell23_457762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_457762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457762 prefixEnd_457762 := by exact prefixLift 457762
  have htrace : WordTrace (prefixWord ++ tailWord_457762) baseStart_457762 baseEnd_457762 := by
    simpa [prefixWord, tailWord_457762, baseEnd_457762] using wordTrace_append hprefix tailTrace_457762
  have hstable : (prefixWord ++ tailWord_457762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457762).length < 2 ^ (prefixWord ++ tailWord_457762).sum := by decide
  have hdescent : baseEnd_457762 < baseStart_457762 := by decide
  rcases family_descends (prefixWord ++ tailWord_457762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457772 : List Nat := [2, 2, 1, 1, 1, 2, 3, 5, 1, 3, 2]
def baseStart_457772 : Nat := 118140960795 + 457772 * 2 ^ 59
def prefixEnd_457772 : Nat := 4983230072969 + 3 ^ 40 * 457772 * 2
def baseEnd_457772 : Nat := 235057066170088198644751

theorem tailTrace_457772 : CollatzResearch.WordTrace tailWord_457772 prefixEnd_457772 235057066170088198644751 := by
  unfold tailWord_457772
  simp only [CollatzResearch.WordTrace]
  refine ⟨8348158248788850039191785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11130877665051800052255713 8348158248788850039191785)
  ·
    refine ⟨6261118686591637529393839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8348158248788850039191785 6261118686591637529393839)
    ·
      refine ⟨9391678029887456294090759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6261118686591637529393839 9391678029887456294090759)
      ·
        refine ⟨14087517044831184441136139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9391678029887456294090759 14087517044831184441136139)
        ·
          refine ⟨21131275567246776661704209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14087517044831184441136139 21131275567246776661704209)
          ·
            refine ⟨15848456675435082496278157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21131275567246776661704209 15848456675435082496278157)
            ·
              refine ⟨5943171253288155936104309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15848456675435082496278157 5943171253288155936104309)
              ·
                refine ⟨557172304995764619009779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5943171253288155936104309 557172304995764619009779)
                ·
                  refine ⟨835758457493646928514669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 557172304995764619009779 835758457493646928514669)
                  ·
                    refine ⟨313409421560117598193001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 835758457493646928514669 313409421560117598193001)
                    ·
                      refine ⟨235057066170088198644751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 313409421560117598193001 235057066170088198644751)
                      ·
                        rfl

theorem cell23_457772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 3, 2].length) (baseStart_457772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457772 prefixEnd_457772 := by exact prefixLift 457772
  have htrace : WordTrace (prefixWord ++ tailWord_457772) baseStart_457772 baseEnd_457772 := by
    simpa [prefixWord, tailWord_457772, baseEnd_457772] using wordTrace_append hprefix tailTrace_457772
  have hstable : (prefixWord ++ tailWord_457772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457772).length < 2 ^ (prefixWord ++ tailWord_457772).sum := by decide
  have hdescent : baseEnd_457772 < baseStart_457772 := by decide
  rcases family_descends (prefixWord ++ tailWord_457772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457780 : List Nat := [2, 5, 1, 2, 1, 2, 3, 2, 1, 2, 2]
def baseStart_457780 : Nat := 118140960795 + 457780 * 2 ^ 59
def prefixEnd_457780 : Nat := 4983230072969 + 3 ^ 40 * 457780 * 2
def baseEnd_457780 : Nat := 235061174015324167344715

theorem tailTrace_457780 : CollatzResearch.WordTrace tailWord_457780 prefixEnd_457780 235061174015324167344715 := by
  unfold tailWord_457780
  simp only [CollatzResearch.WordTrace]
  refine ⟨8348304140774358722337397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11131072187699144963116529 8348304140774358722337397)
  ·
    refine ⟨782653513197596130219131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8348304140774358722337397 782653513197596130219131)
    ·
      refine ⟨1173980269796394195328697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 782653513197596130219131 1173980269796394195328697)
      ·
        refine ⟨880485202347295646496523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1173980269796394195328697 880485202347295646496523)
        ·
          refine ⟨1320727803520943469744785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880485202347295646496523 1320727803520943469744785)
          ·
            refine ⟨990545852640707602308589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1320727803520943469744785 990545852640707602308589)
            ·
              refine ⟨371454694740265350865721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 990545852640707602308589 371454694740265350865721)
              ·
                refine ⟨278591021055199013149291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371454694740265350865721 278591021055199013149291)
                ·
                  refine ⟨417886531582798519723937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278591021055199013149291 417886531582798519723937)
                  ·
                    refine ⟨313414898687098889792953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 417886531582798519723937 313414898687098889792953)
                    ·
                      refine ⟨235061174015324167344715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 313414898687098889792953 235061174015324167344715)
                      ·
                        rfl

theorem cell23_457780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_457780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457780 prefixEnd_457780 := by exact prefixLift 457780
  have htrace : WordTrace (prefixWord ++ tailWord_457780) baseStart_457780 baseEnd_457780 := by
    simpa [prefixWord, tailWord_457780, baseEnd_457780] using wordTrace_append hprefix tailTrace_457780
  have hstable : (prefixWord ++ tailWord_457780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457780).length < 2 ^ (prefixWord ++ tailWord_457780).sum := by decide
  have hdescent : baseEnd_457780 < baseStart_457780 := by decide
  rcases family_descends (prefixWord ++ tailWord_457780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457808 : List Nat := [2, 1, 1, 1, 1, 3, 1, 6, 7]
def baseStart_457808 : Nat := 118140960795 + 457808 * 2 ^ 59
def prefixEnd_457808 : Nat := 4983230072969 + 3 ^ 40 * 457808 * 2
def baseEnd_457808 : Nat := 26119505719294450866065

theorem tailTrace_457808 : CollatzResearch.WordTrace tailWord_457808 prefixEnd_457808 26119505719294450866065 := by
  unfold tailWord_457808
  simp only [CollatzResearch.WordTrace]
  refine ⟨8348814762723639113347039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11131753016964852151129385 8348814762723639113347039)
  ·
    refine ⟨12523222144085458670020559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8348814762723639113347039 12523222144085458670020559)
    ·
      refine ⟨18784833216128188005030839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12523222144085458670020559 18784833216128188005030839)
      ·
        refine ⟨28177249824192282007546259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18784833216128188005030839 28177249824192282007546259)
        ·
          refine ⟨42265874736288423011319389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28177249824192282007546259 42265874736288423011319389)
          ·
            refine ⟨15849703026108158629244771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42265874736288423011319389 15849703026108158629244771)
            ·
              refine ⟨23774554539162237943867157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15849703026108158629244771 23774554539162237943867157)
              ·
                refine ⟨1114432244023229903618773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23774554539162237943867157 1114432244023229903618773)
                ·
                  refine ⟨26119505719294450866065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1114432244023229903618773 26119505719294450866065)
                  ·
                    rfl

theorem cell23_457808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 7].length) (baseStart_457808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457808 prefixEnd_457808 := by exact prefixLift 457808
  have htrace : WordTrace (prefixWord ++ tailWord_457808) baseStart_457808 baseEnd_457808 := by
    simpa [prefixWord, tailWord_457808, baseEnd_457808] using wordTrace_append hprefix tailTrace_457808
  have hstable : (prefixWord ++ tailWord_457808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457808).length < 2 ^ (prefixWord ++ tailWord_457808).sum := by decide
  have hdescent : baseEnd_457808 < baseStart_457808 := by decide
  rcases family_descends (prefixWord ++ tailWord_457808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457818 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7]
def baseStart_457818 : Nat := 118140960795 + 457818 * 2 ^ 59
def prefixEnd_457818 : Nat := 4983230072969 + 3 ^ 40 * 457818 * 2
def baseEnd_457818 : Nat := 235080686280195018669539

theorem tailTrace_457818 : CollatzResearch.WordTrace tailWord_457818 prefixEnd_457818 235080686280195018669539 := by
  unfold tailWord_457818
  simp only [CollatzResearch.WordTrace]
  refine ⟨4174498563852762483639527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11131996170274033289705405 4174498563852762483639527)
  ·
    refine ⟨6261747845779143725459291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4174498563852762483639527 6261747845779143725459291)
    ·
      refine ⟨9392621768668715588188937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6261747845779143725459291 9392621768668715588188937)
      ·
        refine ⟨7044466326501536691141703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9392621768668715588188937 7044466326501536691141703)
        ·
          refine ⟨10566699489752305036712555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7044466326501536691141703 10566699489752305036712555)
          ·
            refine ⟨15850049234628457555068833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10566699489752305036712555 15850049234628457555068833)
            ·
              refine ⟨11887536925971343166301625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15850049234628457555068833 11887536925971343166301625)
              ·
                refine ⟨8915652694478507374726219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11887536925971343166301625 8915652694478507374726219)
                ·
                  refine ⟨13373479041717761062089329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8915652694478507374726219 13373479041717761062089329)
                  ·
                    refine ⟨10030109281288320796566997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13373479041717761062089329 10030109281288320796566997)
                    ·
                      refine ⟨235080686280195018669539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 10030109281288320796566997 235080686280195018669539)
                      ·
                        rfl

theorem cell23_457818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_457818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457818 prefixEnd_457818 := by exact prefixLift 457818
  have htrace : WordTrace (prefixWord ++ tailWord_457818) baseStart_457818 baseEnd_457818 := by
    simpa [prefixWord, tailWord_457818, baseEnd_457818] using wordTrace_append hprefix tailTrace_457818
  have hstable : (prefixWord ++ tailWord_457818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457818).length < 2 ^ (prefixWord ++ tailWord_457818).sum := by decide
  have hdescent : baseEnd_457818 < baseStart_457818 := by decide
  rcases family_descends (prefixWord ++ tailWord_457818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457842 : List Nat := [3, 2, 1, 2, 2, 1, 3, 4, 5]
def baseStart_457842 : Nat := 118140960795 + 457842 * 2 ^ 59
def prefixEnd_457842 : Nat := 4983230072969 + 3 ^ 40 * 457842 * 2
def baseEnd_457842 : Nat := 26121445535100324974381

theorem tailTrace_457842 : CollatzResearch.WordTrace tailWord_457842 prefixEnd_457842 26121445535100324974381 := by
  unfold tailWord_457842
  simp only [CollatzResearch.WordTrace]
  refine ⟨4174717401831025508357945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11132579738216068022287853 4174717401831025508357945)
  ·
    refine ⟨3131038051373269131268459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4174717401831025508357945 3131038051373269131268459)
    ·
      refine ⟨4696557077059903696902689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3131038051373269131268459 4696557077059903696902689)
      ·
        refine ⟨3522417807794927772677017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4696557077059903696902689 3522417807794927772677017)
        ·
          refine ⟨2641813355846195829507763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3522417807794927772677017 2641813355846195829507763)
          ·
            refine ⟨3962720033769293744261645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2641813355846195829507763 3962720033769293744261645)
            ·
              refine ⟨1486020012663485154098117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3962720033769293744261645 1486020012663485154098117)
              ·
                refine ⟨278628752374403466393397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1486020012663485154098117 278628752374403466393397)
                ·
                  refine ⟨26121445535100324974381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 278628752374403466393397 26121445535100324974381)
                  ·
                    rfl

theorem cell23_457842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4, 5].length) (baseStart_457842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457842 prefixEnd_457842 := by exact prefixLift 457842
  have htrace : WordTrace (prefixWord ++ tailWord_457842) baseStart_457842 baseEnd_457842 := by
    simpa [prefixWord, tailWord_457842, baseEnd_457842] using wordTrace_append hprefix tailTrace_457842
  have hstable : (prefixWord ++ tailWord_457842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457842).length < 2 ^ (prefixWord ++ tailWord_457842).sum := by decide
  have hdescent : baseEnd_457842 < baseStart_457842 := by decide
  rcases family_descends (prefixWord ++ tailWord_457842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457925 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 1, 7, 3]
def baseStart_457925 : Nat := 118140960795 + 457925 * 2 ^ 59
def prefixEnd_457925 : Nat := 4983230072969 + 3 ^ 40 * 457925 * 2
def baseEnd_457925 : Nat := 235135628710226100031547

theorem tailTrace_457925 : CollatzResearch.WordTrace tailWord_457925 prefixEnd_457925 235135628710226100031547 := by
  unfold tailWord_457925
  simp only [CollatzResearch.WordTrace]
  refine ⟨16701896866023407208703229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11134597910682271472468819 16701896866023407208703229)
  ·
    refine ⟨6263211324758777703263711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16701896866023407208703229 6263211324758777703263711)
    ·
      refine ⟨9394816987138166554895567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6263211324758777703263711 9394816987138166554895567)
      ·
        refine ⟨14092225480707249832343351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9394816987138166554895567 14092225480707249832343351)
        ·
          refine ⟨21138338221060874748515027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14092225480707249832343351 21138338221060874748515027)
          ·
            refine ⟨31707507331591312122772541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21138338221060874748515027 31707507331591312122772541)
            ·
              refine ⟨11890315249346742046039703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31707507331591312122772541 11890315249346742046039703)
              ·
                refine ⟨17835472874020113069059555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11890315249346742046039703 17835472874020113069059555)
                ·
                  refine ⟨26753209311030169603589333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17835472874020113069059555 26753209311030169603589333)
                  ·
                    refine ⟨627028343227269600084125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26753209311030169603589333 627028343227269600084125)
                    ·
                      refine ⟨235135628710226100031547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 627028343227269600084125 235135628710226100031547)
                      ·
                        rfl

theorem cell23_457925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 7, 3].length) (baseStart_457925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457925 prefixEnd_457925 := by exact prefixLift 457925
  have htrace : WordTrace (prefixWord ++ tailWord_457925) baseStart_457925 baseEnd_457925 := by
    simpa [prefixWord, tailWord_457925, baseEnd_457925] using wordTrace_append hprefix tailTrace_457925
  have hstable : (prefixWord ++ tailWord_457925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457925).length < 2 ^ (prefixWord ++ tailWord_457925).sum := by decide
  have hdescent : baseEnd_457925 < baseStart_457925 := by decide
  rcases family_descends (prefixWord ++ tailWord_457925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457945 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 5, 5]
def baseStart_457945 : Nat := 118140960795 + 457945 * 2 ^ 59
def prefixEnd_457945 : Nat := 4983230072969 + 3 ^ 40 * 457945 * 2
def baseEnd_457945 : Nat := 78381966107772007260485

theorem tailTrace_457945 : CollatzResearch.WordTrace tailWord_457945 prefixEnd_457945 78381966107772007260485 := by
  unfold tailWord_457945
  simp only [CollatzResearch.WordTrace]
  refine ⟨16702626325950950624431289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11135084217300633749620859 16702626325950950624431289)
  ·
    refine ⟨12526969744463212968323467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16702626325950950624431289 12526969744463212968323467)
    ·
      refine ⟨18790454616694819452485201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12526969744463212968323467 18790454616694819452485201)
      ·
        refine ⟨14092840962521114589363901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18790454616694819452485201 14092840962521114589363901)
        ·
          refine ⟨5284815360945417971011463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14092840962521114589363901 5284815360945417971011463)
          ·
            refine ⟨7927223041418126956517195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5284815360945417971011463 7927223041418126956517195)
            ·
              refine ⟨11890834562127190434775793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7927223041418126956517195 11890834562127190434775793)
              ·
                refine ⟨8918125921595392826081845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11890834562127190434775793 8918125921595392826081845)
                ·
                  refine ⟨836074305149568077445173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8918125921595392826081845 836074305149568077445173)
                  ·
                    refine ⟨78381966107772007260485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 836074305149568077445173 78381966107772007260485)
                    ·
                      rfl

theorem cell23_457945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 5].length) (baseStart_457945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_457945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_457945 prefixEnd_457945 := by exact prefixLift 457945
  have htrace : WordTrace (prefixWord ++ tailWord_457945) baseStart_457945 baseEnd_457945 := by
    simpa [prefixWord, tailWord_457945, baseEnd_457945] using wordTrace_append hprefix tailTrace_457945
  have hstable : (prefixWord ++ tailWord_457945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457945).length < 2 ^ (prefixWord ++ tailWord_457945).sum := by decide
  have hdescent : baseEnd_457945 < baseStart_457945 := by decide
  rcases family_descends (prefixWord ++ tailWord_457945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458010 : List Nat := [3, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3]
def baseStart_458010 : Nat := 118140960795 + 458010 * 2 ^ 59
def prefixEnd_458010 : Nat := 4983230072969 + 3 ^ 40 * 458010 * 2
def baseEnd_458010 : Nat := 235179274565858267468657

theorem tailTrace_458010 : CollatzResearch.WordTrace tailWord_458010 prefixEnd_458010 235179274565858267468657 := by
  unfold tailWord_458010
  simp only [CollatzResearch.WordTrace]
  refine ⟨4176249267678866681386871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11136664713810311150364989 4176249267678866681386871)
  ·
    refine ⟨6264373901518300022080307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4176249267678866681386871 6264373901518300022080307)
    ·
      refine ⟨9396560852277450033120461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6264373901518300022080307 9396560852277450033120461)
      ·
        refine ⟨3523710319604043762420173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9396560852277450033120461 3523710319604043762420173)
        ·
          refine ⟨1321391369851516410907565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3523710319604043762420173 1321391369851516410907565)
          ·
            refine ⟨495521763694318654090337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1321391369851516410907565 495521763694318654090337)
            ·
              refine ⟨371641322770738990567753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 495521763694318654090337 371641322770738990567753)
              ·
                refine ⟨278730992078054242925815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371641322770738990567753 278730992078054242925815)
                ·
                  refine ⟨418096488117081364388723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278730992078054242925815 418096488117081364388723)
                  ·
                    refine ⟨627144732175622046583085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 418096488117081364388723 627144732175622046583085)
                    ·
                      refine ⟨235179274565858267468657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 627144732175622046583085 235179274565858267468657)
                      ·
                        rfl

theorem cell23_458010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_458010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458010 prefixEnd_458010 := by exact prefixLift 458010
  have htrace : WordTrace (prefixWord ++ tailWord_458010) baseStart_458010 baseEnd_458010 := by
    simpa [prefixWord, tailWord_458010, baseEnd_458010] using wordTrace_append hprefix tailTrace_458010
  have hstable : (prefixWord ++ tailWord_458010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458010).length < 2 ^ (prefixWord ++ tailWord_458010).sum := by decide
  have hdescent : baseEnd_458010 < baseStart_458010 := by decide
  rcases family_descends (prefixWord ++ tailWord_458010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458026 : List Nat := [3, 1, 4, 2, 1, 1, 2, 3, 2, 4]
def baseStart_458026 : Nat := 118140960795 + 458026 * 2 ^ 59
def prefixEnd_458026 : Nat := 4983230072969 + 3 ^ 40 * 458026 * 2
def baseEnd_458026 : Nat := 78395830085443401622861

theorem tailTrace_458026 : CollatzResearch.WordTrace tailWord_458026 prefixEnd_458026 78395830085443401622861 := by
  unfold tailWord_458026
  simp only [CollatzResearch.WordTrace]
  refine ⟨4176395159664375364532483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11137053759105000972086621 4176395159664375364532483)
  ·
    refine ⟨6264592739496563046798725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4176395159664375364532483 6264592739496563046798725)
    ·
      refine ⟨1174611138655605571274761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6264592739496563046798725 1174611138655605571274761)
      ·
        refine ⟨880958353991704178456071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1174611138655605571274761 880958353991704178456071)
        ·
          refine ⟨1321437530987556267684107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880958353991704178456071 1321437530987556267684107)
          ·
            refine ⟨1982156296481334401526161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1321437530987556267684107 1982156296481334401526161)
            ·
              refine ⟨1486617222361000801144621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1982156296481334401526161 1486617222361000801144621)
              ·
                refine ⟨557481458385375300429233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1486617222361000801144621 557481458385375300429233)
                ·
                  refine ⟨418111093789031475321925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 557481458385375300429233 418111093789031475321925)
                  ·
                    refine ⟨78395830085443401622861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 418111093789031475321925 78395830085443401622861)
                    ·
                      rfl

theorem cell23_458026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_458026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458026 prefixEnd_458026 := by exact prefixLift 458026
  have htrace : WordTrace (prefixWord ++ tailWord_458026) baseStart_458026 baseEnd_458026 := by
    simpa [prefixWord, tailWord_458026, baseEnd_458026] using wordTrace_append hprefix tailTrace_458026
  have hstable : (prefixWord ++ tailWord_458026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458026).length < 2 ^ (prefixWord ++ tailWord_458026).sum := by decide
  have hdescent : baseEnd_458026 < baseStart_458026 := by decide
  rcases family_descends (prefixWord ++ tailWord_458026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458036 : List Nat := [2, 5, 1, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_458036 : Nat := 118140960795 + 458036 * 2 ^ 59
def prefixEnd_458036 : Nat := 4983230072969 + 3 ^ 40 * 458036 * 2
def baseEnd_458036 : Nat := 235192625062875165743537

theorem tailTrace_458036 : CollatzResearch.WordTrace tailWord_458036 prefixEnd_458036 235192625062875165743537 := by
  unfold tailWord_458036
  simp only [CollatzResearch.WordTrace]
  refine ⟨8352972684310636582996981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11137296912414182110662641 8352972684310636582996981)
  ·
    refine ⟨783091189154122179655967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8352972684310636582996981 783091189154122179655967)
    ·
      refine ⟨1174636783731183269483951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 783091189154122179655967 1174636783731183269483951)
      ·
        refine ⟨1761955175596774904225927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1174636783731183269483951 1761955175596774904225927)
        ·
          refine ⟨2642932763395162356338891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1761955175596774904225927 2642932763395162356338891)
          ·
            refine ⟨3964399145092743534508337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2642932763395162356338891 3964399145092743534508337)
            ·
              refine ⟨2973299358819557650881253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3964399145092743534508337 2973299358819557650881253)
              ·
                refine ⟨557493629778667059540235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2973299358819557650881253 557493629778667059540235)
                ·
                  refine ⟨836240444668000589310353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 557493629778667059540235 836240444668000589310353)
                  ·
                    refine ⟨627180333501000441982765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 836240444668000589310353 627180333501000441982765)
                    ·
                      refine ⟨235192625062875165743537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 627180333501000441982765 235192625062875165743537)
                      ·
                        rfl

theorem cell23_458036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_458036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458036 prefixEnd_458036 := by exact prefixLift 458036
  have htrace : WordTrace (prefixWord ++ tailWord_458036) baseStart_458036 baseEnd_458036 := by
    simpa [prefixWord, tailWord_458036, baseEnd_458036] using wordTrace_append hprefix tailTrace_458036
  have hstable : (prefixWord ++ tailWord_458036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458036).length < 2 ^ (prefixWord ++ tailWord_458036).sum := by decide
  have hdescent : baseEnd_458036 < baseStart_458036 := by decide
  rcases family_descends (prefixWord ++ tailWord_458036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458070 : List Nat := [5, 2, 3, 1, 1, 1, 1, 2, 1, 1, 5]
def baseStart_458070 : Nat := 118140960795 + 458070 * 2 ^ 59
def prefixEnd_458070 : Nat := 4983230072969 + 3 ^ 40 * 458070 * 2
def baseEnd_458070 : Nat := 235210083405128032718381

theorem tailTrace_458070 : CollatzResearch.WordTrace tailWord_458070 prefixEnd_458070 235210083405128032718381 := by
  unfold tailWord_458070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1044199090656131060795729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11138123633665397981821109 1044199090656131060795729)
  ·
    refine ⟨783149317992098295596797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1044199090656131060795729 783149317992098295596797)
    ·
      refine ⟨293680994247036860848799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 783149317992098295596797 293680994247036860848799)
      ·
        refine ⟨440521491370555291273199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293680994247036860848799 440521491370555291273199)
        ·
          refine ⟨660782237055832936909799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440521491370555291273199 660782237055832936909799)
          ·
            refine ⟨991173355583749405364699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660782237055832936909799 991173355583749405364699)
            ·
              refine ⟨1486760033375624108047049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 991173355583749405364699 1486760033375624108047049)
              ·
                refine ⟨1115070025031718081035287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1486760033375624108047049 1115070025031718081035287)
                ·
                  refine ⟨1672605037547577121552931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1115070025031718081035287 1672605037547577121552931)
                  ·
                    refine ⟨2508907556321365682329397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1672605037547577121552931 2508907556321365682329397)
                    ·
                      refine ⟨235210083405128032718381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2508907556321365682329397 235210083405128032718381)
                      ·
                        rfl

theorem cell23_458070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_458070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458070 prefixEnd_458070 := by exact prefixLift 458070
  have htrace : WordTrace (prefixWord ++ tailWord_458070) baseStart_458070 baseEnd_458070 := by
    simpa [prefixWord, tailWord_458070, baseEnd_458070] using wordTrace_append hprefix tailTrace_458070
  have hstable : (prefixWord ++ tailWord_458070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458070).length < 2 ^ (prefixWord ++ tailWord_458070).sum := by decide
  have hdescent : baseEnd_458070 < baseStart_458070 := by decide
  rcases family_descends (prefixWord ++ tailWord_458070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458077 : List Nat := [1, 4, 5, 1, 1, 1, 3, 1, 2, 4]
def baseStart_458077 : Nat := 118140960795 + 458077 * 2 ^ 59
def prefixEnd_458077 : Nat := 4983230072969 + 3 ^ 40 * 458077 * 2
def baseEnd_458077 : Nat := 78404559256569835110283

theorem tailTrace_458077 : CollatzResearch.WordTrace tailWord_458077 prefixEnd_458077 78404559256569835110283 := by
  unfold tailWord_458077
  simp only [CollatzResearch.WordTrace]
  refine ⟨16707440761472737168236485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11138293840981824778824323 16707440761472737168236485)
  ·
    refine ⟨3132645142776138219044341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16707440761472737168236485 3132645142776138219044341)
    ·
      refine ⟨293685482135262958035407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3132645142776138219044341 293685482135262958035407)
      ·
        refine ⟨440528223202894437053111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293685482135262958035407 440528223202894437053111)
        ·
          refine ⟨660792334804341655579667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440528223202894437053111 660792334804341655579667)
          ·
            refine ⟨991188502206512483369501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660792334804341655579667 991188502206512483369501)
            ·
              refine ⟨371695688327442181263563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 991188502206512483369501 371695688327442181263563)
              ·
                refine ⟨557543532491163271895345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371695688327442181263563 557543532491163271895345)
                ·
                  refine ⟨418157649368372453921509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 557543532491163271895345 418157649368372453921509)
                  ·
                    refine ⟨78404559256569835110283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 418157649368372453921509 78404559256569835110283)
                    ·
                      rfl

theorem cell23_458077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_458077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458077 prefixEnd_458077 := by exact prefixLift 458077
  have htrace : WordTrace (prefixWord ++ tailWord_458077) baseStart_458077 baseEnd_458077 := by
    simpa [prefixWord, tailWord_458077, baseEnd_458077] using wordTrace_append hprefix tailTrace_458077
  have hstable : (prefixWord ++ tailWord_458077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458077).length < 2 ^ (prefixWord ++ tailWord_458077).sum := by decide
  have hdescent : baseEnd_458077 < baseStart_458077 := by decide
  rcases family_descends (prefixWord ++ tailWord_458077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458083 : List Nat := [1, 1, 1, 5, 2, 3, 3, 1, 2, 1, 3]
def baseStart_458083 : Nat := 118140960795 + 458083 * 2 ^ 59
def prefixEnd_458083 : Nat := 4983230072969 + 3 ^ 40 * 458083 * 2
def baseEnd_458083 : Nat := 235216758653636481855821

theorem tailTrace_458083 : CollatzResearch.WordTrace tailWord_458083 prefixEnd_458083 235216758653636481855821 := by
  unfold tailWord_458083
  simp only [CollatzResearch.WordTrace]
  refine ⟨16707659599451000192954903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11138439732967333461969935 16707659599451000192954903)
  ·
    refine ⟨25061489399176500289432355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16707659599451000192954903 25061489399176500289432355)
    ·
      refine ⟨37592234098764750434148533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25061489399176500289432355 37592234098764750434148533)
      ·
        refine ⟨3524271946759195353201425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37592234098764750434148533 3524271946759195353201425)
        ·
          refine ⟨2643203960069396514901069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3524271946759195353201425 2643203960069396514901069)
          ·
            refine ⟨991201485026023693087901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2643203960069396514901069 991201485026023693087901)
            ·
              refine ⟨371700556884758884907963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 991201485026023693087901 371700556884758884907963)
              ·
                refine ⟨557550835327138327361945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371700556884758884907963 557550835327138327361945)
                ·
                  refine ⟨418163126495353745521459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 557550835327138327361945 418163126495353745521459)
                  ·
                    refine ⟨627244689743030618282189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 418163126495353745521459 627244689743030618282189)
                    ·
                      refine ⟨235216758653636481855821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 627244689743030618282189 235216758653636481855821)
                      ·
                        rfl

theorem cell23_458083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_458083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458083 prefixEnd_458083 := by exact prefixLift 458083
  have htrace : WordTrace (prefixWord ++ tailWord_458083) baseStart_458083 baseEnd_458083 := by
    simpa [prefixWord, tailWord_458083, baseEnd_458083] using wordTrace_append hprefix tailTrace_458083
  have hstable : (prefixWord ++ tailWord_458083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458083).length < 2 ^ (prefixWord ++ tailWord_458083).sum := by decide
  have hdescent : baseEnd_458083 < baseStart_458083 := by decide
  rcases family_descends (prefixWord ++ tailWord_458083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458089 : List Nat := [1, 2, 1, 1, 1, 3, 2, 5, 1, 4, 2]
def baseStart_458089 : Nat := 118140960795 + 458089 * 2 ^ 59
def prefixEnd_458089 : Nat := 4983230072969 + 3 ^ 40 * 458089 * 2
def baseEnd_458089 : Nat := 235219839537563458380793

theorem tailTrace_458089 : CollatzResearch.WordTrace tailWord_458089 prefixEnd_458089 235219839537563458380793 := by
  unfold tailWord_458089
  simp only [CollatzResearch.WordTrace]
  refine ⟨16707878437429263217673321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11138585624952842145115547 16707878437429263217673321)
  ·
    refine ⟨12530908828071947413254991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16707878437429263217673321 12530908828071947413254991)
    ·
      refine ⟨18796363242107921119882487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12530908828071947413254991 18796363242107921119882487)
      ·
        refine ⟨28194544863161881679823731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18796363242107921119882487 28194544863161881679823731)
        ·
          refine ⟨42291817294742822519735597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28194544863161881679823731 42291817294742822519735597)
          ·
            refine ⟨15859431485528558444900849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42291817294742822519735597 15859431485528558444900849)
            ·
              refine ⟨11894573614146418833675637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15859431485528558444900849 11894573614146418833675637)
              ·
                refine ⟨1115116276326226765657091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11894573614146418833675637 1115116276326226765657091)
                ·
                  refine ⟨1672674414489340148485637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1115116276326226765657091 1672674414489340148485637)
                  ·
                    refine ⟨313626452716751277841057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1672674414489340148485637 313626452716751277841057)
                    ·
                      refine ⟨235219839537563458380793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 313626452716751277841057 235219839537563458380793)
                      ·
                        rfl

theorem cell23_458089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 4, 2].length) (baseStart_458089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458089 prefixEnd_458089 := by exact prefixLift 458089
  have htrace : WordTrace (prefixWord ++ tailWord_458089) baseStart_458089 baseEnd_458089 := by
    simpa [prefixWord, tailWord_458089, baseEnd_458089] using wordTrace_append hprefix tailTrace_458089
  have hstable : (prefixWord ++ tailWord_458089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458089).length < 2 ^ (prefixWord ++ tailWord_458089).sum := by decide
  have hdescent : baseEnd_458089 < baseStart_458089 := by decide
  rcases family_descends (prefixWord ++ tailWord_458089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458093 : List Nat := [1, 5, 1, 1, 1, 4, 2, 2, 1, 3, 2]
def baseStart_458093 : Nat := 118140960795 + 458093 * 2 ^ 59
def prefixEnd_458093 : Nat := 4983230072969 + 3 ^ 40 * 458093 * 2
def baseEnd_458093 : Nat := 235221893460181442730775

theorem tailTrace_458093 : CollatzResearch.WordTrace tailWord_458093 prefixEnd_458093 235221893460181442730775 := by
  unfold tailWord_458093
  simp only [CollatzResearch.WordTrace]
  refine ⟨16708024329414771900818933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11138682886276514600545955 16708024329414771900818933)
  ·
    refine ⟨1566377280882634865701775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16708024329414771900818933 1566377280882634865701775)
    ·
      refine ⟨2349565921323952298552663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1566377280882634865701775 2349565921323952298552663)
      ·
        refine ⟨3524348881985928447828995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2349565921323952298552663 3524348881985928447828995)
        ·
          refine ⟨5286523322978892671743493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3524348881985928447828995 5286523322978892671743493)
          ·
            refine ⟨991223123058542375951905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5286523322978892671743493 991223123058542375951905)
            ·
              refine ⟨743417342293906781963929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 991223123058542375951905 743417342293906781963929)
              ·
                refine ⟨557563006720430086472947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 743417342293906781963929 557563006720430086472947)
                ·
                  refine ⟨836344510080645129709421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 557563006720430086472947 836344510080645129709421)
                  ·
                    refine ⟨313629191280241923641033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 836344510080645129709421 313629191280241923641033)
                    ·
                      refine ⟨235221893460181442730775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 313629191280241923641033 235221893460181442730775)
                      ·
                        rfl

theorem cell23_458093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_458093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458093 prefixEnd_458093 := by exact prefixLift 458093
  have htrace : WordTrace (prefixWord ++ tailWord_458093) baseStart_458093 baseEnd_458093 := by
    simpa [prefixWord, tailWord_458093, baseEnd_458093] using wordTrace_append hprefix tailTrace_458093
  have hstable : (prefixWord ++ tailWord_458093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458093).length < 2 ^ (prefixWord ++ tailWord_458093).sum := by decide
  have hdescent : baseEnd_458093 < baseStart_458093 := by decide
  rcases family_descends (prefixWord ++ tailWord_458093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458149 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 4, 5, 2]
def baseStart_458149 : Nat := 118140960795 + 458149 * 2 ^ 59
def prefixEnd_458149 : Nat := 4983230072969 + 3 ^ 40 * 458149 * 2
def baseEnd_458149 : Nat := 235250648376833223630517

theorem tailTrace_458149 : CollatzResearch.WordTrace tailWord_458149 prefixEnd_458149 235250648376833223630517 := by
  unfold tailWord_458149
  simp only [CollatzResearch.WordTrace]
  refine ⟨16710066817211893464857501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11140044544807928976571667 16710066817211893464857501)
  ·
    refine ⟨6266275056454460049321563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16710066817211893464857501 6266275056454460049321563)
    ·
      refine ⟨9399412584681690073982345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6266275056454460049321563 9399412584681690073982345)
      ·
        refine ⟨7049559438511267555486759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9399412584681690073982345 7049559438511267555486759)
        ·
          refine ⟨10574339157766901333230139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7049559438511267555486759 10574339157766901333230139)
          ·
            refine ⟨15861508736650351999845209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10574339157766901333230139 15861508736650351999845209)
            ·
              refine ⟨11896131552487763999883907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15861508736650351999845209 11896131552487763999883907)
              ·
                refine ⟨17844197328731645999825861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11896131552487763999883907 17844197328731645999825861)
                ·
                  refine ⟨3345786999137183624967349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17844197328731645999825861 3345786999137183624967349)
                  ·
                    refine ⟨313667531169110964840689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3345786999137183624967349 313667531169110964840689)
                    ·
                      refine ⟨235250648376833223630517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 313667531169110964840689 235250648376833223630517)
                      ·
                        rfl

theorem cell23_458149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 5, 2].length) (baseStart_458149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458149 prefixEnd_458149 := by exact prefixLift 458149
  have htrace : WordTrace (prefixWord ++ tailWord_458149) baseStart_458149 baseEnd_458149 := by
    simpa [prefixWord, tailWord_458149, baseEnd_458149] using wordTrace_append hprefix tailTrace_458149
  have hstable : (prefixWord ++ tailWord_458149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458149).length < 2 ^ (prefixWord ++ tailWord_458149).sum := by decide
  have hdescent : baseEnd_458149 < baseStart_458149 := by decide
  rcases family_descends (prefixWord ++ tailWord_458149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458179 : List Nat := [1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 4]
def baseStart_458179 : Nat := 118140960795 + 458179 * 2 ^ 59
def prefixEnd_458179 : Nat := 4983230072969 + 3 ^ 40 * 458179 * 2
def baseEnd_458179 : Nat := 235266052796468106255379

theorem tailTrace_458179 : CollatzResearch.WordTrace tailWord_458179 prefixEnd_458179 235266052796468106255379 := by
  unfold tailWord_458179
  simp only [CollatzResearch.WordTrace]
  refine ⟨16711161007103208588449591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11140774004735472392299727 16711161007103208588449591)
  ·
    refine ⟨25066741510654812882674387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16711161007103208588449591 25066741510654812882674387)
    ·
      refine ⟨37600112265982219324011581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25066741510654812882674387 37600112265982219324011581)
      ·
        refine ⟨14100042099743332246504343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37600112265982219324011581 14100042099743332246504343)
        ·
          refine ⟨21150063149614998369756515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14100042099743332246504343 21150063149614998369756515)
          ·
            refine ⟨31725094724422497554634773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21150063149614998369756515 31725094724422497554634773)
            ·
              refine ⟨1487113815207304572873505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31725094724422497554634773 1487113815207304572873505)
              ·
                refine ⟨1115335361405478429655129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1487113815207304572873505 1115335361405478429655129)
                ·
                  refine ⟨836501521054108822241347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1115335361405478429655129 836501521054108822241347)
                  ·
                    refine ⟨1254752281581163233362021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 836501521054108822241347 1254752281581163233362021)
                    ·
                      refine ⟨235266052796468106255379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1254752281581163233362021 235266052796468106255379)
                      ·
                        rfl

theorem cell23_458179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_458179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458179 prefixEnd_458179 := by exact prefixLift 458179
  have htrace : WordTrace (prefixWord ++ tailWord_458179) baseStart_458179 baseEnd_458179 := by
    simpa [prefixWord, tailWord_458179, baseEnd_458179] using wordTrace_append hprefix tailTrace_458179
  have hstable : (prefixWord ++ tailWord_458179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458179).length < 2 ^ (prefixWord ++ tailWord_458179).sum := by decide
  have hdescent : baseEnd_458179 < baseStart_458179 := by decide
  rcases family_descends (prefixWord ++ tailWord_458179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458180 : List Nat := [2, 3, 3, 2, 1, 3, 2, 2, 5]
def baseStart_458180 : Nat := 118140960795 + 458180 * 2 ^ 59
def prefixEnd_458180 : Nat := 4983230072969 + 3 ^ 40 * 458180 * 2
def baseEnd_458180 : Nat := 26140729586346955815875

theorem tailTrace_458180 : CollatzResearch.WordTrace tailWord_458180 prefixEnd_458180 26140729586346955815875 := by
  unfold tailWord_458180
  simp only [CollatzResearch.WordTrace]
  refine ⟨8355598740049792879617997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11140798320066390506157329 8355598740049792879617997)
  ·
    refine ⟨3133349527518672329856749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8355598740049792879617997 3133349527518672329856749)
    ·
      refine ⟨1175006072819502123696281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3133349527518672329856749 1175006072819502123696281)
      ·
        refine ⟨881254554614626592772211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1175006072819502123696281 881254554614626592772211)
        ·
          refine ⟨1321881831921939889158317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 881254554614626592772211 1321881831921939889158317)
          ·
            refine ⟨495705686970727458434369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1321881831921939889158317 495705686970727458434369)
            ·
              refine ⟨371779265228045593825777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 495705686970727458434369 371779265228045593825777)
              ·
                refine ⟨278834448921034195369333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371779265228045593825777 278834448921034195369333)
                ·
                  refine ⟨26140729586346955815875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 278834448921034195369333 26140729586346955815875)
                  ·
                    rfl

theorem cell23_458180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2, 5].length) (baseStart_458180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458180 prefixEnd_458180 := by exact prefixLift 458180
  have htrace : WordTrace (prefixWord ++ tailWord_458180) baseStart_458180 baseEnd_458180 := by
    simpa [prefixWord, tailWord_458180, baseEnd_458180] using wordTrace_append hprefix tailTrace_458180
  have hstable : (prefixWord ++ tailWord_458180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458180).length < 2 ^ (prefixWord ++ tailWord_458180).sum := by decide
  have hdescent : baseEnd_458180 < baseStart_458180 := by decide
  rcases family_descends (prefixWord ++ tailWord_458180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458192 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 6]
def baseStart_458192 : Nat := 118140960795 + 458192 * 2 ^ 59
def prefixEnd_458192 : Nat := 4983230072969 + 3 ^ 40 * 458192 * 2
def baseEnd_458192 : Nat := 235272728044976555392819

theorem tailTrace_458192 : CollatzResearch.WordTrace tailWord_458192 prefixEnd_458192 235272728044976555392819 := by
  unfold tailWord_458192
  simp only [CollatzResearch.WordTrace]
  refine ⟨8355817578028055904336415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11141090104037407872448553 8355817578028055904336415)
  ·
    refine ⟨12533726367042083856504623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8355817578028055904336415 12533726367042083856504623)
    ·
      refine ⟨18800589550563125784756935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12533726367042083856504623 18800589550563125784756935)
      ·
        refine ⟨28200884325844688677135403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18800589550563125784756935 28200884325844688677135403)
        ·
          refine ⟨42301326488767033015703105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28200884325844688677135403 42301326488767033015703105)
          ·
            refine ⟨31725994866575274761777329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42301326488767033015703105 31725994866575274761777329)
            ·
              refine ⟨23794496149931456071332997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31725994866575274761777329 23794496149931456071332997)
              ·
                refine ⟨4461468028112148013374937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23794496149931456071332997 4461468028112148013374937)
                ·
                  refine ⟨3346101021084111010031203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4461468028112148013374937 3346101021084111010031203)
                  ·
                    refine ⟨5019151531626166515046805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3346101021084111010031203 5019151531626166515046805)
                    ·
                      refine ⟨235272728044976555392819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5019151531626166515046805 235272728044976555392819)
                      ·
                        rfl

theorem cell23_458192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 6].length) (baseStart_458192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458192 prefixEnd_458192 := by exact prefixLift 458192
  have htrace : WordTrace (prefixWord ++ tailWord_458192) baseStart_458192 baseEnd_458192 := by
    simpa [prefixWord, tailWord_458192, baseEnd_458192] using wordTrace_append hprefix tailTrace_458192
  have hstable : (prefixWord ++ tailWord_458192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458192).length < 2 ^ (prefixWord ++ tailWord_458192).sum := by decide
  have hdescent : baseEnd_458192 < baseStart_458192 := by decide
  rcases family_descends (prefixWord ++ tailWord_458192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458199 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 4, 2, 3]
def baseStart_458199 : Nat := 118140960795 + 458199 * 2 ^ 59
def prefixEnd_458199 : Nat := 4983230072969 + 3 ^ 40 * 458199 * 2
def baseEnd_458199 : Nat := 235276322409558028005287

theorem tailTrace_458199 : CollatzResearch.WordTrace tailWord_458199 prefixEnd_458199 235276322409558028005287 := by
  unfold tailWord_458199
  simp only [CollatzResearch.WordTrace]
  refine ⟨16711890467030752004177651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11141260311353834669451767 16711890467030752004177651)
  ·
    refine ⟨25067835700546128006266477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16711890467030752004177651 25067835700546128006266477)
    ·
      refine ⟨9400438387704798002349929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25067835700546128006266477 9400438387704798002349929)
      ·
        refine ⟨7050328790778598501762447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9400438387704798002349929 7050328790778598501762447)
        ·
          refine ⟨10575493186167897752643671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7050328790778598501762447 10575493186167897752643671)
          ·
            refine ⟨15863239779251846628965507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10575493186167897752643671 15863239779251846628965507)
            ·
              refine ⟨23794859668877769943448261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15863239779251846628965507 23794859668877769943448261)
              ·
                refine ⟨4461536187914581864396549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23794859668877769943448261 4461536187914581864396549)
                ·
                  refine ⟨836538035233984099574353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4461536187914581864396549 836538035233984099574353)
                  ·
                    refine ⟨627403526425488074680765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 836538035233984099574353 627403526425488074680765)
                    ·
                      refine ⟨235276322409558028005287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 627403526425488074680765 235276322409558028005287)
                      ·
                        rfl

theorem cell23_458199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_458199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458199 prefixEnd_458199 := by exact prefixLift 458199
  have htrace : WordTrace (prefixWord ++ tailWord_458199) baseStart_458199 baseEnd_458199 := by
    simpa [prefixWord, tailWord_458199, baseEnd_458199] using wordTrace_append hprefix tailTrace_458199
  have hstable : (prefixWord ++ tailWord_458199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458199).length < 2 ^ (prefixWord ++ tailWord_458199).sum := by decide
  have hdescent : baseEnd_458199 < baseStart_458199 := by decide
  rcases family_descends (prefixWord ++ tailWord_458199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458213 : List Nat := [1, 3, 1, 5, 1, 3, 1, 1, 2, 1, 4]
def baseStart_458213 : Nat := 118140960795 + 458213 * 2 ^ 59
def prefixEnd_458213 : Nat := 4983230072969 + 3 ^ 40 * 458213 * 2
def baseEnd_458213 : Nat := 235283511138720973230223

theorem tailTrace_458213 : CollatzResearch.WordTrace tailWord_458213 prefixEnd_458213 235283511138720973230223 := by
  unfold tailWord_458213
  simp only [CollatzResearch.WordTrace]
  refine ⟨16712401088980032395187293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11141600725986688263458195 16712401088980032395187293)
  ·
    refine ⟨6267150408367512148195235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16712401088980032395187293 6267150408367512148195235)
    ·
      refine ⟨9400725612551268222292853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6267150408367512148195235 9400725612551268222292853)
      ·
        refine ⟨881318026176681395839955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9400725612551268222292853 881318026176681395839955)
        ·
          refine ⟨1321977039265022093759933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 881318026176681395839955 1321977039265022093759933)
          ·
            refine ⟨495741389724383285159975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1321977039265022093759933 495741389724383285159975)
            ·
              refine ⟨743612084586574927739963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495741389724383285159975 743612084586574927739963)
              ·
                refine ⟨1115418126879862391609945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 743612084586574927739963 1115418126879862391609945)
                ·
                  refine ⟨836563595159896793707459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1115418126879862391609945 836563595159896793707459)
                  ·
                    refine ⟨1254845392739845190561189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 836563595159896793707459 1254845392739845190561189)
                    ·
                      refine ⟨235283511138720973230223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1254845392739845190561189 235283511138720973230223)
                      ·
                        rfl

theorem cell23_458213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_458213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458213 prefixEnd_458213 := by exact prefixLift 458213
  have htrace : WordTrace (prefixWord ++ tailWord_458213) baseStart_458213 baseEnd_458213 := by
    simpa [prefixWord, tailWord_458213, baseEnd_458213] using wordTrace_append hprefix tailTrace_458213
  have hstable : (prefixWord ++ tailWord_458213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458213).length < 2 ^ (prefixWord ++ tailWord_458213).sum := by decide
  have hdescent : baseEnd_458213 < baseStart_458213 := by decide
  rcases family_descends (prefixWord ++ tailWord_458213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458296 : List Nat := [2, 1, 2, 1, 4, 2, 2, 1, 4, 4]
def baseStart_458296 : Nat := 118140960795 + 458296 * 2 ^ 59
def prefixEnd_458296 : Nat := 4983230072969 + 3 ^ 40 * 458296 * 2
def baseEnd_458296 : Nat := 78442043344348049497447

theorem tailTrace_458296 : CollatzResearch.WordTrace tailWord_458296 prefixEnd_458296 78442043344348049497447 := by
  unfold tailWord_458296
  simp only [CollatzResearch.WordTrace]
  refine ⟨8357714173839668785229371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11143618898452891713639161 8357714173839668785229371)
  ·
    refine ⟨12536571260759503177844057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8357714173839668785229371 12536571260759503177844057)
    ·
      refine ⟨9402428445569627383383043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12536571260759503177844057 9402428445569627383383043)
      ·
        refine ⟨14103642668354441075074565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9402428445569627383383043 14103642668354441075074565)
        ·
          refine ⟨2644433000316457701576481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14103642668354441075074565 2644433000316457701576481)
          ·
            refine ⟨1983324750237343276182361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2644433000316457701576481 1983324750237343276182361)
            ·
              refine ⟨1487493562678007457136771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1983324750237343276182361 1487493562678007457136771)
              ·
                refine ⟨2231240344017011185705157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1487493562678007457136771 2231240344017011185705157)
                ·
                  refine ⟨418357564503189597319717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2231240344017011185705157 418357564503189597319717)
                  ·
                    refine ⟨78442043344348049497447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 418357564503189597319717 78442043344348049497447)
                    ·
                      rfl

theorem cell23_458296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 4, 4].length) (baseStart_458296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458296 prefixEnd_458296 := by exact prefixLift 458296
  have htrace : WordTrace (prefixWord ++ tailWord_458296) baseStart_458296 baseEnd_458296 := by
    simpa [prefixWord, tailWord_458296, baseEnd_458296] using wordTrace_append hprefix tailTrace_458296
  have hstable : (prefixWord ++ tailWord_458296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458296).length < 2 ^ (prefixWord ++ tailWord_458296).sum := by decide
  have hdescent : baseEnd_458296 < baseStart_458296 := by decide
  rcases family_descends (prefixWord ++ tailWord_458296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458297 : List Nat := [1, 2, 1, 5, 1, 3, 3, 2, 1, 1, 3]
def baseStart_458297 : Nat := 118140960795 + 458297 * 2 ^ 59
def prefixEnd_458297 : Nat := 4983230072969 + 3 ^ 40 * 458297 * 2
def baseEnd_458297 : Nat := 235326643513698644579837

theorem tailTrace_458297 : CollatzResearch.WordTrace tailWord_458297 prefixEnd_458297 235326643513698644579837 := by
  unfold tailWord_458297
  simp only [CollatzResearch.WordTrace]
  refine ⟨16715464820675714741245145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11143643213783809827496763 16715464820675714741245145)
  ·
    refine ⟨12536598615506786055933859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16715464820675714741245145 12536598615506786055933859)
    ·
      refine ⟨18804897923260179083900789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12536598615506786055933859 18804897923260179083900789)
      ·
        refine ⟨1762959180305641789115699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18804897923260179083900789 1762959180305641789115699)
        ·
          refine ⟨2644438770458462683673549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1762959180305641789115699 2644438770458462683673549)
          ·
            refine ⟨991664538921923506377581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2644438770458462683673549 991664538921923506377581)
            ·
              refine ⟨371874202095721314891593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 991664538921923506377581 371874202095721314891593)
              ·
                refine ⟨278905651571790986168695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371874202095721314891593 278905651571790986168695)
                ·
                  refine ⟨418358477357686479253043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278905651571790986168695 418358477357686479253043)
                  ·
                    refine ⟨627537716036529718879565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 418358477357686479253043 627537716036529718879565)
                    ·
                      refine ⟨235326643513698644579837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 627537716036529718879565 235326643513698644579837)
                      ·
                        rfl

theorem cell23_458297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_458297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458297 prefixEnd_458297 := by exact prefixLift 458297
  have htrace : WordTrace (prefixWord ++ tailWord_458297) baseStart_458297 baseEnd_458297 := by
    simpa [prefixWord, tailWord_458297, baseEnd_458297] using wordTrace_append hprefix tailTrace_458297
  have hstable : (prefixWord ++ tailWord_458297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458297).length < 2 ^ (prefixWord ++ tailWord_458297).sum := by decide
  have hdescent : baseEnd_458297 < baseStart_458297 := by decide
  rcases family_descends (prefixWord ++ tailWord_458297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458309 : List Nat := [1, 3, 1, 1, 1, 4, 4, 8]
def baseStart_458309 : Nat := 118140960795 + 458309 * 2 ^ 59
def prefixEnd_458309 : Nat := 4983230072969 + 3 ^ 40 * 458309 * 2
def baseEnd_458309 : Nat := 8716029825242688801103

theorem tailTrace_458309 : CollatzResearch.WordTrace tailWord_458309 prefixEnd_458309 8716029825242688801103 := by
  unfold tailWord_458309
  simp only [CollatzResearch.WordTrace]
  refine ⟨16715902496632240790681981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11143934997754827193787987 16715902496632240790681981)
  ·
    refine ⟨6268463436237090296505743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16715902496632240790681981 6268463436237090296505743)
    ·
      refine ⟨9402695154355635444758615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6268463436237090296505743 9402695154355635444758615)
      ·
        refine ⟨14104042731533453167137923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9402695154355635444758615 14104042731533453167137923)
        ·
          refine ⟨21156064097300179750706885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14104042731533453167137923 21156064097300179750706885)
          ·
            refine ⟨3966762018243783703257541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21156064097300179750706885 3966762018243783703257541)
            ·
              refine ⟨743767878420709444360789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3966762018243783703257541 743767878420709444360789)
              ·
                refine ⟨8716029825242688801103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 743767878420709444360789 8716029825242688801103)
                ·
                  rfl

theorem cell23_458309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 8].length) (baseStart_458309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458309 prefixEnd_458309 := by exact prefixLift 458309
  have htrace : WordTrace (prefixWord ++ tailWord_458309) baseStart_458309 baseEnd_458309 := by
    simpa [prefixWord, tailWord_458309, baseEnd_458309] using wordTrace_append hprefix tailTrace_458309
  have hstable : (prefixWord ++ tailWord_458309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458309).length < 2 ^ (prefixWord ++ tailWord_458309).sum := by decide
  have hdescent : baseEnd_458309 < baseStart_458309 := by decide
  rcases family_descends (prefixWord ++ tailWord_458309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458317 : List Nat := [1, 6, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_458317 : Nat := 118140960795 + 458317 * 2 ^ 59
def prefixEnd_458317 : Nat := 4983230072969 + 3 ^ 40 * 458317 * 2
def baseEnd_458317 : Nat := 78445637708929522109915

theorem tailTrace_458317 : CollatzResearch.WordTrace tailWord_458317 prefixEnd_458317 78445637708929522109915 := by
  unfold tailWord_458317
  simp only [CollatzResearch.WordTrace]
  refine ⟨16716194280603258156973205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11144129520402172104648803 16716194280603258156973205)
  ·
    refine ⟨783571606903277726108119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16716194280603258156973205 783571606903277726108119)
    ·
      refine ⟨1175357410354916589162179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 783571606903277726108119 1175357410354916589162179)
      ·
        refine ⟨1763036115532374883743269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1175357410354916589162179 1763036115532374883743269)
        ·
          refine ⟨330569271662320290701863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1763036115532374883743269 330569271662320290701863)
          ·
            refine ⟨495853907493480436052795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330569271662320290701863 495853907493480436052795)
            ·
              refine ⟨743780861240220654079193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495853907493480436052795 743780861240220654079193)
              ·
                refine ⟨557835645930165490559395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 743780861240220654079193 557835645930165490559395)
                ·
                  refine ⟨836753468895248235839093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 557835645930165490559395 836753468895248235839093)
                  ·
                    refine ⟨78445637708929522109915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 836753468895248235839093 78445637708929522109915)
                    ·
                      rfl

theorem cell23_458317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_458317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458317 prefixEnd_458317 := by exact prefixLift 458317
  have htrace : WordTrace (prefixWord ++ tailWord_458317) baseStart_458317 baseEnd_458317 := by
    simpa [prefixWord, tailWord_458317, baseEnd_458317] using wordTrace_append hprefix tailTrace_458317
  have hstable : (prefixWord ++ tailWord_458317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458317).length < 2 ^ (prefixWord ++ tailWord_458317).sum := by decide
  have hdescent : baseEnd_458317 < baseStart_458317 := by decide
  rcases family_descends (prefixWord ++ tailWord_458317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458340 : List Nat := [2, 3, 1, 1, 2, 4, 3, 1, 1, 2, 3]
def baseStart_458340 : Nat := 118140960795 + 458340 * 2 ^ 59
def prefixEnd_458340 : Nat := 4983230072969 + 3 ^ 40 * 458340 * 2
def baseEnd_458340 : Nat := 235348723181841976342139

theorem tailTrace_458340 : CollatzResearch.WordTrace tailWord_458340 prefixEnd_458340 235348723181841976342139 := by
  unfold tailWord_458340
  simp only [CollatzResearch.WordTrace]
  refine ⟨8358516579759966542530237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11144688773013288723373649 8358516579759966542530237)
  ·
    refine ⟨3134443717409987453448839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8358516579759966542530237 3134443717409987453448839)
    ·
      refine ⟨4701665576114981180173259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3134443717409987453448839 4701665576114981180173259)
      ·
        refine ⟨7052498364172471770259889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4701665576114981180173259 7052498364172471770259889)
        ·
          refine ⟨5289373773129353827694917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7052498364172471770259889 5289373773129353827694917)
          ·
            refine ⟨991757582461753842692797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5289373773129353827694917 991757582461753842692797)
            ·
              refine ⟨371909093423157691009799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 991757582461753842692797 371909093423157691009799)
              ·
                refine ⟨557863640134736536514699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371909093423157691009799 557863640134736536514699)
                ·
                  refine ⟨836795460202104804772049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 557863640134736536514699 836795460202104804772049)
                  ·
                    refine ⟨627596595151578603579037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 836795460202104804772049 627596595151578603579037)
                    ·
                      refine ⟨235348723181841976342139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 627596595151578603579037 235348723181841976342139)
                      ·
                        rfl

theorem cell23_458340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 1, 2, 3].length) (baseStart_458340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458340 prefixEnd_458340 := by exact prefixLift 458340
  have htrace : WordTrace (prefixWord ++ tailWord_458340) baseStart_458340 baseEnd_458340 := by
    simpa [prefixWord, tailWord_458340, baseEnd_458340] using wordTrace_append hprefix tailTrace_458340
  have hstable : (prefixWord ++ tailWord_458340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458340).length < 2 ^ (prefixWord ++ tailWord_458340).sum := by decide
  have hdescent : baseEnd_458340 < baseStart_458340 := by decide
  rcases family_descends (prefixWord ++ tailWord_458340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458354 : List Nat := [3, 2, 1, 2, 3, 1, 4, 2, 1, 2, 2]
def baseStart_458354 : Nat := 118140960795 + 458354 * 2 ^ 59
def prefixEnd_458354 : Nat := 4983230072969 + 3 ^ 40 * 458354 * 2
def baseEnd_458354 : Nat := 235355911911004921567075

theorem tailTrace_458354 : CollatzResearch.WordTrace tailWord_458354 prefixEnd_458354 235355911911004921567075 := by
  unfold tailWord_458354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4179385945367303369017529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11145029187646142317380077 4179385945367303369017529)
  ·
    refine ⟨3134539459025477526763147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4179385945367303369017529 3134539459025477526763147)
    ·
      refine ⟨4701809188538216290144721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3134539459025477526763147 4701809188538216290144721)
      ·
        refine ⟨3526356891403662217608541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4701809188538216290144721 3526356891403662217608541)
        ·
          refine ⟨1322383834276373331603203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3526356891403662217608541 1322383834276373331603203)
          ·
            refine ⟨1983575751414559997404805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1322383834276373331603203 1983575751414559997404805)
            ·
              refine ⟨371920453390229999513401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1983575751414559997404805 371920453390229999513401)
              ·
                refine ⟨278940340042672499635051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371920453390229999513401 278940340042672499635051)
                ·
                  refine ⟨418410510064008749452577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278940340042672499635051 418410510064008749452577)
                  ·
                    refine ⟨313807882548006562089433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 418410510064008749452577 313807882548006562089433)
                    ·
                      refine ⟨235355911911004921567075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 313807882548006562089433 235355911911004921567075)
                      ·
                        rfl

theorem cell23_458354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_458354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458354 prefixEnd_458354 := by exact prefixLift 458354
  have htrace : WordTrace (prefixWord ++ tailWord_458354) baseStart_458354 baseEnd_458354 := by
    simpa [prefixWord, tailWord_458354, baseEnd_458354] using wordTrace_append hprefix tailTrace_458354
  have hstable : (prefixWord ++ tailWord_458354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458354).length < 2 ^ (prefixWord ++ tailWord_458354).sum := by decide
  have hdescent : baseEnd_458354 < baseStart_458354 := by decide
  rcases family_descends (prefixWord ++ tailWord_458354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458446 : List Nat := [4, 1, 1, 1, 3, 1, 1, 3, 1, 7]
def baseStart_458446 : Nat := 118140960795 + 458446 * 2 ^ 59
def prefixEnd_458446 : Nat := 4983230072969 + 3 ^ 40 * 458446 * 2
def baseEnd_458446 : Nat := 78467717377072853872217

theorem tailTrace_458446 : CollatzResearch.WordTrace tailWord_458446 prefixEnd_458446 78467717377072853872217 := by
  unfold tailWord_458446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2090112412141989148552399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11147266198090608792279461 2090112412141989148552399)
  ·
    refine ⟨3135168618212983722828599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2090112412141989148552399 3135168618212983722828599)
    ·
      refine ⟨4702752927319475584242899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3135168618212983722828599 4702752927319475584242899)
      ·
        refine ⟨7054129390979213376364349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4702752927319475584242899 7054129390979213376364349)
        ·
          refine ⟨2645298521617205016136631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7054129390979213376364349 2645298521617205016136631)
          ·
            refine ⟨3967947782425807524204947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2645298521617205016136631 3967947782425807524204947)
            ·
              refine ⟨5951921673638711286307421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3967947782425807524204947 5951921673638711286307421)
              ·
                refine ⟨2231970627614516732365283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5951921673638711286307421 2231970627614516732365283)
                ·
                  refine ⟨3347955941421775098547925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2231970627614516732365283 3347955941421775098547925)
                  ·
                    refine ⟨78467717377072853872217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3347955941421775098547925 78467717377072853872217)
                    ·
                      rfl

theorem cell23_458446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_458446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458446 prefixEnd_458446 := by exact prefixLift 458446
  have htrace : WordTrace (prefixWord ++ tailWord_458446) baseStart_458446 baseEnd_458446 := by
    simpa [prefixWord, tailWord_458446, baseEnd_458446] using wordTrace_append hprefix tailTrace_458446
  have hstable : (prefixWord ++ tailWord_458446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458446).length < 2 ^ (prefixWord ++ tailWord_458446).sum := by decide
  have hdescent : baseEnd_458446 < baseStart_458446 := by decide
  rcases family_descends (prefixWord ++ tailWord_458446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458450 : List Nat := [3, 2, 2, 2, 2, 1, 3, 3, 5]
def baseStart_458450 : Nat := 118140960795 + 458450 * 2 ^ 59
def prefixEnd_458450 : Nat := 4983230072969 + 3 ^ 40 * 458450 * 2
def baseEnd_458450 : Nat := 26156134005981838440737

theorem tailTrace_458450 : CollatzResearch.WordTrace tailWord_458450 prefixEnd_458450 26156134005981838440737 := by
  unfold tailWord_458450
  simp only [CollatzResearch.WordTrace]
  refine ⟨4180261297280355467891201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11147363459414281247709869 4180261297280355467891201)
  ·
    refine ⟨3135195972960266600918401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4180261297280355467891201 3135195972960266600918401)
    ·
      refine ⟨2351396979720199950688801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3135195972960266600918401 2351396979720199950688801)
      ·
        refine ⟨1763547734790149963016601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2351396979720199950688801 1763547734790149963016601)
        ·
          refine ⟨1322660801092612472262451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1763547734790149963016601 1322660801092612472262451)
          ·
            refine ⟨1983991201638918708393677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1322660801092612472262451 1983991201638918708393677)
            ·
              refine ⟨743996700614594515647629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1983991201638918708393677 743996700614594515647629)
              ·
                refine ⟨278998762730472943367861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 743996700614594515647629 278998762730472943367861)
                ·
                  refine ⟨26156134005981838440737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 278998762730472943367861 26156134005981838440737)
                  ·
                    rfl

theorem cell23_458450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3, 5].length) (baseStart_458450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458450 prefixEnd_458450 := by exact prefixLift 458450
  have htrace : WordTrace (prefixWord ++ tailWord_458450) baseStart_458450 baseEnd_458450 := by
    simpa [prefixWord, tailWord_458450, baseEnd_458450] using wordTrace_append hprefix tailTrace_458450
  have hstable : (prefixWord ++ tailWord_458450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458450).length < 2 ^ (prefixWord ++ tailWord_458450).sum := by decide
  have hdescent : baseEnd_458450 < baseStart_458450 := by decide
  rcases family_descends (prefixWord ++ tailWord_458450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458456 : List Nat := [2, 1, 2, 2, 3, 1, 2, 2, 1, 2, 5]
def baseStart_458456 : Nat := 118140960795 + 458456 * 2 ^ 59
def prefixEnd_458456 : Nat := 4983230072969 + 3 ^ 40 * 458456 * 2
def baseEnd_458456 : Nat := 235408286937763522491605

theorem tailTrace_458456 : CollatzResearch.WordTrace tailWord_458456 prefixEnd_458456 235408286937763522491605 := by
  unfold tailWord_458456
  simp only [CollatzResearch.WordTrace]
  refine ⟨8360632013549842448141611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11147509351399789930855481 8360632013549842448141611)
  ·
    refine ⟨12540948020324763672212417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8360632013549842448141611 12540948020324763672212417)
    ·
      refine ⟨9405711015243572754159313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12540948020324763672212417 9405711015243572754159313)
      ·
        refine ⟨7054283261432679565619485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9405711015243572754159313 7054283261432679565619485)
        ·
          refine ⟨2645356223037254837107307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7054283261432679565619485 2645356223037254837107307)
          ·
            refine ⟨3968034334555882255660961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2645356223037254837107307 3968034334555882255660961)
            ·
              refine ⟨2976025750916911691745721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3968034334555882255660961 2976025750916911691745721)
              ·
                refine ⟨2232019313187683768809291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2976025750916911691745721 2232019313187683768809291)
                ·
                  refine ⟨3348028969781525653213937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2232019313187683768809291 3348028969781525653213937)
                  ·
                    refine ⟨2511021727336144239910453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3348028969781525653213937 2511021727336144239910453)
                    ·
                      refine ⟨235408286937763522491605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2511021727336144239910453 235408286937763522491605)
                      ·
                        rfl

theorem cell23_458456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_458456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458456 prefixEnd_458456 := by exact prefixLift 458456
  have htrace : WordTrace (prefixWord ++ tailWord_458456) baseStart_458456 baseEnd_458456 := by
    simpa [prefixWord, tailWord_458456, baseEnd_458456] using wordTrace_append hprefix tailTrace_458456
  have hstable : (prefixWord ++ tailWord_458456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458456).length < 2 ^ (prefixWord ++ tailWord_458456).sum := by decide
  have hdescent : baseEnd_458456 < baseStart_458456 := by decide
  rcases family_descends (prefixWord ++ tailWord_458456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458467 : List Nat := [1, 1, 1, 7, 2, 1, 3, 2, 5]
def baseStart_458467 : Nat := 118140960795 + 458467 * 2 ^ 59
def prefixEnd_458467 : Nat := 4983230072969 + 3 ^ 40 * 458467 * 2
def baseEnd_458467 : Nat := 26157103913884775494895

theorem tailTrace_458467 : CollatzResearch.WordTrace tailWord_458467 prefixEnd_458467 26157103913884775494895 := by
  unfold tailWord_458467
  simp only [CollatzResearch.WordTrace]
  refine ⟨16721665230059833774933655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11147776820039889183289103 16721665230059833774933655)
  ·
    refine ⟨25082497845089750662400483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16721665230059833774933655 25082497845089750662400483)
    ·
      refine ⟨37623746767634625993600725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25082497845089750662400483 37623746767634625993600725)
      ·
        refine ⟨881806564866436546725017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 37623746767634625993600725 881806564866436546725017)
        ·
          refine ⟨661354923649827410043763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 881806564866436546725017 661354923649827410043763)
          ·
            refine ⟨992032385474741115065645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661354923649827410043763 992032385474741115065645)
            ·
              refine ⟨372012144553027918149617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 992032385474741115065645 372012144553027918149617)
              ·
                refine ⟨279009108414770938612213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372012144553027918149617 279009108414770938612213)
                ·
                  refine ⟨26157103913884775494895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 279009108414770938612213 26157103913884775494895)
                  ·
                    rfl

theorem cell23_458467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2, 5].length) (baseStart_458467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458467 prefixEnd_458467 := by exact prefixLift 458467
  have htrace : WordTrace (prefixWord ++ tailWord_458467) baseStart_458467 baseEnd_458467 := by
    simpa [prefixWord, tailWord_458467, baseEnd_458467] using wordTrace_append hprefix tailTrace_458467
  have hstable : (prefixWord ++ tailWord_458467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458467).length < 2 ^ (prefixWord ++ tailWord_458467).sum := by decide
  have hdescent : baseEnd_458467 < baseStart_458467 := by decide
  rcases family_descends (prefixWord ++ tailWord_458467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458483 : List Nat := [1, 1, 1, 2, 2, 3, 2, 3, 2, 4, 2]
def baseStart_458483 : Nat := 118140960795 + 458483 * 2 ^ 59
def prefixEnd_458483 : Nat := 4983230072969 + 3 ^ 40 * 458483 * 2
def baseEnd_458483 : Nat := 235422150915434916853981

theorem tailTrace_458483 : CollatzResearch.WordTrace tailWord_458483 prefixEnd_458483 235422150915434916853981 := by
  unfold tailWord_458483
  simp only [CollatzResearch.WordTrace]
  refine ⟨16722248798001868507516103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11148165865334579005010735 16722248798001868507516103)
  ·
    refine ⟨25083373197002802761274155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16722248798001868507516103 25083373197002802761274155)
    ·
      refine ⟨37625059795504204141911233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25083373197002802761274155 37625059795504204141911233)
      ·
        refine ⟨28218794846628153106433425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37625059795504204141911233 28218794846628153106433425)
        ·
          refine ⟨21164096134971114829825069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28218794846628153106433425 21164096134971114829825069)
          ·
            refine ⟨7936536050614168061184401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21164096134971114829825069 7936536050614168061184401)
            ·
              refine ⟨5952402037960626045888301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7936536050614168061184401 5952402037960626045888301)
              ·
                refine ⟨2232150764235234767208113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5952402037960626045888301 2232150764235234767208113)
                ·
                  refine ⟨1674113073176426075406085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2232150764235234767208113 1674113073176426075406085)
                  ·
                    refine ⟨313896201220579889138641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1674113073176426075406085 313896201220579889138641)
                    ·
                      refine ⟨235422150915434916853981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 313896201220579889138641 235422150915434916853981)
                      ·
                        rfl

theorem cell23_458483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 4, 2].length) (baseStart_458483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458483 prefixEnd_458483 := by exact prefixLift 458483
  have htrace : WordTrace (prefixWord ++ tailWord_458483) baseStart_458483 baseEnd_458483 := by
    simpa [prefixWord, tailWord_458483, baseEnd_458483] using wordTrace_append hprefix tailTrace_458483
  have hstable : (prefixWord ++ tailWord_458483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458483).length < 2 ^ (prefixWord ++ tailWord_458483).sum := by decide
  have hdescent : baseEnd_458483 < baseStart_458483 := by decide
  rcases family_descends (prefixWord ++ tailWord_458483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458500 : List Nat := [2, 3, 2, 2, 1, 3, 2, 1, 2, 1, 4]
def baseStart_458500 : Nat := 118140960795 + 458500 * 2 ^ 59
def prefixEnd_458500 : Nat := 4983230072969 + 3 ^ 40 * 458500 * 2
def baseEnd_458500 : Nat := 235430880086561350341403

theorem tailTrace_458500 : CollatzResearch.WordTrace tailWord_458500 prefixEnd_458500 235430880086561350341403 := by
  unfold tailWord_458500
  simp only [CollatzResearch.WordTrace]
  refine ⟨8361434419470140205442477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11148579225960186940589969 8361434419470140205442477)
  ·
    refine ⟨3135537907301302577040929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8361434419470140205442477 3135537907301302577040929)
    ·
      refine ⟨2351653430475976932780697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3135537907301302577040929 2351653430475976932780697)
      ·
        refine ⟨1763740072856982699585523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2351653430475976932780697 1763740072856982699585523)
        ·
          refine ⟨2645610109285474049378285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1763740072856982699585523 2645610109285474049378285)
          ·
            refine ⟨992103790982052768516857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2645610109285474049378285 992103790982052768516857)
            ·
              refine ⟨744077843236539576387643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 992103790982052768516857 744077843236539576387643)
              ·
                refine ⟨1116116764854809364581465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 744077843236539576387643 1116116764854809364581465)
                ·
                  refine ⟨837087573641107023436099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1116116764854809364581465 837087573641107023436099)
                  ·
                    refine ⟨1255631360461660535154149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 837087573641107023436099 1255631360461660535154149)
                    ·
                      refine ⟨235430880086561350341403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1255631360461660535154149 235430880086561350341403)
                      ·
                        rfl

theorem cell23_458500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_458500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458500 prefixEnd_458500 := by exact prefixLift 458500
  have htrace : WordTrace (prefixWord ++ tailWord_458500) baseStart_458500 baseEnd_458500 := by
    simpa [prefixWord, tailWord_458500, baseEnd_458500] using wordTrace_append hprefix tailTrace_458500
  have hstable : (prefixWord ++ tailWord_458500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458500).length < 2 ^ (prefixWord ++ tailWord_458500).sum := by decide
  have hdescent : baseEnd_458500 < baseStart_458500 := by decide
  rcases family_descends (prefixWord ++ tailWord_458500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458543 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 3, 5, 2]
def baseStart_458543 : Nat := 118140960795 + 458543 * 2 ^ 59
def prefixEnd_458543 : Nat := 4983230072969 + 3 ^ 40 * 458543 * 2
def baseEnd_458543 : Nat := 235452959754704682103705

theorem tailTrace_458543 : CollatzResearch.WordTrace tailWord_458543 prefixEnd_458543 235452959754704682103705 := by
  unfold tailWord_458543
  simp only [CollatzResearch.WordTrace]
  refine ⟨16724437177784498754700283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11149624785189665836466855 16724437177784498754700283)
  ·
    refine ⟨25086655766676748132050425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16724437177784498754700283 25086655766676748132050425)
    ·
      refine ⟨18814991825007561099037819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25086655766676748132050425 18814991825007561099037819)
      ·
        refine ⟨28222487737511341648556729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18814991825007561099037819 28222487737511341648556729)
        ·
          refine ⟨21166865803133506236417547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28222487737511341648556729 21166865803133506236417547)
          ·
            refine ⟨31750298704700259354626321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21166865803133506236417547 31750298704700259354626321)
            ·
              refine ⟨23812724028525194515969741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31750298704700259354626321 23812724028525194515969741)
              ·
                refine ⟨8929771510696947943488653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23812724028525194515969741 8929771510696947943488653)
                ·
                  refine ⟨3348664316511355478808245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8929771510696947943488653 3348664316511355478808245)
                  ·
                    refine ⟨313937279672939576138273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3348664316511355478808245 313937279672939576138273)
                    ·
                      refine ⟨235452959754704682103705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 313937279672939576138273 235452959754704682103705)
                      ·
                        rfl

theorem cell23_458543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 5, 2].length) (baseStart_458543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458543 prefixEnd_458543 := by exact prefixLift 458543
  have htrace : WordTrace (prefixWord ++ tailWord_458543) baseStart_458543 baseEnd_458543 := by
    simpa [prefixWord, tailWord_458543, baseEnd_458543] using wordTrace_append hprefix tailTrace_458543
  have hstable : (prefixWord ++ tailWord_458543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458543).length < 2 ^ (prefixWord ++ tailWord_458543).sum := by decide
  have hdescent : baseEnd_458543 < baseStart_458543 := by decide
  rcases family_descends (prefixWord ++ tailWord_458543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458567 : List Nat := [1, 1, 4, 1, 2, 1, 3, 5, 1, 1, 3]
def baseStart_458567 : Nat := 118140960795 + 458567 * 2 ^ 59
def prefixEnd_458567 : Nat := 4983230072969 + 3 ^ 40 * 458567 * 2
def baseEnd_458567 : Nat := 235465283290412588203595

theorem tailTrace_458567 : CollatzResearch.WordTrace tailWord_458567 prefixEnd_458567 235465283290412588203595 := by
  unfold tailWord_458567
  simp only [CollatzResearch.WordTrace]
  refine ⟨16725312529697550853573955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11150208353131700569049303 16725312529697550853573955)
  ·
    refine ⟨25087968794546326280360933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16725312529697550853573955 25087968794546326280360933)
    ·
      refine ⟨4703994148977436177567675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25087968794546326280360933 4703994148977436177567675)
      ·
        refine ⟨7055991223466154266351513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4703994148977436177567675 7055991223466154266351513)
        ·
          refine ⟨5291993417599615699763635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7055991223466154266351513 5291993417599615699763635)
          ·
            refine ⟨7937990126399423549645453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5291993417599615699763635 7937990126399423549645453)
            ·
              refine ⟨2976746297399783831117045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7937990126399423549645453 2976746297399783831117045)
              ·
                refine ⟨279069965381229734167223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2976746297399783831117045 279069965381229734167223)
                ·
                  refine ⟨418604948071844601250835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279069965381229734167223 418604948071844601250835)
                  ·
                    refine ⟨627907422107766901876253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 418604948071844601250835 627907422107766901876253)
                    ·
                      refine ⟨235465283290412588203595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 627907422107766901876253 235465283290412588203595)
                      ·
                        rfl

theorem cell23_458567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5, 1, 1, 3].length) (baseStart_458567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458567 prefixEnd_458567 := by exact prefixLift 458567
  have htrace : WordTrace (prefixWord ++ tailWord_458567) baseStart_458567 baseEnd_458567 := by
    simpa [prefixWord, tailWord_458567, baseEnd_458567] using wordTrace_append hprefix tailTrace_458567
  have hstable : (prefixWord ++ tailWord_458567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458567).length < 2 ^ (prefixWord ++ tailWord_458567).sum := by decide
  have hdescent : baseEnd_458567 < baseStart_458567 := by decide
  rcases family_descends (prefixWord ++ tailWord_458567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458593 : List Nat := [1, 2, 3, 1, 1, 1, 5, 2, 1, 1, 5]
def baseStart_458593 : Nat := 118140960795 + 458593 * 2 ^ 59
def prefixEnd_458593 : Nat := 4983230072969 + 3 ^ 40 * 458593 * 2
def baseEnd_458593 : Nat := 235478633787429486478475

theorem tailTrace_458593 : CollatzResearch.WordTrace tailWord_458593 prefixEnd_458593 235478633787429486478475 := by
  unfold tailWord_458593
  simp only [CollatzResearch.WordTrace]
  refine ⟨16726260827603357294020433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11150840551735571529346955 16726260827603357294020433)
  ·
    refine ⟨12544695620702517970515325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16726260827603357294020433 12544695620702517970515325)
    ·
      refine ⟨4704260857763444238943247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12544695620702517970515325 4704260857763444238943247)
      ·
        refine ⟨7056391286645166358414871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4704260857763444238943247 7056391286645166358414871)
        ·
          refine ⟨10584586929967749537622307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7056391286645166358414871 10584586929967749537622307)
          ·
            refine ⟨15876880394951624306433461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10584586929967749537622307 15876880394951624306433461)
            ·
              refine ⟨1488457537026714778728137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15876880394951624306433461 1488457537026714778728137)
              ·
                refine ⟨1116343152770036084046103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1488457537026714778728137 1116343152770036084046103)
                ·
                  refine ⟨1674514729155054126069155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1116343152770036084046103 1674514729155054126069155)
                  ·
                    refine ⟨2511772093732581189103733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1674514729155054126069155 2511772093732581189103733)
                    ·
                      refine ⟨235478633787429486478475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2511772093732581189103733 235478633787429486478475)
                      ·
                        rfl

theorem cell23_458593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_458593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458593 prefixEnd_458593 := by exact prefixLift 458593
  have htrace : WordTrace (prefixWord ++ tailWord_458593) baseStart_458593 baseEnd_458593 := by
    simpa [prefixWord, tailWord_458593, baseEnd_458593] using wordTrace_append hprefix tailTrace_458593
  have hstable : (prefixWord ++ tailWord_458593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458593).length < 2 ^ (prefixWord ++ tailWord_458593).sum := by decide
  have hdescent : baseEnd_458593 < baseStart_458593 := by decide
  rcases family_descends (prefixWord ++ tailWord_458593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458613 : List Nat := [1, 3, 4, 1, 1, 1, 3, 9]
def baseStart_458613 : Nat := 118140960795 + 458613 * 2 ^ 59
def prefixEnd_458613 : Nat := 4983230072969 + 3 ^ 40 * 458613 * 2
def baseEnd_458613 : Nat := 8721811237056274378829

theorem tailTrace_458613 : CollatzResearch.WordTrace tailWord_458613 prefixEnd_458613 8721811237056274378829 := by
  unfold tailWord_458613
  simp only [CollatzResearch.WordTrace]
  refine ⟨16726990287530900709748493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11151326858353933806498995 16726990287530900709748493)
  ·
    refine ⟨6272621357824087766155685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16726990287530900709748493 6272621357824087766155685)
    ·
      refine ⟨1176116504592016456154191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6272621357824087766155685 1176116504592016456154191)
      ·
        refine ⟨1764174756888024684231287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1176116504592016456154191 1764174756888024684231287)
        ·
          refine ⟨2646262135332037026346931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1764174756888024684231287 2646262135332037026346931)
          ·
            refine ⟨3969393202998055539520397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2646262135332037026346931 3969393202998055539520397)
            ·
              refine ⟨1488522451124270827320149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3969393202998055539520397 1488522451124270827320149)
              ·
                refine ⟨8721811237056274378829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1488522451124270827320149 8721811237056274378829)
                ·
                  rfl

theorem cell23_458613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 9].length) (baseStart_458613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458613 prefixEnd_458613 := by exact prefixLift 458613
  have htrace : WordTrace (prefixWord ++ tailWord_458613) baseStart_458613 baseEnd_458613 := by
    simpa [prefixWord, tailWord_458613, baseEnd_458613] using wordTrace_append hprefix tailTrace_458613
  have hstable : (prefixWord ++ tailWord_458613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458613).length < 2 ^ (prefixWord ++ tailWord_458613).sum := by decide
  have hdescent : baseEnd_458613 < baseStart_458613 := by decide
  rcases family_descends (prefixWord ++ tailWord_458613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458623 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 3, 3, 3]
def baseStart_458623 : Nat := 118140960795 + 458623 * 2 ^ 59
def prefixEnd_458623 : Nat := 4983230072969 + 3 ^ 40 * 458623 * 2
def baseEnd_458623 : Nat := 235494038207064369103337

theorem tailTrace_458623 : CollatzResearch.WordTrace tailWord_458623 prefixEnd_458623 235494038207064369103337 := by
  unfold tailWord_458623
  simp only [CollatzResearch.WordTrace]
  refine ⟨16727355017494672417612523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11151570011663114945075015 16727355017494672417612523)
  ·
    refine ⟨25091032526242008626418785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16727355017494672417612523 25091032526242008626418785)
    ·
      refine ⟨18818274394681506469814089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25091032526242008626418785 18818274394681506469814089)
      ·
        refine ⟨14113705796011129852360567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18818274394681506469814089 14113705796011129852360567)
        ·
          refine ⟨21170558694016694778540851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14113705796011129852360567 21170558694016694778540851)
          ·
            refine ⟨31755838041025042167811277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21170558694016694778540851 31755838041025042167811277)
            ·
              refine ⟨11908439265384390812929229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31755838041025042167811277 11908439265384390812929229)
              ·
                refine ⟨4465664724519146554848461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11908439265384390812929229 4465664724519146554848461)
                ·
                  refine ⟨1674624271694679958068173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4465664724519146554848461 1674624271694679958068173)
                  ·
                    refine ⟨627984101885504984275565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1674624271694679958068173 627984101885504984275565)
                    ·
                      refine ⟨235494038207064369103337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 627984101885504984275565 235494038207064369103337)
                      ·
                        rfl

theorem cell23_458623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3, 3].length) (baseStart_458623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458623 prefixEnd_458623 := by exact prefixLift 458623
  have htrace : WordTrace (prefixWord ++ tailWord_458623) baseStart_458623 baseEnd_458623 := by
    simpa [prefixWord, tailWord_458623, baseEnd_458623] using wordTrace_append hprefix tailTrace_458623
  have hstable : (prefixWord ++ tailWord_458623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458623).length < 2 ^ (prefixWord ++ tailWord_458623).sum := by decide
  have hdescent : baseEnd_458623 < baseStart_458623 := by decide
  rcases family_descends (prefixWord ++ tailWord_458623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458683 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 1, 6, 3]
def baseStart_458683 : Nat := 118140960795 + 458683 * 2 ^ 59
def prefixEnd_458683 : Nat := 4983230072969 + 3 ^ 40 * 458683 * 2
def baseEnd_458683 : Nat := 235524847046334134353061

theorem tailTrace_458683 : CollatzResearch.WordTrace tailWord_458683 prefixEnd_458683 235524847046334134353061 := by
  unfold tailWord_458683
  simp only [CollatzResearch.WordTrace]
  refine ⟨16729543397277302664796703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11153028931518201776531135 16729543397277302664796703)
  ·
    refine ⟨25094315095915953997195055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16729543397277302664796703 25094315095915953997195055)
    ·
      refine ⟨37641472643873930995792583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25094315095915953997195055 37641472643873930995792583)
      ·
        refine ⟨56462208965810896493688875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37641472643873930995792583 56462208965810896493688875)
        ·
          refine ⟨84693313448716344740533313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56462208965810896493688875 84693313448716344740533313)
          ·
            refine ⟨63519985086537258555399985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84693313448716344740533313 63519985086537258555399985)
            ·
              refine ⟨47639988814902943916549989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63519985086537258555399985 47639988814902943916549989)
              ·
                refine ⟨8932497902794301984353123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47639988814902943916549989 8932497902794301984353123)
                ·
                  refine ⟨13398746854191452976529685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8932497902794301984353123 13398746854191452976529685)
                  ·
                    refine ⟨628066258790224358274829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13398746854191452976529685 628066258790224358274829)
                    ·
                      refine ⟨235524847046334134353061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 628066258790224358274829 235524847046334134353061)
                      ·
                        rfl

theorem cell23_458683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6, 3].length) (baseStart_458683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458683 prefixEnd_458683 := by exact prefixLift 458683
  have htrace : WordTrace (prefixWord ++ tailWord_458683) baseStart_458683 baseEnd_458683 := by
    simpa [prefixWord, tailWord_458683, baseEnd_458683] using wordTrace_append hprefix tailTrace_458683
  have hstable : (prefixWord ++ tailWord_458683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458683).length < 2 ^ (prefixWord ++ tailWord_458683).sum := by decide
  have hdescent : baseEnd_458683 < baseStart_458683 := by decide
  rcases family_descends (prefixWord ++ tailWord_458683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458700 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 2, 4, 3]
def baseStart_458700 : Nat := 118140960795 + 458700 * 2 ^ 59
def prefixEnd_458700 : Nat := 4983230072969 + 3 ^ 40 * 458700 * 2
def baseEnd_458700 : Nat := 235533576217460567840483

theorem tailTrace_458700 : CollatzResearch.WordTrace tailWord_458700 prefixEnd_458700 235533576217460567840483 := by
  unfold tailWord_458700
  simp only [CollatzResearch.WordTrace]
  refine ⟨8365081719107857284082777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11153442292143809712110369 8365081719107857284082777)
  ·
    refine ⟨6273811289330892963062083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8365081719107857284082777 6273811289330892963062083)
    ·
      refine ⟨9410716933996339444593125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6273811289330892963062083 9410716933996339444593125)
      ·
        refine ⟨1764509425124313645861211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9410716933996339444593125 1764509425124313645861211)
        ·
          refine ⟨2646764137686470468791817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1764509425124313645861211 2646764137686470468791817)
          ·
            refine ⟨1985073103264852851593863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2646764137686470468791817 1985073103264852851593863)
            ·
              refine ⟨2977609654897279277390795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1985073103264852851593863 2977609654897279277390795)
              ·
                refine ⟨4466414482345918916086193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2977609654897279277390795 4466414482345918916086193)
                ·
                  refine ⟨3349810861759439187064645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4466414482345918916086193 3349810861759439187064645)
                  ·
                    refine ⟨628089536579894847574621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3349810861759439187064645 628089536579894847574621)
                    ·
                      refine ⟨235533576217460567840483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 628089536579894847574621 235533576217460567840483)
                      ·
                        rfl

theorem cell23_458700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_458700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458700 prefixEnd_458700 := by exact prefixLift 458700
  have htrace : WordTrace (prefixWord ++ tailWord_458700) baseStart_458700 baseEnd_458700 := by
    simpa [prefixWord, tailWord_458700, baseEnd_458700] using wordTrace_append hprefix tailTrace_458700
  have hstable : (prefixWord ++ tailWord_458700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458700).length < 2 ^ (prefixWord ++ tailWord_458700).sum := by decide
  have hdescent : baseEnd_458700 < baseStart_458700 := by decide
  rcases family_descends (prefixWord ++ tailWord_458700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458703 : List Nat := [1, 1, 2, 1, 1, 5, 2, 3, 7]
def baseStart_458703 : Nat := 118140960795 + 458703 * 2 ^ 59
def prefixEnd_458703 : Nat := 4983230072969 + 3 ^ 40 * 458703 * 2
def baseEnd_458703 : Nat := 26170568517713784011441

theorem tailTrace_458703 : CollatzResearch.WordTrace tailWord_458703 prefixEnd_458703 26170568517713784011441 := by
  unfold tailWord_458703
  simp only [CollatzResearch.WordTrace]
  refine ⟨16730272857204846080524763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11153515238136564053683175 16730272857204846080524763)
  ·
    refine ⟨25095409285807269120787145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16730272857204846080524763 25095409285807269120787145)
    ·
      refine ⟨18821556964355451840590359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25095409285807269120787145 18821556964355451840590359)
      ·
        refine ⟨28232335446533177760885539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18821556964355451840590359 28232335446533177760885539)
        ·
          refine ⟨42348503169799766641328309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28232335446533177760885539 42348503169799766641328309)
          ·
            refine ⟨3970172172168728122624529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42348503169799766641328309 3970172172168728122624529)
            ·
              refine ⟨2977629129126546091968397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3970172172168728122624529 2977629129126546091968397)
              ·
                refine ⟨1116610923422454784488149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2977629129126546091968397 1116610923422454784488149)
                ·
                  refine ⟨26170568517713784011441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1116610923422454784488149 26170568517713784011441)
                  ·
                    rfl

theorem cell23_458703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 7].length) (baseStart_458703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458703 prefixEnd_458703 := by exact prefixLift 458703
  have htrace : WordTrace (prefixWord ++ tailWord_458703) baseStart_458703 baseEnd_458703 := by
    simpa [prefixWord, tailWord_458703, baseEnd_458703] using wordTrace_append hprefix tailTrace_458703
  have hstable : (prefixWord ++ tailWord_458703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458703).length < 2 ^ (prefixWord ++ tailWord_458703).sum := by decide
  have hdescent : baseEnd_458703 < baseStart_458703 := by decide
  rcases family_descends (prefixWord ++ tailWord_458703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458714 : List Nat := [3, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2]
def baseStart_458714 : Nat := 118140960795 + 458714 * 2 ^ 59
def prefixEnd_458714 : Nat := 4983230072969 + 3 ^ 40 * 458714 * 2
def baseEnd_458714 : Nat := 235540764946623513065419

theorem tailTrace_458714 : CollatzResearch.WordTrace tailWord_458714 prefixEnd_458714 235540764946623513065419 := by
  unfold tailWord_458714
  simp only [CollatzResearch.WordTrace]
  refine ⟨4182668515041248739793799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11153782706776663306116797 4182668515041248739793799)
  ·
    refine ⟨6274002772561873109690699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4182668515041248739793799 6274002772561873109690699)
    ·
      refine ⟨9411004158842809664536049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6274002772561873109690699 9411004158842809664536049)
      ·
        refine ⟨7058253119132107248402037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9411004158842809664536049 7058253119132107248402037)
        ·
          refine ⟨661711229918635054537691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7058253119132107248402037 661711229918635054537691)
          ·
            refine ⟨992566844877952581806537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661711229918635054537691 992566844877952581806537)
            ·
              refine ⟨744425133658464436354903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 992566844877952581806537 744425133658464436354903)
              ·
                refine ⟨1116637700487696654532355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 744425133658464436354903 1116637700487696654532355)
                ·
                  refine ⟨1674956550731544981798533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1116637700487696654532355 1674956550731544981798533)
                  ·
                    refine ⟨314054353262164684087225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1674956550731544981798533 314054353262164684087225)
                    ·
                      refine ⟨235540764946623513065419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 314054353262164684087225 235540764946623513065419)
                      ·
                        rfl

theorem cell23_458714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2].length) (baseStart_458714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458714 prefixEnd_458714 := by exact prefixLift 458714
  have htrace : WordTrace (prefixWord ++ tailWord_458714) baseStart_458714 baseEnd_458714 := by
    simpa [prefixWord, tailWord_458714, baseEnd_458714] using wordTrace_append hprefix tailTrace_458714
  have hstable : (prefixWord ++ tailWord_458714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458714).length < 2 ^ (prefixWord ++ tailWord_458714).sum := by decide
  have hdescent : baseEnd_458714 < baseStart_458714 := by decide
  rcases family_descends (prefixWord ++ tailWord_458714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458730 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 1, 5, 3]
def baseStart_458730 : Nat := 118140960795 + 458730 * 2 ^ 59
def prefixEnd_458730 : Nat := 4983230072969 + 3 ^ 40 * 458730 * 2
def baseEnd_458730 : Nat := 235548980637095450465345

theorem tailTrace_458730 : CollatzResearch.WordTrace tailWord_458730 prefixEnd_458730 235548980637095450465345 := by
  unfold tailWord_458730
  simp only [CollatzResearch.WordTrace]
  refine ⟨4182814407026757422939411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11154171752071353127838429 4182814407026757422939411)
  ·
    refine ⟨6274221610540136134409117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4182814407026757422939411 6274221610540136134409117)
    ·
      refine ⟨2352833103952551050403419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6274221610540136134409117 2352833103952551050403419)
      ·
        refine ⟨3529249655928826575605129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2352833103952551050403419 3529249655928826575605129)
        ·
          refine ⟨2646937241946619931703847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3529249655928826575605129 2646937241946619931703847)
          ·
            refine ⟨3970405862919929897555771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2646937241946619931703847 3970405862919929897555771)
            ·
              refine ⟨5955608794379894846333657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3970405862919929897555771 5955608794379894846333657)
              ·
                refine ⟨4466706595784921134750243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5955608794379894846333657 4466706595784921134750243)
                ·
                  refine ⟨6700059893677381702125365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4466706595784921134750243 6700059893677381702125365)
                  ·
                    refine ⟨628130615032254534574253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6700059893677381702125365 628130615032254534574253)
                    ·
                      refine ⟨235548980637095450465345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 628130615032254534574253 235548980637095450465345)
                      ·
                        rfl

theorem cell23_458730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_458730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458730 prefixEnd_458730 := by exact prefixLift 458730
  have htrace : WordTrace (prefixWord ++ tailWord_458730) baseStart_458730 baseEnd_458730 := by
    simpa [prefixWord, tailWord_458730, baseEnd_458730] using wordTrace_append hprefix tailTrace_458730
  have hstable : (prefixWord ++ tailWord_458730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458730).length < 2 ^ (prefixWord ++ tailWord_458730).sum := by decide
  have hdescent : baseEnd_458730 < baseStart_458730 := by decide
  rcases family_descends (prefixWord ++ tailWord_458730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458765 : List Nat := [1, 7, 1, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_458765 : Nat := 118140960795 + 458765 * 2 ^ 59
def prefixEnd_458765 : Nat := 4983230072969 + 3 ^ 40 * 458765 * 2
def baseEnd_458765 : Nat := 235566952460002813527685

theorem tailTrace_458765 : CollatzResearch.WordTrace tailWord_458765 prefixEnd_458765 235566952460002813527685 := by
  unfold tailWord_458765
  simp only [CollatzResearch.WordTrace]
  refine ⟨16732534182980230669281749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11155022788653487112854499 16732534182980230669281749)
  ·
    refine ⟨392168769913599156311291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 16732534182980230669281749 392168769913599156311291)
    ·
      refine ⟨588253154870398734466937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392168769913599156311291 588253154870398734466937)
      ·
        refine ⟨441189866152799050850203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 588253154870398734466937 441189866152799050850203)
        ·
          refine ⟨661784799229198576275305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441189866152799050850203 661784799229198576275305)
          ·
            refine ⟨496338599421898932206479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 661784799229198576275305 496338599421898932206479)
            ·
              refine ⟨744507899132848398309719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 496338599421898932206479 744507899132848398309719)
              ·
                refine ⟨1116761848699272597464579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 744507899132848398309719 1116761848699272597464579)
                ·
                  refine ⟨1675142773048908896196869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1116761848699272597464579 1675142773048908896196869)
                  ·
                    refine ⟨314089269946670418036913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1675142773048908896196869 314089269946670418036913)
                    ·
                      refine ⟨235566952460002813527685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 314089269946670418036913 235566952460002813527685)
                      ·
                        rfl

theorem cell23_458765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_458765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458765 prefixEnd_458765 := by exact prefixLift 458765
  have htrace : WordTrace (prefixWord ++ tailWord_458765) baseStart_458765 baseEnd_458765 := by
    simpa [prefixWord, tailWord_458765, baseEnd_458765] using wordTrace_append hprefix tailTrace_458765
  have hstable : (prefixWord ++ tailWord_458765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458765).length < 2 ^ (prefixWord ++ tailWord_458765).sum := by decide
  have hdescent : baseEnd_458765 < baseStart_458765 := by decide
  rcases family_descends (prefixWord ++ tailWord_458765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458810 : List Nat := [3, 1, 1, 1, 3, 1, 1, 6, 6]
def baseStart_458810 : Nat := 118140960795 + 458810 * 2 ^ 59
def prefixEnd_458810 : Nat := 4983230072969 + 3 ^ 40 * 458810 * 2
def baseEnd_458810 : Nat := 26176673232161681940553

theorem tailTrace_458810 : CollatzResearch.WordTrace tailWord_458810 prefixEnd_458810 26176673232161681940553 := by
  unfold tailWord_458810
  simp only [CollatzResearch.WordTrace]
  refine ⟨4183543866954300838667471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11156116978544802236446589 4183543866954300838667471)
  ·
    refine ⟨6275315800431451258001207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4183543866954300838667471 6275315800431451258001207)
    ·
      refine ⟨9412973700647176887001811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6275315800431451258001207 9412973700647176887001811)
      ·
        refine ⟨14119460550970765330502717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9412973700647176887001811 14119460550970765330502717)
        ·
          refine ⟨5294797706614036998938519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14119460550970765330502717 5294797706614036998938519)
          ·
            refine ⟨7942196559921055498407779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5294797706614036998938519 7942196559921055498407779)
            ·
              refine ⟨11913294839881583247611669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7942196559921055498407779 11913294839881583247611669)
              ·
                refine ⟨558435695619449214731797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11913294839881583247611669 558435695619449214731797)
                ·
                  refine ⟨26176673232161681940553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 558435695619449214731797 26176673232161681940553)
                  ·
                    rfl

theorem cell23_458810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 6].length) (baseStart_458810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458810 prefixEnd_458810 := by exact prefixLift 458810
  have htrace : WordTrace (prefixWord ++ tailWord_458810) baseStart_458810 baseEnd_458810 := by
    simpa [prefixWord, tailWord_458810, baseEnd_458810] using wordTrace_append hprefix tailTrace_458810
  have hstable : (prefixWord ++ tailWord_458810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458810).length < 2 ^ (prefixWord ++ tailWord_458810).sum := by decide
  have hdescent : baseEnd_458810 < baseStart_458810 := by decide
  rcases family_descends (prefixWord ++ tailWord_458810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458864 : List Nat := [2, 1, 1, 1, 5, 2, 2, 2, 2, 3, 2]
def baseStart_458864 : Nat := 118140960795 + 458864 * 2 ^ 59
def prefixEnd_458864 : Nat := 4983230072969 + 3 ^ 40 * 458864 * 2
def baseEnd_458864 : Nat := 235617787044797926189729

theorem tailTrace_458864 : CollatzResearch.WordTrace tailWord_458864 prefixEnd_458864 235617787044797926189729 := by
  unfold tailWord_458864
  simp only [CollatzResearch.WordTrace]
  refine ⟨8368072504810785288567823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11157430006414380384757097 8368072504810785288567823)
  ·
    refine ⟨12552108757216177932851735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8368072504810785288567823 12552108757216177932851735)
    ·
      refine ⟨18828163135824266899277603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12552108757216177932851735 18828163135824266899277603)
      ·
        refine ⟨28242244703736400348916405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18828163135824266899277603 28242244703736400348916405)
        ·
          refine ⟨2647710440975287532710913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28242244703736400348916405 2647710440975287532710913)
          ·
            refine ⟨1985782830731465649533185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2647710440975287532710913 1985782830731465649533185)
            ·
              refine ⟨1489337123048599237149889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1985782830731465649533185 1489337123048599237149889)
              ·
                refine ⟨1117002842286449427862417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1489337123048599237149889 1117002842286449427862417)
                ·
                  refine ⟨837752131714837070896813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1117002842286449427862417 837752131714837070896813)
                  ·
                    refine ⟨314157049393063901586305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 837752131714837070896813 314157049393063901586305)
                    ·
                      refine ⟨235617787044797926189729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 314157049393063901586305 235617787044797926189729)
                      ·
                        rfl

theorem cell23_458864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 2, 3, 2].length) (baseStart_458864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458864 prefixEnd_458864 := by exact prefixLift 458864
  have htrace : WordTrace (prefixWord ++ tailWord_458864) baseStart_458864 baseEnd_458864 := by
    simpa [prefixWord, tailWord_458864, baseEnd_458864] using wordTrace_append hprefix tailTrace_458864
  have hstable : (prefixWord ++ tailWord_458864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458864).length < 2 ^ (prefixWord ++ tailWord_458864).sum := by decide
  have hdescent : baseEnd_458864 < baseStart_458864 := by decide
  rcases family_descends (prefixWord ++ tailWord_458864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458871 : List Nat := [1, 1, 3, 1, 1, 6, 1, 4, 1, 1, 3]
def baseStart_458871 : Nat := 118140960795 + 458871 * 2 ^ 59
def prefixEnd_458871 : Nat := 4983230072969 + 3 ^ 40 * 458871 * 2
def baseEnd_458871 : Nat := 235621381409379398802197

theorem tailTrace_458871 : CollatzResearch.WordTrace tailWord_458871 prefixEnd_458871 235621381409379398802197 := by
  unfold tailWord_458871
  simp only [CollatzResearch.WordTrace]
  refine ⟨16736400320596210772640467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11157600213730807181760311 16736400320596210772640467)
  ·
    refine ⟨25104600480894316158960701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16736400320596210772640467 25104600480894316158960701)
    ·
      refine ⟨9414225180335368559610263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25104600480894316158960701 9414225180335368559610263)
      ·
        refine ⟨14121337770503052839415395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9414225180335368559610263 14121337770503052839415395)
        ·
          refine ⟨21182006655754579259123093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14121337770503052839415395 21182006655754579259123093)
          ·
            refine ⟨992906561988495902771395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21182006655754579259123093 992906561988495902771395)
            ·
              refine ⟨1489359842982743854157093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 992906561988495902771395 1489359842982743854157093)
              ·
                refine ⟨279254970559264472654455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1489359842982743854157093 279254970559264472654455)
                ·
                  refine ⟨418882455838896708981683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279254970559264472654455 418882455838896708981683)
                  ·
                    refine ⟨628323683758345063472525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 418882455838896708981683 628323683758345063472525)
                    ·
                      refine ⟨235621381409379398802197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 628323683758345063472525 235621381409379398802197)
                      ·
                        rfl

theorem cell23_458871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4, 1, 1, 3].length) (baseStart_458871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458871 prefixEnd_458871 := by exact prefixLift 458871
  have htrace : WordTrace (prefixWord ++ tailWord_458871) baseStart_458871 baseEnd_458871 := by
    simpa [prefixWord, tailWord_458871, baseEnd_458871] using wordTrace_append hprefix tailTrace_458871
  have hstable : (prefixWord ++ tailWord_458871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458871).length < 2 ^ (prefixWord ++ tailWord_458871).sum := by decide
  have hdescent : baseEnd_458871 < baseStart_458871 := by decide
  rcases family_descends (prefixWord ++ tailWord_458871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458877 : List Nat := [1, 4, 1, 1, 3, 2, 1, 2, 3, 1, 4]
def baseStart_458877 : Nat := 118140960795 + 458877 * 2 ^ 59
def prefixEnd_458877 : Nat := 4983230072969 + 3 ^ 40 * 458877 * 2
def baseEnd_458877 : Nat := 235624462293306375327169

theorem tailTrace_458877 : CollatzResearch.WordTrace tailWord_458877 prefixEnd_458877 235624462293306375327169 := by
  unfold tailWord_458877
  simp only [CollatzResearch.WordTrace]
  refine ⟨16736619158574473797358885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11157746105716315864905923 16736619158574473797358885)
  ·
    refine ⟨3138116092232713837004791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16736619158574473797358885 3138116092232713837004791)
    ·
      refine ⟨4707174138349070755507187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3138116092232713837004791 4707174138349070755507187)
      ·
        refine ⟨7060761207523606133260781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4707174138349070755507187 7060761207523606133260781)
        ·
          refine ⟨2647785452821352299972793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7060761207523606133260781 2647785452821352299972793)
          ·
            refine ⟨1985839089616014224979595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2647785452821352299972793 1985839089616014224979595)
            ·
              refine ⟨2978758634424021337469393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1985839089616014224979595 2978758634424021337469393)
              ·
                refine ⟨2234068975818016003102045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2978758634424021337469393 2234068975818016003102045)
                ·
                  refine ⟨837775865931756001163267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2234068975818016003102045 837775865931756001163267)
                  ·
                    refine ⟨1256663798897634001744901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 837775865931756001163267 1256663798897634001744901)
                    ·
                      refine ⟨235624462293306375327169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1256663798897634001744901 235624462293306375327169)
                      ·
                        rfl

theorem cell23_458877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_458877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458877 prefixEnd_458877 := by exact prefixLift 458877
  have htrace : WordTrace (prefixWord ++ tailWord_458877) baseStart_458877 baseEnd_458877 := by
    simpa [prefixWord, tailWord_458877, baseEnd_458877] using wordTrace_append hprefix tailTrace_458877
  have hstable : (prefixWord ++ tailWord_458877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458877).length < 2 ^ (prefixWord ++ tailWord_458877).sum := by decide
  have hdescent : baseEnd_458877 < baseStart_458877 := by decide
  rcases family_descends (prefixWord ++ tailWord_458877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458880 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 5]
def baseStart_458880 : Nat := 118140960795 + 458880 * 2 ^ 59
def prefixEnd_458880 : Nat := 4983230072969 + 3 ^ 40 * 458880 * 2
def baseEnd_458880 : Nat := 235626002735269863589655

theorem tailTrace_458880 : CollatzResearch.WordTrace tailWord_458880 prefixEnd_458880 235626002735269863589655 := by
  unfold tailWord_458880
  simp only [CollatzResearch.WordTrace]
  refine ⟨8368364288781802654859047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11157819051709070206478729 8368364288781802654859047)
  ·
    refine ⟨12552546433172703982288571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8368364288781802654859047 12552546433172703982288571)
    ·
      refine ⟨18828819649759055973432857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12552546433172703982288571 18828819649759055973432857)
      ·
        refine ⟨14121614737319291980074643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18828819649759055973432857 14121614737319291980074643)
        ·
          refine ⟨21182422105978937970111965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14121614737319291980074643 21182422105978937970111965)
          ·
            refine ⟨7943408289742101738791987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21182422105978937970111965 7943408289742101738791987)
            ·
              refine ⟨11915112434613152608187981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7943408289742101738791987 11915112434613152608187981)
              ·
                refine ⟨4468167162979932228070493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11915112434613152608187981 4468167162979932228070493)
                ·
                  refine ⟨1675562686117474585526435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4468167162979932228070493 1675562686117474585526435)
                  ·
                    refine ⟨2513344029176211878289653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1675562686117474585526435 2513344029176211878289653)
                    ·
                      refine ⟨235626002735269863589655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2513344029176211878289653 235626002735269863589655)
                      ·
                        rfl

theorem cell23_458880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_458880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458880 prefixEnd_458880 := by exact prefixLift 458880
  have htrace : WordTrace (prefixWord ++ tailWord_458880) baseStart_458880 baseEnd_458880 := by
    simpa [prefixWord, tailWord_458880, baseEnd_458880] using wordTrace_append hprefix tailTrace_458880
  have hstable : (prefixWord ++ tailWord_458880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458880).length < 2 ^ (prefixWord ++ tailWord_458880).sum := by decide
  have hdescent : baseEnd_458880 < baseStart_458880 := by decide
  rcases family_descends (prefixWord ++ tailWord_458880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458911 : List Nat := [1, 1, 2, 6, 1, 1, 4, 1, 1, 1, 4]
def baseStart_458911 : Nat := 118140960795 + 458911 * 2 ^ 59
def prefixEnd_458911 : Nat := 4983230072969 + 3 ^ 40 * 458911 * 2
def baseEnd_458911 : Nat := 235641920635559242302013

theorem tailTrace_458911 : CollatzResearch.WordTrace tailWord_458911 prefixEnd_458911 235641920635559242302013 := by
  unfold tailWord_458911
  simp only [CollatzResearch.WordTrace]
  refine ⟨16737859240451297604096587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11158572826967531736064391 16737859240451297604096587)
  ·
    refine ⟨25106788860676946406144881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16737859240451297604096587 25106788860676946406144881)
    ·
      refine ⟨18830091645507709804608661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25106788860676946406144881 18830091645507709804608661)
      ·
        refine ⟨882660545883173897091031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18830091645507709804608661 882660545883173897091031)
        ·
          refine ⟨1323990818824760845636547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882660545883173897091031 1323990818824760845636547)
          ·
            refine ⟨1985986228237141268454821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323990818824760845636547 1985986228237141268454821)
            ·
              refine ⟨372372417794463987835279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1985986228237141268454821 372372417794463987835279)
              ·
                refine ⟨558558626691695981752919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 372372417794463987835279 558558626691695981752919)
                ·
                  refine ⟨837837940037543972629379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 558558626691695981752919 837837940037543972629379)
                  ·
                    refine ⟨1256756910056315958944069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 837837940037543972629379 1256756910056315958944069)
                    ·
                      refine ⟨235641920635559242302013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1256756910056315958944069 235641920635559242302013)
                      ·
                        rfl

theorem cell23_458911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_458911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458911 prefixEnd_458911 := by exact prefixLift 458911
  have htrace : WordTrace (prefixWord ++ tailWord_458911) baseStart_458911 baseEnd_458911 := by
    simpa [prefixWord, tailWord_458911, baseEnd_458911] using wordTrace_append hprefix tailTrace_458911
  have hstable : (prefixWord ++ tailWord_458911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458911).length < 2 ^ (prefixWord ++ tailWord_458911).sum := by decide
  have hdescent : baseEnd_458911 < baseStart_458911 := by decide
  rcases family_descends (prefixWord ++ tailWord_458911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458944 : List Nat := [2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 3]
def baseStart_458944 : Nat := 118140960795 + 458944 * 2 ^ 59
def prefixEnd_458944 : Nat := 4983230072969 + 3 ^ 40 * 458944 * 2
def baseEnd_458944 : Nat := 235658865497157613189361

theorem tailTrace_458944 : CollatzResearch.WordTrace tailWord_458944 prefixEnd_458944 235658865497157613189361 := by
  unfold tailWord_458944
  simp only [CollatzResearch.WordTrace]
  refine ⟨8369531424665872120023943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11159375232887829493365257 8369531424665872120023943)
  ·
    refine ⟨12554297136998808180035915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8369531424665872120023943 12554297136998808180035915)
    ·
      refine ⟨18831445705498212270053873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12554297136998808180035915 18831445705498212270053873)
      ·
        refine ⟨14123584279123659202540405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18831445705498212270053873 14123584279123659202540405)
        ·
          refine ⟨1324086026167843050238163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14123584279123659202540405 1324086026167843050238163)
          ·
            refine ⟨1986129039251764575357245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1324086026167843050238163 1986129039251764575357245)
            ·
              refine ⟨744798389719411715758967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1986129039251764575357245 744798389719411715758967)
              ·
                refine ⟨1117197584579117573638451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 744798389719411715758967 1117197584579117573638451)
                ·
                  refine ⟨1675796376868676360457677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1117197584579117573638451 1675796376868676360457677)
                  ·
                    refine ⟨628423641325753635171629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1675796376868676360457677 628423641325753635171629)
                    ·
                      refine ⟨235658865497157613189361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 628423641325753635171629 235658865497157613189361)
                      ·
                        rfl

theorem cell23_458944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 3].length) (baseStart_458944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458944 prefixEnd_458944 := by exact prefixLift 458944
  have htrace : WordTrace (prefixWord ++ tailWord_458944) baseStart_458944 baseEnd_458944 := by
    simpa [prefixWord, tailWord_458944, baseEnd_458944] using wordTrace_append hprefix tailTrace_458944
  have hstable : (prefixWord ++ tailWord_458944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458944).length < 2 ^ (prefixWord ++ tailWord_458944).sum := by decide
  have hdescent : baseEnd_458944 < baseStart_458944 := by decide
  rcases family_descends (prefixWord ++ tailWord_458944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458987 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 2, 4, 3]
def baseStart_458987 : Nat := 118140960795 + 458987 * 2 ^ 59
def prefixEnd_458987 : Nat := 4983230072969 + 3 ^ 40 * 458987 * 2
def baseEnd_458987 : Nat := 235680945165300944951663

theorem tailTrace_458987 : CollatzResearch.WordTrace tailWord_458987 prefixEnd_458987 235680945165300944951663 := by
  unfold tailWord_458987
  simp only [CollatzResearch.WordTrace]
  refine ⟨16740631188175962583863215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11160420792117308389242143 16740631188175962583863215)
  ·
    refine ⟨25110946782263943875794823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16740631188175962583863215 25110946782263943875794823)
    ·
      refine ⟨37666420173395915813692235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25110946782263943875794823 37666420173395915813692235)
      ·
        refine ⟨56499630260093873720538353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37666420173395915813692235 56499630260093873720538353)
        ·
          refine ⟨42374722695070405290403765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56499630260093873720538353 42374722695070405290403765)
          ·
            refine ⟨3972630252662850495975353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42374722695070405290403765 3972630252662850495975353)
            ·
              refine ⟨2979472689497137871981515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3972630252662850495975353 2979472689497137871981515)
              ·
                refine ⟨4469209034245706807972273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2979472689497137871981515 4469209034245706807972273)
                ·
                  refine ⟨3351906775684280105979205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4469209034245706807972273 3351906775684280105979205)
                  ·
                    refine ⟨628482520440802519871101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3351906775684280105979205 628482520440802519871101)
                    ·
                      refine ⟨235680945165300944951663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 628482520440802519871101 235680945165300944951663)
                      ·
                        rfl

theorem cell23_458987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4, 3].length) (baseStart_458987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_458987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_458987 prefixEnd_458987 := by exact prefixLift 458987
  have htrace : WordTrace (prefixWord ++ tailWord_458987) baseStart_458987 baseEnd_458987 := by
    simpa [prefixWord, tailWord_458987, baseEnd_458987] using wordTrace_append hprefix tailTrace_458987
  have hstable : (prefixWord ++ tailWord_458987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458987).length < 2 ^ (prefixWord ++ tailWord_458987).sum := by decide
  have hdescent : baseEnd_458987 < baseStart_458987 := by decide
  rcases family_descends (prefixWord ++ tailWord_458987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459041 : List Nat := [1, 2, 3, 2, 1, 1, 6, 2, 5]
def baseStart_459041 : Nat := 118140960795 + 459041 * 2 ^ 59
def prefixEnd_459041 : Nat := 4983230072969 + 3 ^ 40 * 459041 * 2
def baseEnd_459041 : Nat := 26189852568960414852935

theorem tailTrace_459041 : CollatzResearch.WordTrace tailWord_459041 prefixEnd_459041 26189852568960414852935 := by
  unfold tailWord_459041
  simp only [CollatzResearch.WordTrace]
  refine ⟨16742600729980329806328977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11161733819986886537552651 16742600729980329806328977)
  ·
    refine ⟨12556950547485247354746733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16742600729980329806328977 12556950547485247354746733)
    ·
      refine ⟨4708856455306967758030025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12556950547485247354746733 4708856455306967758030025)
      ·
        refine ⟨3531642341480225818522519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4708856455306967758030025 3531642341480225818522519)
        ·
          refine ⟨5297463512220338727783779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3531642341480225818522519 5297463512220338727783779)
          ·
            refine ⟨7946195268330508091675669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5297463512220338727783779 7946195268330508091675669)
            ·
              refine ⟨372477903202992566797297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7946195268330508091675669 372477903202992566797297)
              ·
                refine ⟨279358427402244425097973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372477903202992566797297 279358427402244425097973)
                ·
                  refine ⟨26189852568960414852935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 279358427402244425097973 26189852568960414852935)
                  ·
                    rfl

theorem cell23_459041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2, 5].length) (baseStart_459041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459041 prefixEnd_459041 := by exact prefixLift 459041
  have htrace : WordTrace (prefixWord ++ tailWord_459041) baseStart_459041 baseEnd_459041 := by
    simpa [prefixWord, tailWord_459041, baseEnd_459041] using wordTrace_append hprefix tailTrace_459041
  have hstable : (prefixWord ++ tailWord_459041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459041).length < 2 ^ (prefixWord ++ tailWord_459041).sum := by decide
  have hdescent : baseEnd_459041 < baseStart_459041 := by decide
  rcases family_descends (prefixWord ++ tailWord_459041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459084 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 5, 4]
def baseStart_459084 : Nat := 118140960795 + 459084 * 2 ^ 59
def prefixEnd_459084 : Nat := 4983230072969 + 3 ^ 40 * 459084 * 2
def baseEnd_459084 : Nat := 78576917596262355146239

theorem tailTrace_459084 : CollatzResearch.WordTrace tailWord_459084 prefixEnd_459084 78576917596262355146239 := by
  unfold tailWord_459084
  simp only [CollatzResearch.WordTrace]
  refine ⟨8372084534412274075072153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11162779379216365433429537 8372084534412274075072153)
  ·
    refine ⟨6279063400809205556304115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8372084534412274075072153 6279063400809205556304115)
    ·
      refine ⟨9418595101213808334456173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6279063400809205556304115 9418595101213808334456173)
      ·
        refine ⟨3531973162955178125421065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9418595101213808334456173 3531973162955178125421065)
        ·
          refine ⟨2648979872216383594065799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3531973162955178125421065 2648979872216383594065799)
          ·
            refine ⟨3973469808324575391098699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2648979872216383594065799 3973469808324575391098699)
            ·
              refine ⟨5960204712486863086648049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3973469808324575391098699 5960204712486863086648049)
              ·
                refine ⟨4470153534365147314986037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5960204712486863086648049 4470153534365147314986037)
                ·
                  refine ⟨419076893846732560779941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4470153534365147314986037 419076893846732560779941)
                  ·
                    refine ⟨78576917596262355146239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 419076893846732560779941 78576917596262355146239)
                    ·
                      rfl

theorem cell23_459084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 5, 4].length) (baseStart_459084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459084 prefixEnd_459084 := by exact prefixLift 459084
  have htrace : WordTrace (prefixWord ++ tailWord_459084) baseStart_459084 baseEnd_459084 := by
    simpa [prefixWord, tailWord_459084, baseEnd_459084] using wordTrace_append hprefix tailTrace_459084
  have hstable : (prefixWord ++ tailWord_459084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459084).length < 2 ^ (prefixWord ++ tailWord_459084).sum := by decide
  have hdescent : baseEnd_459084 < baseStart_459084 := by decide
  rcases family_descends (prefixWord ++ tailWord_459084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459165 : List Nat := [1, 4, 2, 1, 5, 1, 2, 1, 6]
def baseStart_459165 : Nat := 118140960795 + 459165 * 2 ^ 59
def prefixEnd_459165 : Nat := 4983230072969 + 3 ^ 40 * 459165 * 2
def baseEnd_459165 : Nat := 26196927191311249836205

theorem tailTrace_459165 : CollatzResearch.WordTrace tailWord_459165 prefixEnd_459165 26196927191311249836205 := by
  unfold tailWord_459165
  simp only [CollatzResearch.WordTrace]
  refine ⟨16747123381531098983842949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11164748921020732655895299 16747123381531098983842949)
  ·
    refine ⟨3140085634037081059470553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16747123381531098983842949 3140085634037081059470553)
    ·
      refine ⟨2355064225527810794602915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3140085634037081059470553 2355064225527810794602915)
      ·
        refine ⟨3532596338291716191904373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2355064225527810794602915 3532596338291716191904373)
        ·
          refine ⟨331180906714848392991035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3532596338291716191904373 331180906714848392991035)
          ·
            refine ⟨496771360072272589486553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331180906714848392991035 496771360072272589486553)
            ·
              refine ⟨372578520054204442114915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 496771360072272589486553 372578520054204442114915)
              ·
                refine ⟨558867780081306663172373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 372578520054204442114915 558867780081306663172373)
                ·
                  refine ⟨26196927191311249836205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 558867780081306663172373 26196927191311249836205)
                  ·
                    rfl

theorem cell23_459165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 6].length) (baseStart_459165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459165 prefixEnd_459165 := by exact prefixLift 459165
  have htrace : WordTrace (prefixWord ++ tailWord_459165) baseStart_459165 baseEnd_459165 := by
    simpa [prefixWord, tailWord_459165, baseEnd_459165] using wordTrace_append hprefix tailTrace_459165
  have hstable : (prefixWord ++ tailWord_459165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459165).length < 2 ^ (prefixWord ++ tailWord_459165).sum := by decide
  have hdescent : baseEnd_459165 < baseStart_459165 := by decide
  rcases family_descends (prefixWord ++ tailWord_459165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459204 : List Nat := [2, 3, 3, 2, 13]
def baseStart_459204 : Nat := 118140960795 + 459204 * 2 ^ 59
def prefixEnd_459204 : Nat := 4983230072969 + 3 ^ 40 * 459204 * 2
def baseEnd_459204 : Nat := 323446324372190117885

theorem tailTrace_459204 : CollatzResearch.WordTrace tailWord_459204 prefixEnd_459204 323446324372190117885 := by
  unfold tailWord_459204
  simp only [CollatzResearch.WordTrace]
  refine ⟨8374272914194904322256333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11165697218926539096341777 8374272914194904322256333)
  ·
    refine ⟨3140352342823089120846125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8374272914194904322256333 3140352342823089120846125)
    ·
      refine ⟨1177632128558658420317297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3140352342823089120846125 1177632128558658420317297)
      ·
        refine ⟨883224096418993815237973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1177632128558658420317297 883224096418993815237973)
        ·
          refine ⟨323446324372190117885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 883224096418993815237973 323446324372190117885)
          ·
            rfl

theorem cell23_459204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 13].length) (baseStart_459204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459204 prefixEnd_459204 := by exact prefixLift 459204
  have htrace : WordTrace (prefixWord ++ tailWord_459204) baseStart_459204 baseEnd_459204 := by
    simpa [prefixWord, tailWord_459204, baseEnd_459204] using wordTrace_append hprefix tailTrace_459204
  have hstable : (prefixWord ++ tailWord_459204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459204).length < 2 ^ (prefixWord ++ tailWord_459204).sum := by decide
  have hdescent : baseEnd_459204 < baseStart_459204 := by decide
  rcases family_descends (prefixWord ++ tailWord_459204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459208 : List Nat := [2, 1, 3, 1, 3, 3, 2, 2, 2, 4]
def baseStart_459208 : Nat := 118140960795 + 459208 * 2 ^ 59
def prefixEnd_459208 : Nat := 4983230072969 + 3 ^ 40 * 459208 * 2
def baseEnd_459208 : Nat := 78598141463314860096049

theorem tailTrace_459208 : CollatzResearch.WordTrace tailWord_459208 prefixEnd_459208 78598141463314860096049 := by
  unfold tailWord_459208
  simp only [CollatzResearch.WordTrace]
  refine ⟨8374345860187658663829139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11165794480250211551772185 8374345860187658663829139)
  ·
    refine ⟨12561518790281487995743709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8374345860187658663829139 12561518790281487995743709)
    ·
      refine ⟨4710569546355557998403891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12561518790281487995743709 4710569546355557998403891)
      ·
        refine ⟨7065854319533336997605837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4710569546355557998403891 7065854319533336997605837)
        ·
          refine ⟨2649695369825001374102189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7065854319533336997605837 2649695369825001374102189)
          ·
            refine ⟨993635763684375515288321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2649695369825001374102189 993635763684375515288321)
            ·
              refine ⟨745226822763281636466241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 993635763684375515288321 745226822763281636466241)
              ·
                refine ⟨558920117072461227349681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 745226822763281636466241 558920117072461227349681)
                ·
                  refine ⟨419190087804345920512261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 558920117072461227349681 419190087804345920512261)
                  ·
                    refine ⟨78598141463314860096049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 419190087804345920512261 78598141463314860096049)
                    ·
                      rfl

theorem cell23_459208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_459208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459208 prefixEnd_459208 := by exact prefixLift 459208
  have htrace : WordTrace (prefixWord ++ tailWord_459208) baseStart_459208 baseEnd_459208 := by
    simpa [prefixWord, tailWord_459208, baseEnd_459208] using wordTrace_append hprefix tailTrace_459208
  have hstable : (prefixWord ++ tailWord_459208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459208).length < 2 ^ (prefixWord ++ tailWord_459208).sum := by decide
  have hdescent : baseEnd_459208 < baseStart_459208 := by decide
  rcases family_descends (prefixWord ++ tailWord_459208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459221 : List Nat := [1, 3, 2, 3, 1, 4, 1, 8]
def baseStart_459221 : Nat := 118140960795 + 459221 * 2 ^ 59
def prefixEnd_459221 : Nat := 4983230072969 + 3 ^ 40 * 459221 * 2
def baseEnd_459221 : Nat := 8733374060683445534281

theorem tailTrace_459221 : CollatzResearch.WordTrace tailWord_459221 prefixEnd_459221 8733374060683445534281 := by
  unfold tailWord_459221
  simp only [CollatzResearch.WordTrace]
  refine ⟨16749165869328220547881517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11166110579552147031921011 16749165869328220547881517)
  ·
    refine ⟨6280937200998082705455569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16749165869328220547881517 6280937200998082705455569)
    ·
      refine ⟨4710702900748562029091677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6280937200998082705455569 4710702900748562029091677)
      ·
        refine ⟨1766513587780710760909379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4710702900748562029091677 1766513587780710760909379)
        ·
          refine ⟨2649770381671066141364069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1766513587780710760909379 2649770381671066141364069)
          ·
            refine ⟨496831946563324901505763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2649770381671066141364069 496831946563324901505763)
            ·
              refine ⟨745247919844987352258645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 496831946563324901505763 745247919844987352258645)
              ·
                refine ⟨8733374060683445534281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 745247919844987352258645 8733374060683445534281)
                ·
                  rfl

theorem cell23_459221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 8].length) (baseStart_459221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459221 prefixEnd_459221 := by exact prefixLift 459221
  have htrace : WordTrace (prefixWord ++ tailWord_459221) baseStart_459221 baseEnd_459221 := by
    simpa [prefixWord, tailWord_459221, baseEnd_459221] using wordTrace_append hprefix tailTrace_459221
  have hstable : (prefixWord ++ tailWord_459221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459221).length < 2 ^ (prefixWord ++ tailWord_459221).sum := by decide
  have hdescent : baseEnd_459221 < baseStart_459221 := by decide
  rcases family_descends (prefixWord ++ tailWord_459221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459231 : List Nat := [1, 1, 2, 3, 3, 2, 1, 3, 1, 3, 3]
def baseStart_459231 : Nat := 118140960795 + 459231 * 2 ^ 59
def prefixEnd_459231 : Nat := 4983230072969 + 3 ^ 40 * 459231 * 2
def baseEnd_459231 : Nat := 235806234444997990300541

theorem tailTrace_459231 : CollatzResearch.WordTrace tailWord_459231 prefixEnd_459231 235806234444997990300541 := by
  unfold tailWord_459231
  simp only [CollatzResearch.WordTrace]
  refine ⟨16749530599291992255745547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11166353732861328170497031 16749530599291992255745547)
  ·
    refine ⟨25124295898937988383618321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16749530599291992255745547 25124295898937988383618321)
    ·
      refine ⟨18843221924203491287713741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25124295898937988383618321 18843221924203491287713741)
      ·
        refine ⟨7066208221576309232892653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18843221924203491287713741 7066208221576309232892653)
        ·
          refine ⟨2649828083091115962334745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7066208221576309232892653 2649828083091115962334745)
          ·
            refine ⟨1987371062318336971751059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2649828083091115962334745 1987371062318336971751059)
            ·
              refine ⟨2981056593477505457626589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1987371062318336971751059 2981056593477505457626589)
              ·
                refine ⟨1117896222554064546609971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2981056593477505457626589 1117896222554064546609971)
                ·
                  refine ⟨1676844333831096819914957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1117896222554064546609971 1676844333831096819914957)
                  ·
                    refine ⟨628816625186661307468109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1676844333831096819914957 628816625186661307468109)
                    ·
                      refine ⟨235806234444997990300541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 628816625186661307468109 235806234444997990300541)
                      ·
                        rfl

theorem cell23_459231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_459231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459231 prefixEnd_459231 := by exact prefixLift 459231
  have htrace : WordTrace (prefixWord ++ tailWord_459231) baseStart_459231 baseEnd_459231 := by
    simpa [prefixWord, tailWord_459231, baseEnd_459231] using wordTrace_append hprefix tailTrace_459231
  have hstable : (prefixWord ++ tailWord_459231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459231).length < 2 ^ (prefixWord ++ tailWord_459231).sum := by decide
  have hdescent : baseEnd_459231 < baseStart_459231 := by decide
  rcases family_descends (prefixWord ++ tailWord_459231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459244 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 5]
def baseStart_459244 : Nat := 118140960795 + 459244 * 2 ^ 59
def prefixEnd_459244 : Nat := 4983230072969 + 3 ^ 40 * 459244 * 2
def baseEnd_459244 : Nat := 235812909693506439437981

theorem tailTrace_459244 : CollatzResearch.WordTrace tailWord_459244 prefixEnd_459244 235812909693506439437981 := by
  unfold tailWord_459244
  simp only [CollatzResearch.WordTrace]
  refine ⟨8375002374122447737984393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11166669832163263650645857 8375002374122447737984393)
  ·
    refine ⟨6281251780591835803488295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8375002374122447737984393 6281251780591835803488295)
    ·
      refine ⟨9421877670887753705232443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6281251780591835803488295 9421877670887753705232443)
      ·
        refine ⟨14132816506331630557848665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9421877670887753705232443 14132816506331630557848665)
        ·
          refine ⟨10599612379748722918386499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14132816506331630557848665 10599612379748722918386499)
          ·
            refine ⟨15899418569623084377579749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10599612379748722918386499 15899418569623084377579749)
            ·
              refine ⟨2981140981804328320796203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15899418569623084377579749 2981140981804328320796203)
              ·
                refine ⟨4471711472706492481194305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2981140981804328320796203 4471711472706492481194305)
                ·
                  refine ⟨3353783604529869360895729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4471711472706492481194305 3353783604529869360895729)
                  ·
                    refine ⟨2515337703397402020671797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3353783604529869360895729 2515337703397402020671797)
                    ·
                      refine ⟨235812909693506439437981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2515337703397402020671797 235812909693506439437981)
                      ·
                        rfl

theorem cell23_459244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_459244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459244 prefixEnd_459244 := by exact prefixLift 459244
  have htrace : WordTrace (prefixWord ++ tailWord_459244) baseStart_459244 baseEnd_459244 := by
    simpa [prefixWord, tailWord_459244, baseEnd_459244] using wordTrace_append hprefix tailTrace_459244
  have hstable : (prefixWord ++ tailWord_459244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459244).length < 2 ^ (prefixWord ++ tailWord_459244).sum := by decide
  have hdescent : baseEnd_459244 < baseStart_459244 := by decide
  rcases family_descends (prefixWord ++ tailWord_459244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459265 : List Nat := [1, 2, 4, 1, 3, 1, 3, 2, 2, 1, 3]
def baseStart_459265 : Nat := 118140960795 + 459265 * 2 ^ 59
def prefixEnd_459265 : Nat := 4983230072969 + 3 ^ 40 * 459265 * 2
def baseEnd_459265 : Nat := 235823692787250857275385

theorem tailTrace_459265 : CollatzResearch.WordTrace tailWord_459265 prefixEnd_459265 235823692787250857275385 := by
  unfold tailWord_459265
  simp only [CollatzResearch.WordTrace]
  refine ⟨16750770681168816062483249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11167180454112544041655499 16750770681168816062483249)
  ·
    refine ⟨12563078010876612046862437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16750770681168816062483249 12563078010876612046862437)
    ·
      refine ⟨2355577127039364758786707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12563078010876612046862437 2355577127039364758786707)
      ·
        refine ⟨3533365690559047138180061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2355577127039364758786707 3533365690559047138180061)
        ·
          refine ⟨1325012133959642676817523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3533365690559047138180061 1325012133959642676817523)
          ·
            refine ⟨1987518200939464015226285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1325012133959642676817523 1987518200939464015226285)
            ·
              refine ⟨745319325352299005709857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1987518200939464015226285 745319325352299005709857)
              ·
                refine ⟨558989494014224254282393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 745319325352299005709857 558989494014224254282393)
                ·
                  refine ⟨419242120510668190711795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 558989494014224254282393 419242120510668190711795)
                  ·
                    refine ⟨628863180766002286067693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 419242120510668190711795 628863180766002286067693)
                    ·
                      refine ⟨235823692787250857275385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 628863180766002286067693 235823692787250857275385)
                      ·
                        rfl

theorem cell23_459265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_459265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459265 prefixEnd_459265 := by exact prefixLift 459265
  have htrace : WordTrace (prefixWord ++ tailWord_459265) baseStart_459265 baseEnd_459265 := by
    simpa [prefixWord, tailWord_459265, baseEnd_459265] using wordTrace_append hprefix tailTrace_459265
  have hstable : (prefixWord ++ tailWord_459265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459265).length < 2 ^ (prefixWord ++ tailWord_459265).sum := by decide
  have hdescent : baseEnd_459265 < baseStart_459265 := by decide
  rcases family_descends (prefixWord ++ tailWord_459265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459371 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 7, 4]
def baseStart_459371 : Nat := 118140960795 + 459371 * 2 ^ 59
def prefixEnd_459371 : Nat := 4983230072969 + 3 ^ 40 * 459371 * 2
def baseEnd_459371 : Nat := 78626040578875814183299

theorem tailTrace_459371 : CollatzResearch.WordTrace tailWord_459371 prefixEnd_459371 78626040578875814183299 := by
  unfold tailWord_459371
  simp only [CollatzResearch.WordTrace]
  refine ⟨16754636818784796165841967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11169757879189864110561311 16754636818784796165841967)
  ·
    refine ⟨25131955228177194248762951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16754636818784796165841967 25131955228177194248762951)
    ·
      refine ⟨37697932842265791373144427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25131955228177194248762951 37697932842265791373144427)
      ·
        refine ⟨56546899263398687059716641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37697932842265791373144427 56546899263398687059716641)
        ·
          refine ⟨42410174447549015294787481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56546899263398687059716641 42410174447549015294787481)
          ·
            refine ⟨31807630835661761471090611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42410174447549015294787481 31807630835661761471090611)
            ·
              refine ⟨47711446253492642206635917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31807630835661761471090611 47711446253492642206635917)
              ·
                refine ⟨17891792345059740827488469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47711446253492642206635917 17891792345059740827488469)
                ·
                  refine ⟨419338883087337675644261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17891792345059740827488469 419338883087337675644261)
                  ·
                    refine ⟨78626040578875814183299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 419338883087337675644261 78626040578875814183299)
                    ·
                      rfl

theorem cell23_459371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7, 4].length) (baseStart_459371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459371 prefixEnd_459371 := by exact prefixLift 459371
  have htrace : WordTrace (prefixWord ++ tailWord_459371) baseStart_459371 baseEnd_459371 := by
    simpa [prefixWord, tailWord_459371, baseEnd_459371] using wordTrace_append hprefix tailTrace_459371
  have hstable : (prefixWord ++ tailWord_459371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459371).length < 2 ^ (prefixWord ++ tailWord_459371).sum := by decide
  have hdescent : baseEnd_459371 < baseStart_459371 := by decide
  rcases family_descends (prefixWord ++ tailWord_459371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459411 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 2, 5, 3]
def baseStart_459411 : Nat := 118140960795 + 459411 * 2 ^ 59
def prefixEnd_459411 : Nat := 4983230072969 + 3 ^ 40 * 459411 * 2
def baseEnd_459411 : Nat := 235898660962807286049713

theorem tailTrace_459411 : CollatzResearch.WordTrace tailWord_459411 prefixEnd_459411 235898660962807286049713 := by
  unfold tailWord_459411
  simp only [CollatzResearch.WordTrace]
  refine ⟨16756095738639882997298087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11170730492426588664865391 16756095738639882997298087)
  ·
    refine ⟨25134143607959824495947131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16756095738639882997298087 25134143607959824495947131)
    ·
      refine ⟨37701215411939736743920697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25134143607959824495947131 37701215411939736743920697)
      ·
        refine ⟨28275911558954802557940523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37701215411939736743920697 28275911558954802557940523)
        ·
          refine ⟨42413867338432203836910785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28275911558954802557940523 42413867338432203836910785)
          ·
            refine ⟨31810400503824152877683089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42413867338432203836910785 31810400503824152877683089)
            ·
              refine ⟨23857800377868114658262317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31810400503824152877683089 23857800377868114658262317)
              ·
                refine ⟨8946675141700542996848369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23857800377868114658262317 8946675141700542996848369)
                ·
                  refine ⟨6710006356275407247636277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8946675141700542996848369 6710006356275407247636277)
                  ·
                    refine ⟨629063095900819429465901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6710006356275407247636277 629063095900819429465901)
                    ·
                      refine ⟨235898660962807286049713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 629063095900819429465901 235898660962807286049713)
                      ·
                        rfl

theorem cell23_459411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5, 3].length) (baseStart_459411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459411 prefixEnd_459411 := by exact prefixLift 459411
  have htrace : WordTrace (prefixWord ++ tailWord_459411) baseStart_459411 baseEnd_459411 := by
    simpa [prefixWord, tailWord_459411, baseEnd_459411] using wordTrace_append hprefix tailTrace_459411
  have hstable : (prefixWord ++ tailWord_459411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459411).length < 2 ^ (prefixWord ++ tailWord_459411).sum := by decide
  have hdescent : baseEnd_459411 < baseStart_459411 := by decide
  rcases family_descends (prefixWord ++ tailWord_459411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459412 : List Nat := [2, 4, 2, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_459412 : Nat := 118140960795 + 459412 * 2 ^ 59
def prefixEnd_459412 : Nat := 4983230072969 + 3 ^ 40 * 459412 * 2
def baseEnd_459412 : Nat := 235899174443461782137209

theorem tailTrace_459412 : CollatzResearch.WordTrace tailWord_459412 prefixEnd_459412 235899174443461782137209 := by
  unfold tailWord_459412
  simp only [CollatzResearch.WordTrace]
  refine ⟨8378066105818130084042245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11170754807757506778722993 8378066105818130084042245)
  ·
    refine ⟨1570887394840899390757921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8378066105818130084042245 1570887394840899390757921)
    ·
      refine ⟨1178165546130674543068441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1570887394840899390757921 1178165546130674543068441)
      ·
        refine ⟨883624159598005907301331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1178165546130674543068441 883624159598005907301331)
        ·
          refine ⟨1325436239397008860951997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 883624159598005907301331 1325436239397008860951997)
          ·
            refine ⟨497038589773878322856999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1325436239397008860951997 497038589773878322856999)
            ·
              refine ⟨745557884660817484285499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497038589773878322856999 745557884660817484285499)
              ·
                refine ⟨1118336826991226226428249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 745557884660817484285499 1118336826991226226428249)
                ·
                  refine ⟨838752620243419669821187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1118336826991226226428249 838752620243419669821187)
                  ·
                    refine ⟨1258128930365129504731781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 838752620243419669821187 1258128930365129504731781)
                    ·
                      refine ⟨235899174443461782137209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1258128930365129504731781 235899174443461782137209)
                      ·
                        rfl

theorem cell23_459412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_459412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459412 prefixEnd_459412 := by exact prefixLift 459412
  have htrace : WordTrace (prefixWord ++ tailWord_459412) baseStart_459412 baseEnd_459412 := by
    simpa [prefixWord, tailWord_459412, baseEnd_459412] using wordTrace_append hprefix tailTrace_459412
  have hstable : (prefixWord ++ tailWord_459412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459412).length < 2 ^ (prefixWord ++ tailWord_459412).sum := by decide
  have hdescent : baseEnd_459412 < baseStart_459412 := by decide
  rcases family_descends (prefixWord ++ tailWord_459412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459479 : List Nat := [1, 1, 3, 2, 1, 6, 1, 3, 1, 1, 3]
def baseStart_459479 : Nat := 118140960795 + 459479 * 2 ^ 59
def prefixEnd_459479 : Nat := 4983230072969 + 3 ^ 40 * 459479 * 2
def baseEnd_459479 : Nat := 235933577647313019999401

theorem tailTrace_459479 : CollatzResearch.WordTrace tailWord_459479 prefixEnd_459479 235933577647313019999401 := by
  unfold tailWord_459479
  simp only [CollatzResearch.WordTrace]
  refine ⟨16758575902393530610773491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11172383934929020407182327 16758575902393530610773491)
  ·
    refine ⟨25137863853590295916160237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16758575902393530610773491 25137863853590295916160237)
    ·
      refine ⟨9426698945096360968560089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25137863853590295916160237 9426698945096360968560089)
      ·
        refine ⟨7070024208822270726420067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9426698945096360968560089 7070024208822270726420067)
        ·
          refine ⟨10605036313233406089630101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7070024208822270726420067 10605036313233406089630101)
          ·
            refine ⟨497111077182815910451411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10605036313233406089630101 497111077182815910451411)
            ·
              refine ⟨745666615774223865677117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497111077182815910451411 745666615774223865677117)
              ·
                refine ⟨279624980915333949628919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 745666615774223865677117 279624980915333949628919)
                ·
                  refine ⟨419437471373000924443379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279624980915333949628919 419437471373000924443379)
                  ·
                    refine ⟨629156207059501386665069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 419437471373000924443379 629156207059501386665069)
                    ·
                      refine ⟨235933577647313019999401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 629156207059501386665069 235933577647313019999401)
                      ·
                        rfl

theorem cell23_459479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3, 1, 1, 3].length) (baseStart_459479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459479 prefixEnd_459479 := by exact prefixLift 459479
  have htrace : WordTrace (prefixWord ++ tailWord_459479) baseStart_459479 baseEnd_459479 := by
    simpa [prefixWord, tailWord_459479, baseEnd_459479] using wordTrace_append hprefix tailTrace_459479
  have hstable : (prefixWord ++ tailWord_459479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459479).length < 2 ^ (prefixWord ++ tailWord_459479).sum := by decide
  have hdescent : baseEnd_459479 < baseStart_459479 := by decide
  rcases family_descends (prefixWord ++ tailWord_459479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459488 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 3]
def baseStart_459488 : Nat := 118140960795 + 459488 * 2 ^ 59
def prefixEnd_459488 : Nat := 4983230072969 + 3 ^ 40 * 459488 * 2
def baseEnd_459488 : Nat := 235938198973203484786859

theorem tailTrace_459488 : CollatzResearch.WordTrace tailWord_459488 prefixEnd_459488 235938198973203484786859 := by
  unfold tailWord_459488
  simp only [CollatzResearch.WordTrace]
  refine ⟨8379452079680462573925559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11172602772907283431900745 8379452079680462573925559)
  ·
    refine ⟨12569178119520693860888339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8379452079680462573925559 12569178119520693860888339)
    ·
      refine ⟨18853767179281040791332509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12569178119520693860888339 18853767179281040791332509)
      ·
        refine ⟨7070162692230390296749691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18853767179281040791332509 7070162692230390296749691)
        ·
          refine ⟨10605244038345585445124537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7070162692230390296749691 10605244038345585445124537)
          ·
            refine ⟨7953933028759189083843403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10605244038345585445124537 7953933028759189083843403)
            ·
              refine ⟨11930899543138783625765105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7953933028759189083843403 11930899543138783625765105)
              ·
                refine ⟨8948174657354087719323829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11930899543138783625765105 8948174657354087719323829)
                ·
                  refine ⟨838891374126945723686609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8948174657354087719323829 838891374126945723686609)
                  ·
                    refine ⟨629168530595209292764957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 838891374126945723686609 629168530595209292764957)
                    ·
                      refine ⟨235938198973203484786859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 629168530595209292764957 235938198973203484786859)
                      ·
                        rfl

theorem cell23_459488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_459488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459488 prefixEnd_459488 := by exact prefixLift 459488
  have htrace : WordTrace (prefixWord ++ tailWord_459488) baseStart_459488 baseEnd_459488 := by
    simpa [prefixWord, tailWord_459488, baseEnd_459488] using wordTrace_append hprefix tailTrace_459488
  have hstable : (prefixWord ++ tailWord_459488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459488).length < 2 ^ (prefixWord ++ tailWord_459488).sum := by decide
  have hdescent : baseEnd_459488 < baseStart_459488 := by decide
  rcases family_descends (prefixWord ++ tailWord_459488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459496 : List Nat := [2, 1, 4, 1, 4, 1, 3, 2, 1, 1, 3]
def baseStart_459496 : Nat := 118140960795 + 459496 * 2 ^ 59
def prefixEnd_459496 : Nat := 4983230072969 + 3 ^ 40 * 459496 * 2
def baseEnd_459496 : Nat := 235942306818439453486823

theorem tailTrace_459496 : CollatzResearch.WordTrace tailWord_459496 prefixEnd_459496 235942306818439453486823 := by
  unfold tailWord_459496
  simp only [CollatzResearch.WordTrace]
  refine ⟨8379597971665971257071171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11172797295554628342761561 8379597971665971257071171)
  ·
    refine ⟨12569396957498956885606757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8379597971665971257071171 12569396957498956885606757)
    ·
      refine ⟨2356761929531054416051267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12569396957498956885606757 2356761929531054416051267)
      ·
        refine ⟨3535142894296581624076901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2356761929531054416051267 3535142894296581624076901)
        ·
          refine ⟨662839292680609054514419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3535142894296581624076901 662839292680609054514419)
          ·
            refine ⟨994258939020913581771629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662839292680609054514419 994258939020913581771629)
            ·
              refine ⟨372847102132842593164361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 994258939020913581771629 372847102132842593164361)
              ·
                refine ⟨279635326599631944873271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372847102132842593164361 279635326599631944873271)
                ·
                  refine ⟨419452989899447917309907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279635326599631944873271 419452989899447917309907)
                  ·
                    refine ⟨629179484849171875964861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 419452989899447917309907 629179484849171875964861)
                    ·
                      refine ⟨235942306818439453486823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 629179484849171875964861 235942306818439453486823)
                      ·
                        rfl

theorem cell23_459496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_459496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459496 prefixEnd_459496 := by exact prefixLift 459496
  have htrace : WordTrace (prefixWord ++ tailWord_459496) baseStart_459496 baseEnd_459496 := by
    simpa [prefixWord, tailWord_459496, baseEnd_459496] using wordTrace_append hprefix tailTrace_459496
  have hstable : (prefixWord ++ tailWord_459496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459496).length < 2 ^ (prefixWord ++ tailWord_459496).sum := by decide
  have hdescent : baseEnd_459496 < baseStart_459496 := by decide
  rcases family_descends (prefixWord ++ tailWord_459496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459511 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 6]
def baseStart_459511 : Nat := 118140960795 + 459511 * 2 ^ 59
def prefixEnd_459511 : Nat := 4983230072969 + 3 ^ 40 * 459511 * 2
def baseEnd_459511 : Nat := 235950009028256894799253

theorem tailTrace_459511 : CollatzResearch.WordTrace tailWord_459511 prefixEnd_459511 235950009028256894799253 := by
  unfold tailWord_459511
  simp only [CollatzResearch.WordTrace]
  refine ⟨16759743038277600075938387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11173162025518400050625591 16759743038277600075938387)
  ·
    refine ⟨25139614557416400113907581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16759743038277600075938387 25139614557416400113907581)
    ·
      refine ⟨9427355459031150042715343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25139614557416400113907581 9427355459031150042715343)
      ·
        refine ⟨14141033188546725064073015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9427355459031150042715343 14141033188546725064073015)
        ·
          refine ⟨21211549782820087596109523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14141033188546725064073015 21211549782820087596109523)
          ·
            refine ⟨31817324674230131394164285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21211549782820087596109523 31817324674230131394164285)
            ·
              refine ⟨11931496752836299272811607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31817324674230131394164285 11931496752836299272811607)
              ·
                refine ⟨17897245129254448909217411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11931496752836299272811607 17897245129254448909217411)
                ·
                  refine ⟨26845867693881673363826117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17897245129254448909217411 26845867693881673363826117)
                  ·
                    refine ⟨5033600192602813755717397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26845867693881673363826117 5033600192602813755717397)
                    ·
                      refine ⟨235950009028256894799253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5033600192602813755717397 235950009028256894799253)
                      ·
                        rfl

theorem cell23_459511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_459511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459511 prefixEnd_459511 := by exact prefixLift 459511
  have htrace : WordTrace (prefixWord ++ tailWord_459511) baseStart_459511 baseEnd_459511 := by
    simpa [prefixWord, tailWord_459511, baseEnd_459511] using wordTrace_append hprefix tailTrace_459511
  have hstable : (prefixWord ++ tailWord_459511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459511).length < 2 ^ (prefixWord ++ tailWord_459511).sum := by decide
  have hdescent : baseEnd_459511 < baseStart_459511 := by decide
  rcases family_descends (prefixWord ++ tailWord_459511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459522 : List Nat := [3, 4, 1, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_459522 : Nat := 118140960795 + 459522 * 2 ^ 59
def prefixEnd_459522 : Nat := 4983230072969 + 3 ^ 40 * 459522 * 2
def baseEnd_459522 : Nat := 235955657315456351761703

theorem tailTrace_459522 : CollatzResearch.WordTrace tailWord_459522 prefixEnd_459522 235955657315456351761703 := by
  unfold tailWord_459522
  simp only [CollatzResearch.WordTrace]
  refine ⟨4190036060309437238647205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11173429494158499303059213 4190036060309437238647205)
  ·
    refine ⟨785631761308019482246351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4190036060309437238647205 785631761308019482246351)
    ·
      refine ⟨1178447641962029223369527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 785631761308019482246351 1178447641962029223369527)
      ·
        refine ⟨1767671462943043835054291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1178447641962029223369527 1767671462943043835054291)
        ·
          refine ⟨2651507194414565752581437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1767671462943043835054291 2651507194414565752581437)
          ·
            refine ⟨994315197905462157218039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2651507194414565752581437 994315197905462157218039)
            ·
              refine ⟨1491472796858193235827059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 994315197905462157218039 1491472796858193235827059)
              ·
                refine ⟨2237209195287289853740589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1491472796858193235827059 2237209195287289853740589)
                ·
                  refine ⟨838953448232733695152721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2237209195287289853740589 838953448232733695152721)
                  ·
                    refine ⟨629215086174550271364541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 838953448232733695152721 629215086174550271364541)
                    ·
                      refine ⟨235955657315456351761703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 629215086174550271364541 235955657315456351761703)
                      ·
                        rfl

theorem cell23_459522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_459522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459522 prefixEnd_459522 := by exact prefixLift 459522
  have htrace : WordTrace (prefixWord ++ tailWord_459522) baseStart_459522 baseEnd_459522 := by
    simpa [prefixWord, tailWord_459522, baseEnd_459522] using wordTrace_append hprefix tailTrace_459522
  have hstable : (prefixWord ++ tailWord_459522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459522).length < 2 ^ (prefixWord ++ tailWord_459522).sum := by decide
  have hdescent : baseEnd_459522 < baseStart_459522 := by decide
  rcases family_descends (prefixWord ++ tailWord_459522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459552 : List Nat := [2, 1, 1, 5, 1, 2, 1, 4, 2, 1, 3]
def baseStart_459552 : Nat := 118140960795 + 459552 * 2 ^ 59
def prefixEnd_459552 : Nat := 4983230072969 + 3 ^ 40 * 459552 * 2
def baseEnd_459552 : Nat := 235971061735091234386565

theorem tailTrace_459552 : CollatzResearch.WordTrace tailWord_459552 prefixEnd_459552 235971061735091234386565 := by
  unfold tailWord_459552
  simp only [CollatzResearch.WordTrace]
  refine ⟨8380619215564532039090455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11174158954086042718787273 8380619215564532039090455)
  ·
    refine ⟨12570928823346798058635683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8380619215564532039090455 12570928823346798058635683)
    ·
      refine ⟨18856393235020197087953525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12570928823346798058635683 18856393235020197087953525)
      ·
        refine ⟨1767786865783143476995643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18856393235020197087953525 1767786865783143476995643)
        ·
          refine ⟨2651680298674715215493465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1767786865783143476995643 2651680298674715215493465)
          ·
            refine ⟨1988760224006036411620099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2651680298674715215493465 1988760224006036411620099)
            ·
              refine ⟨2983140336009054617430149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1988760224006036411620099 2983140336009054617430149)
              ·
                refine ⟨559338813001697740768153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2983140336009054617430149 559338813001697740768153)
                ·
                  refine ⟨419504109751273305576115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 559338813001697740768153 419504109751273305576115)
                  ·
                    refine ⟨629256164626909958364173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 419504109751273305576115 629256164626909958364173)
                    ·
                      refine ⟨235971061735091234386565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 629256164626909958364173 235971061735091234386565)
                      ·
                        rfl

theorem cell23_459552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_459552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459552 prefixEnd_459552 := by exact prefixLift 459552
  have htrace : WordTrace (prefixWord ++ tailWord_459552) baseStart_459552 baseEnd_459552 := by
    simpa [prefixWord, tailWord_459552, baseEnd_459552] using wordTrace_append hprefix tailTrace_459552
  have hstable : (prefixWord ++ tailWord_459552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459552).length < 2 ^ (prefixWord ++ tailWord_459552).sum := by decide
  have hdescent : baseEnd_459552 < baseStart_459552 := by decide
  rcases family_descends (prefixWord ++ tailWord_459552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459590 : List Nat := [6, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3]
def baseStart_459590 : Nat := 118140960795 + 459590 * 2 ^ 59
def prefixEnd_459590 : Nat := 4983230072969 + 3 ^ 40 * 459590 * 2
def baseEnd_459590 : Nat := 235990573999962085711391

theorem tailTrace_459590 : CollatzResearch.WordTrace tailWord_459590 prefixEnd_459590 235990573999962085711391 := by
  unfold tailWord_459590
  simp only [CollatzResearch.WordTrace]
  refine ⟨523832012655981142752007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11175082936660931045376149 523832012655981142752007)
  ·
    refine ⟨785748018983971714128011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 523832012655981142752007 785748018983971714128011)
    ·
      refine ⟨1178622028475957571192017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 785748018983971714128011 1178622028475957571192017)
      ·
        refine ⟨883966521356968178394013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1178622028475957571192017 883966521356968178394013)
        ·
          refine ⟨331487445508863066897755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 883966521356968178394013 331487445508863066897755)
          ·
            refine ⟨497231168263294600346633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331487445508863066897755 497231168263294600346633)
            ·
              refine ⟨372923376197470950259975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 497231168263294600346633 372923376197470950259975)
              ·
                refine ⟨559385064296206425389963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 372923376197470950259975 559385064296206425389963)
                ·
                  refine ⟨839077596444309638084945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 559385064296206425389963 839077596444309638084945)
                  ·
                    refine ⟨629308197333232228563709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 839077596444309638084945 629308197333232228563709)
                    ·
                      refine ⟨235990573999962085711391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 629308197333232228563709 235990573999962085711391)
                      ·
                        rfl

theorem cell23_459590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_459590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459590 prefixEnd_459590 := by exact prefixLift 459590
  have htrace : WordTrace (prefixWord ++ tailWord_459590) baseStart_459590 baseEnd_459590 := by
    simpa [prefixWord, tailWord_459590, baseEnd_459590] using wordTrace_append hprefix tailTrace_459590
  have hstable : (prefixWord ++ tailWord_459590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459590).length < 2 ^ (prefixWord ++ tailWord_459590).sum := by decide
  have hdescent : baseEnd_459590 < baseStart_459590 := by decide
  rcases family_descends (prefixWord ++ tailWord_459590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459592 : List Nat := [2, 1, 3, 1, 1, 3, 2, 2, 4, 2, 2]
def baseStart_459592 : Nat := 118140960795 + 459592 * 2 ^ 59
def prefixEnd_459592 : Nat := 4983230072969 + 3 ^ 40 * 459592 * 2
def baseEnd_459592 : Nat := 235991600961271077886381

theorem tailTrace_459592 : CollatzResearch.WordTrace tailWord_459592 prefixEnd_459592 235991600961271077886381 := by
  unfold tailWord_459592
  simp only [CollatzResearch.WordTrace]
  refine ⟨8381348675492075454818515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11175131567322767273091353 8381348675492075454818515)
  ·
    refine ⟨12572023013238113182227773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8381348675492075454818515 12572023013238113182227773)
    ·
      refine ⟨4714508629964292443335415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12572023013238113182227773 4714508629964292443335415)
      ·
        refine ⟨7071762944946438665003123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4714508629964292443335415 7071762944946438665003123)
        ·
          refine ⟨10607644417419657997504685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7071762944946438665003123 10607644417419657997504685)
          ·
            refine ⟨3977866656532371749064257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10607644417419657997504685 3977866656532371749064257)
            ·
              refine ⟨2983399992399278811798193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3977866656532371749064257 2983399992399278811798193)
              ·
                refine ⟨2237549994299459108848645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2983399992399278811798193 2237549994299459108848645)
                ·
                  refine ⟨419540623931148582909121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2237549994299459108848645 419540623931148582909121)
                  ·
                    refine ⟨314655467948361437181841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 419540623931148582909121 314655467948361437181841)
                    ·
                      refine ⟨235991600961271077886381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 314655467948361437181841 235991600961271077886381)
                      ·
                        rfl

theorem cell23_459592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 4, 2, 2].length) (baseStart_459592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459592 prefixEnd_459592 := by exact prefixLift 459592
  have htrace : WordTrace (prefixWord ++ tailWord_459592) baseStart_459592 baseEnd_459592 := by
    simpa [prefixWord, tailWord_459592, baseEnd_459592] using wordTrace_append hprefix tailTrace_459592
  have hstable : (prefixWord ++ tailWord_459592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459592).length < 2 ^ (prefixWord ++ tailWord_459592).sum := by decide
  have hdescent : baseEnd_459592 < baseStart_459592 := by decide
  rcases family_descends (prefixWord ++ tailWord_459592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459596 : List Nat := [2, 2, 1, 3, 3, 3, 2, 1, 1, 3, 2]
def baseStart_459596 : Nat := 118140960795 + 459596 * 2 ^ 59
def prefixEnd_459596 : Nat := 4983230072969 + 3 ^ 40 * 459596 * 2
def baseEnd_459596 : Nat := 235993654883889062236363

theorem tailTrace_459596 : CollatzResearch.WordTrace tailWord_459596 prefixEnd_459596 235993654883889062236363 := by
  unfold tailWord_459596
  simp only [CollatzResearch.WordTrace]
  refine ⟨8381421621484829796391321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11175228828646439728521761 8381421621484829796391321)
  ·
    refine ⟨6286066216113622347293491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8381421621484829796391321 6286066216113622347293491)
    ·
      refine ⟨9429099324170433520940237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6286066216113622347293491 9429099324170433520940237)
      ·
        refine ⟨3535912246563912570352589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9429099324170433520940237 3535912246563912570352589)
        ·
          refine ⟨1325967092461467213882221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3535912246563912570352589 1325967092461467213882221)
          ·
            refine ⟨497237659673050205205833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1325967092461467213882221 497237659673050205205833)
            ·
              refine ⟨372928244754787653904375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 497237659673050205205833 372928244754787653904375)
              ·
                refine ⟨559392367132181480856563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 372928244754787653904375 559392367132181480856563)
                ·
                  refine ⟨839088550698272221284845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 559392367132181480856563 839088550698272221284845)
                  ·
                    refine ⟨314658206511852082981817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 839088550698272221284845 314658206511852082981817)
                    ·
                      refine ⟨235993654883889062236363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 314658206511852082981817 235993654883889062236363)
                      ·
                        rfl

theorem cell23_459596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_459596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459596 prefixEnd_459596 := by exact prefixLift 459596
  have htrace : WordTrace (prefixWord ++ tailWord_459596) baseStart_459596 baseEnd_459596 := by
    simpa [prefixWord, tailWord_459596, baseEnd_459596] using wordTrace_append hprefix tailTrace_459596
  have hstable : (prefixWord ++ tailWord_459596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459596).length < 2 ^ (prefixWord ++ tailWord_459596).sum := by decide
  have hdescent : baseEnd_459596 < baseStart_459596 := by decide
  rcases family_descends (prefixWord ++ tailWord_459596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459609 : List Nat := [1, 2, 1, 2, 2, 4, 3, 2, 2, 2, 2]
def baseStart_459609 : Nat := 118140960795 + 459609 * 2 ^ 59
def prefixEnd_459609 : Nat := 4983230072969 + 3 ^ 40 * 459609 * 2
def baseEnd_459609 : Nat := 236000330132397511373803

theorem tailTrace_459609 : CollatzResearch.WordTrace tailWord_459609 prefixEnd_459609 236000330132397511373803 := by
  unfold tailWord_459609
  simp only [CollatzResearch.WordTrace]
  refine ⟨16763317391922562813005881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11175544927948375208670587 16763317391922562813005881)
  ·
    refine ⟨12572488043941922109754411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16763317391922562813005881 12572488043941922109754411)
    ·
      refine ⟨18858732065912883164631617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12572488043941922109754411 18858732065912883164631617)
      ·
        refine ⟨14144049049434662373473713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18858732065912883164631617 14144049049434662373473713)
        ·
          refine ⟨10608036787075996780105285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14144049049434662373473713 10608036787075996780105285)
          ·
            refine ⟨1989006897576749396269741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10608036787075996780105285 1989006897576749396269741)
            ·
              refine ⟨745877586591281023601153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1989006897576749396269741 745877586591281023601153)
              ·
                refine ⟨559408189943460767700865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 745877586591281023601153 559408189943460767700865)
                ·
                  refine ⟨419556142457595575775649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 559408189943460767700865 419556142457595575775649)
                  ·
                    refine ⟨314667106843196681831737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 419556142457595575775649 314667106843196681831737)
                    ·
                      refine ⟨236000330132397511373803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 314667106843196681831737 236000330132397511373803)
                      ·
                        rfl

theorem cell23_459609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2, 2, 2].length) (baseStart_459609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459609 prefixEnd_459609 := by exact prefixLift 459609
  have htrace : WordTrace (prefixWord ++ tailWord_459609) baseStart_459609 baseEnd_459609 := by
    simpa [prefixWord, tailWord_459609, baseEnd_459609] using wordTrace_append hprefix tailTrace_459609
  have hstable : (prefixWord ++ tailWord_459609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459609).length < 2 ^ (prefixWord ++ tailWord_459609).sum := by decide
  have hdescent : baseEnd_459609 < baseStart_459609 := by decide
  rcases family_descends (prefixWord ++ tailWord_459609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459615 : List Nat := [1, 1, 2, 3, 1, 3, 1, 6, 5]
def baseStart_459615 : Nat := 118140960795 + 459615 * 2 ^ 59
def prefixEnd_459615 : Nat := 4983230072969 + 3 ^ 40 * 459615 * 2
def baseEnd_459615 : Nat := 26222601224036054210975

theorem tailTrace_459615 : CollatzResearch.WordTrace tailWord_459615 prefixEnd_459615 26222601224036054210975 := by
  unfold tailWord_459615
  simp only [CollatzResearch.WordTrace]
  refine ⟨16763536229900825837724299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11175690819933883891816199 16763536229900825837724299)
  ·
    refine ⟨25145304344851238756586449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16763536229900825837724299 25145304344851238756586449)
    ·
      refine ⟨18858978258638429067439837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25145304344851238756586449 18858978258638429067439837)
      ·
        refine ⟨7072116846989410900289939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18858978258638429067439837 7072116846989410900289939)
        ·
          refine ⟨10608175270484116350434909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7072116846989410900289939 10608175270484116350434909)
          ·
            refine ⟨3978065726431543631413091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10608175270484116350434909 3978065726431543631413091)
            ·
              refine ⟨5967098589647315447119637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3978065726431543631413091 5967098589647315447119637)
              ·
                refine ⟨279707746389717911583733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5967098589647315447119637 279707746389717911583733)
                ·
                  refine ⟨26222601224036054210975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 279707746389717911583733 26222601224036054210975)
                  ·
                    rfl

theorem cell23_459615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6, 5].length) (baseStart_459615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459615 prefixEnd_459615 := by exact prefixLift 459615
  have htrace : WordTrace (prefixWord ++ tailWord_459615) baseStart_459615 baseEnd_459615 := by
    simpa [prefixWord, tailWord_459615, baseEnd_459615] using wordTrace_append hprefix tailTrace_459615
  have hstable : (prefixWord ++ tailWord_459615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459615).length < 2 ^ (prefixWord ++ tailWord_459615).sum := by decide
  have hdescent : baseEnd_459615 < baseStart_459615 := by decide
  rcases family_descends (prefixWord ++ tailWord_459615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459628 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 3, 7]
def baseStart_459628 : Nat := 118140960795 + 459628 * 2 ^ 59
def prefixEnd_459628 : Nat := 4983230072969 + 3 ^ 40 * 459628 * 2
def baseEnd_459628 : Nat := 78670028754944312345405

theorem tailTrace_459628 : CollatzResearch.WordTrace tailWord_459628 prefixEnd_459628 78670028754944312345405 := by
  unfold tailWord_459628
  simp only [CollatzResearch.WordTrace]
  refine ⟨8382005189426864528973769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11176006919235819371965025 8382005189426864528973769)
  ·
    refine ⟨6286503892070148396730327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8382005189426864528973769 6286503892070148396730327)
    ·
      refine ⟨9429755838105222595095491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6286503892070148396730327 9429755838105222595095491)
      ·
        refine ⟨14144633757157833892643237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9429755838105222595095491 14144633757157833892643237)
        ·
          refine ⟨2652118829467093854870607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14144633757157833892643237 2652118829467093854870607)
          ·
            refine ⟨3978178244200640782305911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2652118829467093854870607 3978178244200640782305911)
            ·
              refine ⟨5967267366300961173458867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3978178244200640782305911 5967267366300961173458867)
              ·
                refine ⟨8950901049451441760188301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5967267366300961173458867 8950901049451441760188301)
                ·
                  refine ⟨3356587893544290660070613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8950901049451441760188301 3356587893544290660070613)
                  ·
                    refine ⟨78670028754944312345405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3356587893544290660070613 78670028754944312345405)
                    ·
                      rfl

theorem cell23_459628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_459628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459628 prefixEnd_459628 := by exact prefixLift 459628
  have htrace : WordTrace (prefixWord ++ tailWord_459628) baseStart_459628 baseEnd_459628 := by
    simpa [prefixWord, tailWord_459628, baseEnd_459628] using wordTrace_append hprefix tailTrace_459628
  have hstable : (prefixWord ++ tailWord_459628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459628).length < 2 ^ (prefixWord ++ tailWord_459628).sum := by decide
  have hdescent : baseEnd_459628 < baseStart_459628 := by decide
  rcases family_descends (prefixWord ++ tailWord_459628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459635 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 2, 5, 2]
def baseStart_459635 : Nat := 118140960795 + 459635 * 2 ^ 59
def prefixEnd_459635 : Nat := 4983230072969 + 3 ^ 40 * 459635 * 2
def baseEnd_459635 : Nat := 236013680629414409648683

theorem tailTrace_459635 : CollatzResearch.WordTrace tailWord_459635 prefixEnd_459635 236013680629414409648683 := by
  unfold tailWord_459635
  simp only [CollatzResearch.WordTrace]
  refine ⟨16764265689828369253452359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11176177126552246168968239 16764265689828369253452359)
  ·
    refine ⟨25146398534742553880178539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16764265689828369253452359 25146398534742553880178539)
    ·
      refine ⟨37719597802113830820267809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25146398534742553880178539 37719597802113830820267809)
      ·
        refine ⟨28289698351585373115200857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37719597802113830820267809 28289698351585373115200857)
        ·
          refine ⟨21217273763689029836400643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28289698351585373115200857 21217273763689029836400643)
          ·
            refine ⟨31825910645533544754600965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21217273763689029836400643 31825910645533544754600965)
            ·
              refine ⟨5967358246037539641487681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31825910645533544754600965 5967358246037539641487681)
              ·
                refine ⟨4475518684528154731115761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5967358246037539641487681 4475518684528154731115761)
                ·
                  refine ⟨3356639013396116048336821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4475518684528154731115761 3356639013396116048336821)
                  ·
                    refine ⟨314684907505885879531577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3356639013396116048336821 314684907505885879531577)
                    ·
                      refine ⟨236013680629414409648683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 314684907505885879531577 236013680629414409648683)
                      ·
                        rfl

theorem cell23_459635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 5, 2].length) (baseStart_459635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459635 prefixEnd_459635 := by exact prefixLift 459635
  have htrace : WordTrace (prefixWord ++ tailWord_459635) baseStart_459635 baseEnd_459635 := by
    simpa [prefixWord, tailWord_459635, baseEnd_459635] using wordTrace_append hprefix tailTrace_459635
  have hstable : (prefixWord ++ tailWord_459635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459635).length < 2 ^ (prefixWord ++ tailWord_459635).sum := by decide
  have hdescent : baseEnd_459635 < baseStart_459635 := by decide
  rcases family_descends (prefixWord ++ tailWord_459635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459666 : List Nat := [3, 2, 3, 2, 2, 1, 3, 2, 5]
def baseStart_459666 : Nat := 118140960795 + 459666 * 2 ^ 59
def prefixEnd_459666 : Nat := 4983230072969 + 3 ^ 40 * 459666 * 2
def baseEnd_459666 : Nat := 26225510947744865373449

theorem tailTrace_459666 : CollatzResearch.WordTrace tailWord_459666 prefixEnd_459666 26225510947744865373449 := by
  unfold tailWord_459666
  simp only [CollatzResearch.WordTrace]
  refine ⟨4191349088179015386957713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11176930901810707698553901 4191349088179015386957713)
  ·
    refine ⟨3143511816134261540218285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4191349088179015386957713 3143511816134261540218285)
    ·
      refine ⟨1178816931050348077581857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3143511816134261540218285 1178816931050348077581857)
      ·
        refine ⟨884112698287761058186393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1178816931050348077581857 884112698287761058186393)
        ·
          refine ⟨663084523715820793639795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 884112698287761058186393 663084523715820793639795)
          ·
            refine ⟨994626785573731190459693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663084523715820793639795 994626785573731190459693)
            ·
              refine ⟨372985044590149196422385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 994626785573731190459693 372985044590149196422385)
              ·
                refine ⟨279738783442611897316789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372985044590149196422385 279738783442611897316789)
                ·
                  refine ⟨26225510947744865373449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 279738783442611897316789 26225510947744865373449)
                  ·
                    rfl

theorem cell23_459666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2, 5].length) (baseStart_459666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459666 prefixEnd_459666 := by exact prefixLift 459666
  have htrace : WordTrace (prefixWord ++ tailWord_459666) baseStart_459666 baseEnd_459666 := by
    simpa [prefixWord, tailWord_459666, baseEnd_459666] using wordTrace_append hprefix tailTrace_459666
  have hstable : (prefixWord ++ tailWord_459666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459666).length < 2 ^ (prefixWord ++ tailWord_459666).sum := by decide
  have hdescent : baseEnd_459666 < baseStart_459666 := by decide
  rcases family_descends (prefixWord ++ tailWord_459666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459726 : List Nat := [4, 1, 1, 1, 2, 3, 4, 2, 1, 4]
def baseStart_459726 : Nat := 118140960795 + 459726 * 2 ^ 59
def prefixEnd_459726 : Nat := 4983230072969 + 3 ^ 40 * 459726 * 2
def baseEnd_459726 : Nat := 78686802456324517870255

theorem tailTrace_459726 : CollatzResearch.WordTrace tailWord_459726 prefixEnd_459726 78686802456324517870255 := by
  unfold tailWord_459726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2095948091562336474376879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11178389821665794530010021 2095948091562336474376879)
  ·
    refine ⟨3143922137343504711565319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2095948091562336474376879 3143922137343504711565319)
    ·
      refine ⟨4715883206015257067347979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3143922137343504711565319 4715883206015257067347979)
      ·
        refine ⟨7073824809022885601021969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4715883206015257067347979 7073824809022885601021969)
        ·
          refine ⟨5305368606767164200766477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7073824809022885601021969 5305368606767164200766477)
          ·
            refine ⟨1989513227537686575287429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5305368606767164200766477 1989513227537686575287429)
            ·
              refine ⟨373033730163316232866393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1989513227537686575287429 373033730163316232866393)
              ·
                refine ⟨279775297622487174649795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373033730163316232866393 279775297622487174649795)
                ·
                  refine ⟨419662946433730761974693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279775297622487174649795 419662946433730761974693)
                  ·
                    refine ⟨78686802456324517870255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 419662946433730761974693 78686802456324517870255)
                    ·
                      rfl

theorem cell23_459726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_459726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459726 prefixEnd_459726 := by exact prefixLift 459726
  have htrace : WordTrace (prefixWord ++ tailWord_459726) baseStart_459726 baseEnd_459726 := by
    simpa [prefixWord, tailWord_459726, baseEnd_459726] using wordTrace_append hprefix tailTrace_459726
  have hstable : (prefixWord ++ tailWord_459726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459726).length < 2 ^ (prefixWord ++ tailWord_459726).sum := by decide
  have hdescent : baseEnd_459726 < baseStart_459726 := by decide
  rcases family_descends (prefixWord ++ tailWord_459726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459759 : List Nat := [1, 1, 2, 1, 4, 3, 3, 1, 2, 3, 2]
def baseStart_459759 : Nat := 118140960795 + 459759 * 2 ^ 59
def prefixEnd_459759 : Nat := 4983230072969 + 3 ^ 40 * 459759 * 2
def baseEnd_459759 : Nat := 236077352230571924498113

theorem tailTrace_459759 : CollatzResearch.WordTrace tailWord_459759 prefixEnd_459759 236077352230571924498113 := by
  unfold tailWord_459759
  simp only [CollatzResearch.WordTrace]
  refine ⟨16768788341379138430966331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11179192227586092287310887 16768788341379138430966331)
  ·
    refine ⟨25153182512068707646449497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16768788341379138430966331 25153182512068707646449497)
    ·
      refine ⟨18864886884051530734837123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25153182512068707646449497 18864886884051530734837123)
      ·
        refine ⟨28297330326077296102255685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18864886884051530734837123 28297330326077296102255685)
        ·
          refine ⟨5305749436139493019172941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28297330326077296102255685 5305749436139493019172941)
          ·
            refine ⟨1989656038552309882189853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5305749436139493019172941 1989656038552309882189853)
            ·
              refine ⟨746121014457116205821195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1989656038552309882189853 746121014457116205821195)
              ·
                refine ⟨1119181521685674308731793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746121014457116205821195 1119181521685674308731793)
                ·
                  refine ⟨839386141264255731548845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1119181521685674308731793 839386141264255731548845)
                  ·
                    refine ⟨314769802974095899330817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 839386141264255731548845 314769802974095899330817)
                    ·
                      refine ⟨236077352230571924498113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 314769802974095899330817 236077352230571924498113)
                      ·
                        rfl

theorem cell23_459759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 3, 2].length) (baseStart_459759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459759 prefixEnd_459759 := by exact prefixLift 459759
  have htrace : WordTrace (prefixWord ++ tailWord_459759) baseStart_459759 baseEnd_459759 := by
    simpa [prefixWord, tailWord_459759, baseEnd_459759] using wordTrace_append hprefix tailTrace_459759
  have hstable : (prefixWord ++ tailWord_459759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459759).length < 2 ^ (prefixWord ++ tailWord_459759).sum := by decide
  have hdescent : baseEnd_459759 < baseStart_459759 := by decide
  rcases family_descends (prefixWord ++ tailWord_459759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459785 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 3, 2, 4]
def baseStart_459785 : Nat := 118140960795 + 459785 * 2 ^ 59
def prefixEnd_459785 : Nat := 4983230072969 + 3 ^ 40 * 459785 * 2
def baseEnd_459785 : Nat := 236090702727588822772993

theorem tailTrace_459785 : CollatzResearch.WordTrace tailWord_459785 prefixEnd_459785 236090702727588822772993 := by
  unfold tailWord_459785
  simp only [CollatzResearch.WordTrace]
  refine ⟨16769736639284944871412809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11179824426189963247608539 16769736639284944871412809)
  ·
    refine ⟨12577302479463708653559607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16769736639284944871412809 12577302479463708653559607)
    ·
      refine ⟨18865953719195562980339411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12577302479463708653559607 18865953719195562980339411)
      ·
        refine ⟨28298930578793344470509117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18865953719195562980339411 28298930578793344470509117)
        ·
          refine ⟨10612098967047504176440919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28298930578793344470509117 10612098967047504176440919)
          ·
            refine ⟨15918148450571256264661379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10612098967047504176440919 15918148450571256264661379)
            ·
              refine ⟨23877222675856884396992069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15918148450571256264661379 23877222675856884396992069)
              ·
                refine ⟨4476979251723165824436013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23877222675856884396992069 4476979251723165824436013)
                ·
                  refine ⟨1678867219396187184163505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4476979251723165824436013 1678867219396187184163505)
                  ·
                    refine ⟨1259150414547140388122629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1678867219396187184163505 1259150414547140388122629)
                    ·
                      refine ⟨236090702727588822772993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1259150414547140388122629 236090702727588822772993)
                      ·
                        rfl

theorem cell23_459785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 2, 4].length) (baseStart_459785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459785 prefixEnd_459785 := by exact prefixLift 459785
  have htrace : WordTrace (prefixWord ++ tailWord_459785) baseStart_459785 baseEnd_459785 := by
    simpa [prefixWord, tailWord_459785, baseEnd_459785] using wordTrace_append hprefix tailTrace_459785
  have hstable : (prefixWord ++ tailWord_459785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459785).length < 2 ^ (prefixWord ++ tailWord_459785).sum := by decide
  have hdescent : baseEnd_459785 < baseStart_459785 := by decide
  rcases family_descends (prefixWord ++ tailWord_459785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459799 : List Nat := [1, 1, 3, 5, 1, 3, 1, 1, 1, 6]
def baseStart_459799 : Nat := 118140960795 + 459799 * 2 ^ 59
def prefixEnd_459799 : Nat := 4983230072969 + 3 ^ 40 * 459799 * 2
def baseEnd_459799 : Nat := 78699297152250589332643

theorem tailTrace_459799 : CollatzResearch.WordTrace tailWord_459799 prefixEnd_459799 78699297152250589332643 := by
  unfold tailWord_459799
  simp only [CollatzResearch.WordTrace]
  refine ⟨16770247261234225262422451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11180164840822816841614967 16770247261234225262422451)
  ·
    refine ⟨25155370891851337893633677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16770247261234225262422451 25155370891851337893633677)
    ·
      refine ⟨9433264084444251710112629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25155370891851337893633677 9433264084444251710112629)
      ·
        refine ⟨884368507916648597823059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9433264084444251710112629 884368507916648597823059)
        ·
          refine ⟨1326552761874972896734589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884368507916648597823059 1326552761874972896734589)
          ·
            refine ⟨497457285703114836275471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1326552761874972896734589 497457285703114836275471)
            ·
              refine ⟨746185928554672254413207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497457285703114836275471 746185928554672254413207)
              ·
                refine ⟨1119278892832008381619811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746185928554672254413207 1119278892832008381619811)
                ·
                  refine ⟨1678918339248012572429717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1119278892832008381619811 1678918339248012572429717)
                  ·
                    refine ⟨78699297152250589332643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1678918339248012572429717 78699297152250589332643)
                    ·
                      rfl

theorem cell23_459799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 6].length) (baseStart_459799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459799 prefixEnd_459799 := by exact prefixLift 459799
  have htrace : WordTrace (prefixWord ++ tailWord_459799) baseStart_459799 baseEnd_459799 := by
    simpa [prefixWord, tailWord_459799, baseEnd_459799] using wordTrace_append hprefix tailTrace_459799
  have hstable : (prefixWord ++ tailWord_459799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459799).length < 2 ^ (prefixWord ++ tailWord_459799).sum := by decide
  have hdescent : baseEnd_459799 < baseStart_459799 := by decide
  rcases family_descends (prefixWord ++ tailWord_459799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459809 : List Nat := [1, 2, 3, 2, 3, 1, 1, 4, 1, 2, 3]
def baseStart_459809 : Nat := 118140960795 + 459809 * 2 ^ 59
def prefixEnd_459809 : Nat := 4983230072969 + 3 ^ 40 * 459809 * 2
def baseEnd_459809 : Nat := 236103026263296728872883

theorem tailTrace_459809 : CollatzResearch.WordTrace tailWord_459809 prefixEnd_459809 236103026263296728872883 := by
  unfold tailWord_459809
  simp only [CollatzResearch.WordTrace]
  refine ⟨16770611991197996970286481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11180407994131997980190987 16770611991197996970286481)
  ·
    refine ⟨12577958993398497727714861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16770611991197996970286481 12577958993398497727714861)
    ·
      refine ⟨4716734622524436647893073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12577958993398497727714861 4716734622524436647893073)
      ·
        refine ⟨3537550966893327485919805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4716734622524436647893073 3537550966893327485919805)
        ·
          refine ⟨1326581612584997807219927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3537550966893327485919805 1326581612584997807219927)
          ·
            refine ⟨1989872418877496710829891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326581612584997807219927 1989872418877496710829891)
            ·
              refine ⟨2984808628316245066244837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1989872418877496710829891 2984808628316245066244837)
              ·
                refine ⟨559651617809295949920907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2984808628316245066244837 559651617809295949920907)
                ·
                  refine ⟨839477426713943924881361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 559651617809295949920907 839477426713943924881361)
                  ·
                    refine ⟨629608070035457943661021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 839477426713943924881361 629608070035457943661021)
                    ·
                      refine ⟨236103026263296728872883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 629608070035457943661021 236103026263296728872883)
                      ·
                        rfl

theorem cell23_459809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_459809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459809 prefixEnd_459809 := by exact prefixLift 459809
  have htrace : WordTrace (prefixWord ++ tailWord_459809) baseStart_459809 baseEnd_459809 := by
    simpa [prefixWord, tailWord_459809, baseEnd_459809] using wordTrace_append hprefix tailTrace_459809
  have hstable : (prefixWord ++ tailWord_459809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459809).length < 2 ^ (prefixWord ++ tailWord_459809).sum := by decide
  have hdescent : baseEnd_459809 < baseStart_459809 := by decide
  rcases family_descends (prefixWord ++ tailWord_459809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459812 : List Nat := [2, 3, 1, 4, 1, 2, 1, 9]
def baseStart_459812 : Nat := 118140960795 + 459812 * 2 ^ 59
def prefixEnd_459812 : Nat := 4983230072969 + 3 ^ 40 * 459812 * 2
def baseEnd_459812 : Nat := 8744613581676304338347

theorem tailTrace_459812 : CollatzResearch.WordTrace tailWord_459812 prefixEnd_459812 8744613581676304338347 := by
  unfold tailWord_459812
  simp only [CollatzResearch.WordTrace]
  refine ⟨8385360705093564241322845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11180480940124752321763793 8385360705093564241322845)
  ·
    refine ⟨3144510264410086590496067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8385360705093564241322845 3144510264410086590496067)
    ·
      refine ⟨4716765396615129885744101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3144510264410086590496067 4716765396615129885744101)
      ·
        refine ⟨884393511865336853577019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4716765396615129885744101 884393511865336853577019)
        ·
          refine ⟨1326590267798005280365529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884393511865336853577019 1326590267798005280365529)
          ·
            refine ⟨994942700848503960274147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1326590267798005280365529 994942700848503960274147)
            ·
              refine ⟨1492414051272755940411221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 994942700848503960274147 1492414051272755940411221)
              ·
                refine ⟨8744613581676304338347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1492414051272755940411221 8744613581676304338347)
                ·
                  rfl

theorem cell23_459812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 9].length) (baseStart_459812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459812 prefixEnd_459812 := by exact prefixLift 459812
  have htrace : WordTrace (prefixWord ++ tailWord_459812) baseStart_459812 baseEnd_459812 := by
    simpa [prefixWord, tailWord_459812, baseEnd_459812] using wordTrace_append hprefix tailTrace_459812
  have hstable : (prefixWord ++ tailWord_459812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459812).length < 2 ^ (prefixWord ++ tailWord_459812).sum := by decide
  have hdescent : baseEnd_459812 < baseStart_459812 := by decide
  rcases family_descends (prefixWord ++ tailWord_459812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459839 : List Nat := [1, 1, 2, 2, 3, 1, 1, 6, 2, 1, 3]
def baseStart_459839 : Nat := 118140960795 + 459839 * 2 ^ 59
def prefixEnd_459839 : Nat := 4983230072969 + 3 ^ 40 * 459839 * 2
def baseEnd_459839 : Nat := 236118430682931611497745

theorem tailTrace_459839 : CollatzResearch.WordTrace tailWord_459839 prefixEnd_459839 236118430682931611497745 := by
  unfold tailWord_459839
  simp only [CollatzResearch.WordTrace]
  refine ⟨16771706181089312093878571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11181137454059541395919047 16771706181089312093878571)
  ·
    refine ⟨25157559271633968140817857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16771706181089312093878571 25157559271633968140817857)
    ·
      refine ⟨18868169453725476105613393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25157559271633968140817857 18868169453725476105613393)
      ·
        refine ⟨14151127090294107079210045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18868169453725476105613393 14151127090294107079210045)
        ·
          refine ⟨5306672658860290154703767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14151127090294107079210045 5306672658860290154703767)
          ·
            refine ⟨7960008988290435232055651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5306672658860290154703767 7960008988290435232055651)
            ·
              refine ⟨11940013482435652848083477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7960008988290435232055651 11940013482435652848083477)
              ·
                refine ⟨559688131989171227253913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11940013482435652848083477 559688131989171227253913)
                ·
                  refine ⟨419766098991878420440435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 559688131989171227253913 419766098991878420440435)
                  ·
                    refine ⟨629649148487817630660653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 419766098991878420440435 629649148487817630660653)
                    ·
                      refine ⟨236118430682931611497745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 629649148487817630660653 236118430682931611497745)
                      ·
                        rfl

theorem cell23_459839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2, 1, 3].length) (baseStart_459839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459839 prefixEnd_459839 := by exact prefixLift 459839
  have htrace : WordTrace (prefixWord ++ tailWord_459839) baseStart_459839 baseEnd_459839 := by
    simpa [prefixWord, tailWord_459839, baseEnd_459839] using wordTrace_append hprefix tailTrace_459839
  have hstable : (prefixWord ++ tailWord_459839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459839).length < 2 ^ (prefixWord ++ tailWord_459839).sum := by decide
  have hdescent : baseEnd_459839 < baseStart_459839 := by decide
  rcases family_descends (prefixWord ++ tailWord_459839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459879 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 3, 4, 2]
def baseStart_459879 : Nat := 118140960795 + 459879 * 2 ^ 59
def prefixEnd_459879 : Nat := 4983230072969 + 3 ^ 40 * 459879 * 2
def baseEnd_459879 : Nat := 236138969909111454997561

theorem tailTrace_459879 : CollatzResearch.WordTrace tailWord_459879 prefixEnd_459879 236138969909111454997561 := by
  unfold tailWord_459879
  simp only [CollatzResearch.WordTrace]
  refine ⟨16773165100944398925334691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11182110067296265950223127 16773165100944398925334691)
  ·
    refine ⟨25159747651416598388002037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16773165100944398925334691 25159747651416598388002037)
    ·
      refine ⟨2358726342320306098875191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25159747651416598388002037 2358726342320306098875191)
      ·
        refine ⟨3538089513480459148312787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2358726342320306098875191 3538089513480459148312787)
        ·
          refine ⟨5307134270220688722469181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3538089513480459148312787 5307134270220688722469181)
          ·
            refine ⟨1990175351332758270925943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5307134270220688722469181 1990175351332758270925943)
            ·
              refine ⟨2985263026999137406388915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1990175351332758270925943 2985263026999137406388915)
              ·
                refine ⟨4477894540498706109583373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2985263026999137406388915 4477894540498706109583373)
                ·
                  refine ⟨1679210452687014791093765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4477894540498706109583373 1679210452687014791093765)
                  ·
                    refine ⟨314851959878815273330081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1679210452687014791093765 314851959878815273330081)
                    ·
                      refine ⟨236138969909111454997561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 314851959878815273330081 236138969909111454997561)
                      ·
                        rfl

theorem cell23_459879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_459879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459879 prefixEnd_459879 := by exact prefixLift 459879
  have htrace : WordTrace (prefixWord ++ tailWord_459879) baseStart_459879 baseEnd_459879 := by
    simpa [prefixWord, tailWord_459879, baseEnd_459879] using wordTrace_append hprefix tailTrace_459879
  have hstable : (prefixWord ++ tailWord_459879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459879).length < 2 ^ (prefixWord ++ tailWord_459879).sum := by decide
  have hdescent : baseEnd_459879 < baseStart_459879 := by decide
  rcases family_descends (prefixWord ++ tailWord_459879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459896 : List Nat := [2, 1, 2, 1, 1, 1, 5, 4, 2, 2, 2]
def baseStart_459896 : Nat := 118140960795 + 459896 * 2 ^ 59
def prefixEnd_459896 : Nat := 4983230072969 + 3 ^ 40 * 459896 * 2
def baseEnd_459896 : Nat := 236147699080237888484983

theorem tailTrace_459896 : CollatzResearch.WordTrace tailWord_459896 prefixEnd_459896 236147699080237888484983 := by
  unfold tailWord_459896
  simp only [CollatzResearch.WordTrace]
  refine ⟨8386892570941405414351771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11182523427921873885802361 8386892570941405414351771)
  ·
    refine ⟨12580338856412108121527657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8386892570941405414351771 12580338856412108121527657)
    ·
      refine ⟨9435254142309081091145743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12580338856412108121527657 9435254142309081091145743)
      ·
        refine ⟨14152881213463621636718615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9435254142309081091145743 14152881213463621636718615)
        ·
          refine ⟨21229321820195432455077923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14152881213463621636718615 21229321820195432455077923)
          ·
            refine ⟨31843982730293148682616885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21229321820195432455077923 31843982730293148682616885)
            ·
              refine ⟨2985373380964982688995333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31843982730293148682616885 2985373380964982688995333)
              ·
                refine ⟨559757508930934254186625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2985373380964982688995333 559757508930934254186625)
                ·
                  refine ⟨419818131698200690639969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 559757508930934254186625 419818131698200690639969)
                  ·
                    refine ⟨314863598773650517979977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 419818131698200690639969 314863598773650517979977)
                    ·
                      refine ⟨236147699080237888484983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 314863598773650517979977 236147699080237888484983)
                      ·
                        rfl

theorem cell23_459896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 2, 2, 2].length) (baseStart_459896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459896 prefixEnd_459896 := by exact prefixLift 459896
  have htrace : WordTrace (prefixWord ++ tailWord_459896) baseStart_459896 baseEnd_459896 := by
    simpa [prefixWord, tailWord_459896, baseEnd_459896] using wordTrace_append hprefix tailTrace_459896
  have hstable : (prefixWord ++ tailWord_459896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459896).length < 2 ^ (prefixWord ++ tailWord_459896).sum := by decide
  have hdescent : baseEnd_459896 < baseStart_459896 := by decide
  rcases family_descends (prefixWord ++ tailWord_459896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459909 : List Nat := [1, 3, 1, 1, 6, 1, 1, 1, 2, 2, 4]
def baseStart_459909 : Nat := 118140960795 + 459909 * 2 ^ 59
def prefixEnd_459909 : Nat := 4983230072969 + 3 ^ 40 * 459909 * 2
def baseEnd_459909 : Nat := 236154374328746337622423

theorem tailTrace_459909 : CollatzResearch.WordTrace tailWord_459909 prefixEnd_459909 236154374328746337622423 := by
  unfold tailWord_459909
  simp only [CollatzResearch.WordTrace]
  refine ⟨16774259290835714048926781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11182839527223809365951187 16774259290835714048926781)
  ·
    refine ⟨6290347234063392768347543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16774259290835714048926781 6290347234063392768347543)
    ·
      refine ⟨9435520851095089152521315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6290347234063392768347543 9435520851095089152521315)
      ·
        refine ⟨14153281276642633728781973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9435520851095089152521315 14153281276642633728781973)
        ·
          refine ⟨663435059842623456036655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14153281276642633728781973 663435059842623456036655)
          ·
            refine ⟨995152589763935184054983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663435059842623456036655 995152589763935184054983)
            ·
              refine ⟨1492728884645902776082475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 995152589763935184054983 1492728884645902776082475)
              ·
                refine ⟨2239093326968854164123713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1492728884645902776082475 2239093326968854164123713)
                ·
                  refine ⟨1679319995226640623092785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2239093326968854164123713 1679319995226640623092785)
                  ·
                    refine ⟨1259489996419980467319589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1679319995226640623092785 1259489996419980467319589)
                    ·
                      refine ⟨236154374328746337622423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1259489996419980467319589 236154374328746337622423)
                      ·
                        rfl

theorem cell23_459909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 2, 4].length) (baseStart_459909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459909 prefixEnd_459909 := by exact prefixLift 459909
  have htrace : WordTrace (prefixWord ++ tailWord_459909) baseStart_459909 baseEnd_459909 := by
    simpa [prefixWord, tailWord_459909, baseEnd_459909] using wordTrace_append hprefix tailTrace_459909
  have hstable : (prefixWord ++ tailWord_459909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459909).length < 2 ^ (prefixWord ++ tailWord_459909).sum := by decide
  have hdescent : baseEnd_459909 < baseStart_459909 := by decide
  rcases family_descends (prefixWord ++ tailWord_459909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459946 : List Nat := [3, 1, 5, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_459946 : Nat := 118140960795 + 459946 * 2 ^ 59
def prefixEnd_459946 : Nat := 4983230072969 + 3 ^ 40 * 459946 * 2
def baseEnd_459946 : Nat := 236173373112962692859753

theorem tailTrace_459946 : CollatzResearch.WordTrace tailWord_459946 prefixEnd_459946 236173373112962692859753 := by
  unfold tailWord_459946
  simp only [CollatzResearch.WordTrace]
  refine ⟨4193902197925417342005923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11183739194467779578682461 4193902197925417342005923)
  ·
    refine ⟨6290853296888126013008885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4193902197925417342005923 6290853296888126013008885)
    ·
      refine ⟨589767496583261813719583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6290853296888126013008885 589767496583261813719583)
      ·
        refine ⟨884651244874892720579375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589767496583261813719583 884651244874892720579375)
        ·
          refine ⟨1326976867312339080869063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884651244874892720579375 1326976867312339080869063)
          ·
            refine ⟨1990465300968508621303595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326976867312339080869063 1990465300968508621303595)
            ·
              refine ⟨2985697951452762931955393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1990465300968508621303595 2985697951452762931955393)
              ·
                refine ⟨2239273463589572198966545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2985697951452762931955393 2239273463589572198966545)
                ·
                  refine ⟨1679455097692179149224909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2239273463589572198966545 1679455097692179149224909)
                  ·
                    refine ⟨629795661634567180959341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1679455097692179149224909 629795661634567180959341)
                    ·
                      refine ⟨236173373112962692859753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 629795661634567180959341 236173373112962692859753)
                      ·
                        rfl

theorem cell23_459946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_459946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_459946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_459946 prefixEnd_459946 := by exact prefixLift 459946
  have htrace : WordTrace (prefixWord ++ tailWord_459946) baseStart_459946 baseEnd_459946 := by
    simpa [prefixWord, tailWord_459946, baseEnd_459946] using wordTrace_append hprefix tailTrace_459946
  have hstable : (prefixWord ++ tailWord_459946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459946).length < 2 ^ (prefixWord ++ tailWord_459946).sum := by decide
  have hdescent : baseEnd_459946 < baseStart_459946 := by decide
  rcases family_descends (prefixWord ++ tailWord_459946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460013 : List Nat := [1, 5, 1, 2, 2, 3, 1, 1, 3, 4]
def baseStart_460013 : Nat := 118140960795 + 460013 * 2 ^ 59
def prefixEnd_460013 : Nat := 4983230072969 + 3 ^ 40 * 460013 * 2
def baseEnd_460013 : Nat := 78735925438937976907315

theorem tailTrace_460013 : CollatzResearch.WordTrace tailWord_460013 prefixEnd_460013 78735925438937976907315 := by
  unfold tailWord_460013
  simp only [CollatzResearch.WordTrace]
  refine ⟨16778052482458939810712693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11185368321639293207141795 16778052482458939810712693)
  ·
    refine ⟨1572942420230525607254315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16778052482458939810712693 1572942420230525607254315)
    ·
      refine ⟨2359413630345788410881473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1572942420230525607254315 2359413630345788410881473)
      ·
        refine ⟨1769560222759341308161105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2359413630345788410881473 1769560222759341308161105)
        ·
          refine ⟨1327170167069505981120829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1769560222759341308161105 1327170167069505981120829)
          ·
            refine ⟨497688812651064742920311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1327170167069505981120829 497688812651064742920311)
            ·
              refine ⟨746533218976597114380467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497688812651064742920311 746533218976597114380467)
              ·
                refine ⟨1119799828464895671570701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746533218976597114380467 1119799828464895671570701)
                ·
                  refine ⟨419924935674335876839013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1119799828464895671570701 419924935674335876839013)
                  ·
                    refine ⟨78735925438937976907315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 419924935674335876839013 78735925438937976907315)
                    ·
                      rfl

theorem cell23_460013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_460013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460013 prefixEnd_460013 := by exact prefixLift 460013
  have htrace : WordTrace (prefixWord ++ tailWord_460013) baseStart_460013 baseEnd_460013 := by
    simpa [prefixWord, tailWord_460013, baseEnd_460013] using wordTrace_append hprefix tailTrace_460013
  have hstable : (prefixWord ++ tailWord_460013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460013).length < 2 ^ (prefixWord ++ tailWord_460013).sum := by decide
  have hdescent : baseEnd_460013 < baseStart_460013 := by decide
  rcases family_descends (prefixWord ++ tailWord_460013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460053 : List Nat := [1, 3, 2, 1, 2, 1, 1, 7, 1, 1, 3]
def baseStart_460053 : Nat := 118140960795 + 460053 * 2 ^ 59
def prefixEnd_460053 : Nat := 4983230072969 + 3 ^ 40 * 460053 * 2
def baseEnd_460053 : Nat := 236228315542993774221761

theorem tailTrace_460053 : CollatzResearch.WordTrace tailWord_460053 prefixEnd_460053 236228315542993774221761 := by
  unfold tailWord_460053
  simp only [CollatzResearch.WordTrace]
  refine ⟨16779511402314026642168813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11186340934876017761445875 16779511402314026642168813)
  ·
    refine ⟨6292316775867759990813305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16779511402314026642168813 6292316775867759990813305)
    ·
      refine ⟨4719237581900819993109979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6292316775867759990813305 4719237581900819993109979)
      ·
        refine ⟨7078856372851229989664969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4719237581900819993109979 7078856372851229989664969)
        ·
          refine ⟨5309142279638422492248727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7078856372851229989664969 5309142279638422492248727)
          ·
            refine ⟨7963713419457633738373091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5309142279638422492248727 7963713419457633738373091)
            ·
              refine ⟨11945570129186450607559637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7963713419457633738373091 11945570129186450607559637)
              ·
                refine ⟨279974299902807436114679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11945570129186450607559637 279974299902807436114679)
                ·
                  refine ⟨419961449854211154172019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279974299902807436114679 419961449854211154172019)
                  ·
                    refine ⟨629942174781316731258029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 419961449854211154172019 629942174781316731258029)
                    ·
                      refine ⟨236228315542993774221761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 629942174781316731258029 236228315542993774221761)
                      ·
                        rfl

theorem cell23_460053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7, 1, 1, 3].length) (baseStart_460053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460053 prefixEnd_460053 := by exact prefixLift 460053
  have htrace : WordTrace (prefixWord ++ tailWord_460053) baseStart_460053 baseEnd_460053 := by
    simpa [prefixWord, tailWord_460053, baseEnd_460053] using wordTrace_append hprefix tailTrace_460053
  have hstable : (prefixWord ++ tailWord_460053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460053).length < 2 ^ (prefixWord ++ tailWord_460053).sum := by decide
  have hdescent : baseEnd_460053 < baseStart_460053 := by decide
  rcases family_descends (prefixWord ++ tailWord_460053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460096 : List Nat := [2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 3]
def baseStart_460096 : Nat := 118140960795 + 460096 * 2 ^ 59
def prefixEnd_460096 : Nat := 4983230072969 + 3 ^ 40 * 460096 * 2
def baseEnd_460096 : Nat := 236250395211137105984063

theorem tailTrace_460096 : CollatzResearch.WordTrace tailWord_460096 prefixEnd_460096 236250395211137105984063 := by
  unfold tailWord_460096
  simp only [CollatzResearch.WordTrace]
  refine ⟨8390539870579122492992071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11187386494105496657322761 8390539870579122492992071)
  ·
    refine ⟨12585809805868683739488107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8390539870579122492992071 12585809805868683739488107)
    ·
      refine ⟨18878714708803025609232161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12585809805868683739488107 18878714708803025609232161)
      ·
        refine ⟨14159036031602269206924121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18878714708803025609232161 14159036031602269206924121)
        ·
          refine ⟨10619277023701701905193091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14159036031602269206924121 10619277023701701905193091)
          ·
            refine ⟨15928915535552552857789637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10619277023701701905193091 15928915535552552857789637)
            ·
              refine ⟨2986671662916103660835557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15928915535552552857789637 2986671662916103660835557)
              ·
                refine ⟨560000936796769436406667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2986671662916103660835557 560000936796769436406667)
                ·
                  refine ⟨840001405195154154610001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 560000936796769436406667 840001405195154154610001)
                  ·
                    refine ⟨630001053896365615957501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 840001405195154154610001 630001053896365615957501)
                    ·
                      refine ⟨236250395211137105984063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 630001053896365615957501 236250395211137105984063)
                      ·
                        rfl

theorem cell23_460096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 3].length) (baseStart_460096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460096 prefixEnd_460096 := by exact prefixLift 460096
  have htrace : WordTrace (prefixWord ++ tailWord_460096) baseStart_460096 baseEnd_460096 := by
    simpa [prefixWord, tailWord_460096, baseEnd_460096] using wordTrace_append hprefix tailTrace_460096
  have hstable : (prefixWord ++ tailWord_460096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460096).length < 2 ^ (prefixWord ++ tailWord_460096).sum := by decide
  have hdescent : baseEnd_460096 < baseStart_460096 := by decide
  rcases family_descends (prefixWord ++ tailWord_460096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460153 : List Nat := [1, 2, 1, 3, 2, 1, 3, 4, 1, 3, 2]
def baseStart_460153 : Nat := 118140960795 + 460153 * 2 ^ 59
def prefixEnd_460153 : Nat := 4983230072969 + 3 ^ 40 * 460153 * 2
def baseEnd_460153 : Nat := 236279663608443382971301

theorem tailTrace_460153 : CollatzResearch.WordTrace tailWord_460153 prefixEnd_460153 236279663608443382971301 := by
  unfold tailWord_460153
  simp only [CollatzResearch.WordTrace]
  refine ⟨16783158701951743720809113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11188772467967829147206075 16783158701951743720809113)
  ·
    refine ⟨12587369026463807790606835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16783158701951743720809113 12587369026463807790606835)
    ·
      refine ⟨18881053539695711685910253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12587369026463807790606835 18881053539695711685910253)
      ·
        refine ⟨7080395077385891882216345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18881053539695711685910253 7080395077385891882216345)
        ·
          refine ⟨5310296308039418911662259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7080395077385891882216345 5310296308039418911662259)
          ·
            refine ⟨7965444462059128367493389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5310296308039418911662259 7965444462059128367493389)
            ·
              refine ⟨2987041673272173137810021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7965444462059128367493389 2987041673272173137810021)
              ·
                refine ⟨560070313738532463339379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2987041673272173137810021 560070313738532463339379)
                ·
                  refine ⟨840105470607798695009069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 560070313738532463339379 840105470607798695009069)
                  ·
                    refine ⟨315039551477924510628401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 840105470607798695009069 315039551477924510628401)
                    ·
                      refine ⟨236279663608443382971301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 315039551477924510628401 236279663608443382971301)
                      ·
                        rfl

theorem cell23_460153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 3, 2].length) (baseStart_460153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460153 prefixEnd_460153 := by exact prefixLift 460153
  have htrace : WordTrace (prefixWord ++ tailWord_460153) baseStart_460153 baseEnd_460153 := by
    simpa [prefixWord, tailWord_460153, baseEnd_460153] using wordTrace_append hprefix tailTrace_460153
  have hstable : (prefixWord ++ tailWord_460153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460153).length < 2 ^ (prefixWord ++ tailWord_460153).sum := by decide
  have hdescent : baseEnd_460153 < baseStart_460153 := by decide
  rcases family_descends (prefixWord ++ tailWord_460153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460161 : List Nat := [1, 2, 4, 3, 3, 1, 1, 3, 1, 2, 2]
def baseStart_460161 : Nat := 118140960795 + 460161 * 2 ^ 59
def prefixEnd_460161 : Nat := 4983230072969 + 3 ^ 40 * 460161 * 2
def baseEnd_460161 : Nat := 236283771453679351671265

theorem tailTrace_460161 : CollatzResearch.WordTrace tailWord_460161 prefixEnd_460161 236283771453679351671265 := by
  unfold tailWord_460161
  simp only [CollatzResearch.WordTrace]
  refine ⟨16783450485922761087100337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11188966990615174058066891 16783450485922761087100337)
  ·
    refine ⟨12587587864442070815325253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16783450485922761087100337 12587587864442070815325253)
    ·
      refine ⟨2360172724582888277873485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12587587864442070815325253 2360172724582888277873485)
      ·
        refine ⟨885064771718583104202557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2360172724582888277873485 885064771718583104202557)
        ·
          refine ⟨331899289394468664075959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 885064771718583104202557 331899289394468664075959)
          ·
            refine ⟨497848934091702996113939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331899289394468664075959 497848934091702996113939)
            ·
              refine ⟨746773401137554494170909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497848934091702996113939 746773401137554494170909)
              ·
                refine ⟨280040025426582935314091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 746773401137554494170909 280040025426582935314091)
                ·
                  refine ⟨420060038139874402971137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 280040025426582935314091 420060038139874402971137)
                  ·
                    refine ⟨315045028604905802228353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 420060038139874402971137 315045028604905802228353)
                    ·
                      refine ⟨236283771453679351671265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 315045028604905802228353 236283771453679351671265)
                      ·
                        rfl

theorem cell23_460161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_460161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460161 prefixEnd_460161 := by exact prefixLift 460161
  have htrace : WordTrace (prefixWord ++ tailWord_460161) baseStart_460161 baseEnd_460161 := by
    simpa [prefixWord, tailWord_460161, baseEnd_460161] using wordTrace_append hprefix tailTrace_460161
  have hstable : (prefixWord ++ tailWord_460161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460161).length < 2 ^ (prefixWord ++ tailWord_460161).sum := by decide
  have hdescent : baseEnd_460161 < baseStart_460161 := by decide
  rcases family_descends (prefixWord ++ tailWord_460161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460186 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3]
def baseStart_460186 : Nat := 118140960795 + 460186 * 2 ^ 59
def prefixEnd_460186 : Nat := 4983230072969 + 3 ^ 40 * 460186 * 2
def baseEnd_460186 : Nat := 236296608470041753858649

theorem tailTrace_460186 : CollatzResearch.WordTrace tailWord_460186 prefixEnd_460186 236296608470041753858649 := by
  unfold tailWord_460186
  simp only [CollatzResearch.WordTrace]
  refine ⟨4196090577708047589190103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11189574873888126904506941 4196090577708047589190103)
  ·
    refine ⟨6294135866562071383785155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4196090577708047589190103 6294135866562071383785155)
    ·
      refine ⟨9441203799843107075677733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6294135866562071383785155 9441203799843107075677733)
      ·
        refine ⟨1770225712470582576689575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9441203799843107075677733 1770225712470582576689575)
        ·
          refine ⟨2655338568705873865034363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1770225712470582576689575 2655338568705873865034363)
          ·
            refine ⟨3983007853058810797551545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2655338568705873865034363 3983007853058810797551545)
            ·
              refine ⟨2987255889794108098163659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3983007853058810797551545 2987255889794108098163659)
              ·
                refine ⟨4480883834691162147245489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2987255889794108098163659 4480883834691162147245489)
                ·
                  refine ⟨3360662876018371610434117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4480883834691162147245489 3360662876018371610434117)
                  ·
                    refine ⟨630124289253444676956397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3360662876018371610434117 630124289253444676956397)
                    ·
                      refine ⟨236296608470041753858649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 630124289253444676956397 236296608470041753858649)
                      ·
                        rfl

theorem cell23_460186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_460186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460186 prefixEnd_460186 := by exact prefixLift 460186
  have htrace : WordTrace (prefixWord ++ tailWord_460186) baseStart_460186 baseEnd_460186 := by
    simpa [prefixWord, tailWord_460186, baseEnd_460186] using wordTrace_append hprefix tailTrace_460186
  have hstable : (prefixWord ++ tailWord_460186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460186).length < 2 ^ (prefixWord ++ tailWord_460186).sum := by decide
  have hdescent : baseEnd_460186 < baseStart_460186 := by decide
  rcases family_descends (prefixWord ++ tailWord_460186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460273 : List Nat := [1, 2, 2, 2, 3, 2, 3, 1, 2, 1, 4]
def baseStart_460273 : Nat := 118140960795 + 460273 * 2 ^ 59
def prefixEnd_460273 : Nat := 4983230072969 + 3 ^ 40 * 460273 * 2
def baseEnd_460273 : Nat := 236341281286982913470749

theorem tailTrace_460273 : CollatzResearch.WordTrace tailWord_460273 prefixEnd_460273 236341281286982913470749 := by
  unfold tailWord_460273
  simp only [CollatzResearch.WordTrace]
  refine ⟨16787535461517004215177473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11191690307678002810118315 16787535461517004215177473)
  ·
    refine ⟨12590651596137753161383105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16787535461517004215177473 12590651596137753161383105)
    ·
      refine ⟨9442988697103314871037329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12590651596137753161383105 9442988697103314871037329)
      ·
        refine ⟨7082241522827486153277997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9442988697103314871037329 7082241522827486153277997)
        ·
          refine ⟨2655840571060307307479249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7082241522827486153277997 2655840571060307307479249)
          ·
            refine ⟨1991880428295230480609437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2655840571060307307479249 1991880428295230480609437)
            ·
              refine ⟨746955160610711430228539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1991880428295230480609437 746955160610711430228539)
              ·
                refine ⟨1120432740916067145342809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746955160610711430228539 1120432740916067145342809)
                ·
                  refine ⟨840324555687050359007107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1120432740916067145342809 840324555687050359007107)
                  ·
                    refine ⟨1260486833530575538510661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 840324555687050359007107 1260486833530575538510661)
                    ·
                      refine ⟨236341281286982913470749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1260486833530575538510661 236341281286982913470749)
                      ·
                        rfl

theorem cell23_460273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_460273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460273 prefixEnd_460273 := by exact prefixLift 460273
  have htrace : WordTrace (prefixWord ++ tailWord_460273) baseStart_460273 baseEnd_460273 := by
    simpa [prefixWord, tailWord_460273, baseEnd_460273] using wordTrace_append hprefix tailTrace_460273
  have hstable : (prefixWord ++ tailWord_460273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460273).length < 2 ^ (prefixWord ++ tailWord_460273).sum := by decide
  have hdescent : baseEnd_460273 < baseStart_460273 := by decide
  rcases family_descends (prefixWord ++ tailWord_460273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460300 : List Nat := [2, 2, 1, 2, 5, 1, 2, 1, 3, 4]
def baseStart_460300 : Nat := 118140960795 + 460300 * 2 ^ 59
def prefixEnd_460300 : Nat := 4983230072969 + 3 ^ 40 * 460300 * 2
def baseEnd_460300 : Nat := 78785048421551435944375

theorem tailTrace_460300 : CollatzResearch.WordTrace tailWord_460300 prefixEnd_460300 78785048421551435944375 := by
  unfold tailWord_460300
  simp only [CollatzResearch.WordTrace]
  refine ⟨8394260116209593913205177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11192346821612791884273569 8394260116209593913205177)
  ·
    refine ⟨6295695087157195434903883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8394260116209593913205177 6295695087157195434903883)
    ·
      refine ⟨9443542630735793152355825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6295695087157195434903883 9443542630735793152355825)
      ·
        refine ⟨7082656973051844864266869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9443542630735793152355825 7082656973051844864266869)
        ·
          refine ⟨663999091223610456025019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7082656973051844864266869 663999091223610456025019)
          ·
            refine ⟨995998636835415684037529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663999091223610456025019 995998636835415684037529)
            ·
              refine ⟨746998977626561763028147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 995998636835415684037529 746998977626561763028147)
              ·
                refine ⟨1120498466439842644542221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746998977626561763028147 1120498466439842644542221)
                ·
                  refine ⟨420186924914940991703333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1120498466439842644542221 420186924914940991703333)
                  ·
                    refine ⟨78785048421551435944375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 420186924914940991703333 78785048421551435944375)
                    ·
                      rfl

theorem cell23_460300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 3, 4].length) (baseStart_460300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460300 prefixEnd_460300 := by exact prefixLift 460300
  have htrace : WordTrace (prefixWord ++ tailWord_460300) baseStart_460300 baseEnd_460300 := by
    simpa [prefixWord, tailWord_460300, baseEnd_460300] using wordTrace_append hprefix tailTrace_460300
  have hstable : (prefixWord ++ tailWord_460300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460300).length < 2 ^ (prefixWord ++ tailWord_460300).sum := by decide
  have hdescent : baseEnd_460300 < baseStart_460300 := by decide
  rcases family_descends (prefixWord ++ tailWord_460300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460316 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_460316 : Nat := 118140960795 + 460316 * 2 ^ 59
def prefixEnd_460316 : Nat := 4983230072969 + 3 ^ 40 * 460316 * 2
def baseEnd_460316 : Nat := 236363360955126245233051

theorem tailTrace_460316 : CollatzResearch.WordTrace tailWord_460316 prefixEnd_460316 236363360955126245233051 := by
  unfold tailWord_460316
  simp only [CollatzResearch.WordTrace]
  refine ⟨8394551900180611279496401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11192735866907481705995201 8394551900180611279496401)
  ·
    refine ⟨6295913925135458459622301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8394551900180611279496401 6295913925135458459622301)
    ·
      refine ⟨2360967721925796922358363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6295913925135458459622301 2360967721925796922358363)
      ·
        refine ⟨3541451582888695383537545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2360967721925796922358363 3541451582888695383537545)
        ·
          refine ⟨2656088687166521537653159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3541451582888695383537545 2656088687166521537653159)
          ·
            refine ⟨3984133030749782306479739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2656088687166521537653159 3984133030749782306479739)
            ·
              refine ⟨5976199546124673459719609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3984133030749782306479739 5976199546124673459719609)
              ·
                refine ⟨4482149659593505094789707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5976199546124673459719609 4482149659593505094789707)
                ·
                  refine ⟨6723224489390257642184561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4482149659593505094789707 6723224489390257642184561)
                  ·
                    refine ⟨5042418367042693231638421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6723224489390257642184561 5042418367042693231638421)
                    ·
                      refine ⟨236363360955126245233051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5042418367042693231638421 236363360955126245233051)
                      ·
                        rfl

theorem cell23_460316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_460316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460316 prefixEnd_460316 := by exact prefixLift 460316
  have htrace : WordTrace (prefixWord ++ tailWord_460316) baseStart_460316 baseEnd_460316 := by
    simpa [prefixWord, tailWord_460316, baseEnd_460316] using wordTrace_append hprefix tailTrace_460316
  have hstable : (prefixWord ++ tailWord_460316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460316).length < 2 ^ (prefixWord ++ tailWord_460316).sum := by decide
  have hdescent : baseEnd_460316 < baseStart_460316 := by decide
  rcases family_descends (prefixWord ++ tailWord_460316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460334 : List Nat := [4, 1, 3, 1, 2, 3, 1, 3, 1, 4]
def baseStart_460334 : Nat := 118140960795 + 460334 * 2 ^ 59
def prefixEnd_460334 : Nat := 4983230072969 + 3 ^ 40 * 460334 * 2
def baseEnd_460334 : Nat := 78790867868969058269323

theorem tailTrace_460334 : CollatzResearch.WordTrace tailWord_460334 prefixEnd_460334 78790867868969058269323 := by
  unfold tailWord_460334
  simp only [CollatzResearch.WordTrace]
  refine ⟨2098720039287001454143507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11193173542864007755432037 2098720039287001454143507)
  ·
    refine ⟨3148080058930502181215261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2098720039287001454143507 3148080058930502181215261)
    ·
      refine ⟨1180530022098938317955723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3148080058930502181215261 1180530022098938317955723)
      ·
        refine ⟨1770795033148407476933585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1180530022098938317955723 1770795033148407476933585)
        ·
          refine ⟨1328096274861305607700189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1770795033148407476933585 1328096274861305607700189)
          ·
            refine ⟨498036103072989602887571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1328096274861305607700189 498036103072989602887571)
            ·
              refine ⟨747054154609484404331357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498036103072989602887571 747054154609484404331357)
              ·
                refine ⟨280145307978556651624259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 747054154609484404331357 280145307978556651624259)
                ·
                  refine ⟨420217961967834977436389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 280145307978556651624259 420217961967834977436389)
                  ·
                    refine ⟨78790867868969058269323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 420217961967834977436389 78790867868969058269323)
                    ·
                      rfl

theorem cell23_460334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_460334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460334 prefixEnd_460334 := by exact prefixLift 460334
  have htrace : WordTrace (prefixWord ++ tailWord_460334) baseStart_460334 baseEnd_460334 := by
    simpa [prefixWord, tailWord_460334, baseEnd_460334] using wordTrace_append hprefix tailTrace_460334
  have hstable : (prefixWord ++ tailWord_460334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460334).length < 2 ^ (prefixWord ++ tailWord_460334).sum := by decide
  have hdescent : baseEnd_460334 < baseStart_460334 := by decide
  rcases family_descends (prefixWord ++ tailWord_460334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460343 : List Nat := [1, 1, 3, 1, 2, 4, 2, 3, 1, 5]
def baseStart_460343 : Nat := 118140960795 + 460343 * 2 ^ 59
def prefixEnd_460343 : Nat := 4983230072969 + 3 ^ 40 * 460343 * 2
def baseEnd_460343 : Nat := 78792408310932546531809

theorem tailTrace_460343 : CollatzResearch.WordTrace tailWord_460343 prefixEnd_460343 78792408310932546531809 := by
  unfold tailWord_460343
  simp only [CollatzResearch.WordTrace]
  refine ⟨16790088571263406170225683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11193392380842270780150455 16790088571263406170225683)
  ·
    refine ⟨25185132856895109255338525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16790088571263406170225683 25185132856895109255338525)
    ·
      refine ⟨9444424821335665970751947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25185132856895109255338525 9444424821335665970751947)
      ·
        refine ⟨14166637232003498956127921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9444424821335665970751947 14166637232003498956127921)
        ·
          refine ⟨10624977924002624217095941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14166637232003498956127921 10624977924002624217095941)
          ·
            refine ⟨1992183360750492040705489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10624977924002624217095941 1992183360750492040705489)
            ·
              refine ⟨1494137520562869030529117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1992183360750492040705489 1494137520562869030529117)
              ·
                refine ⟨560301570211075886448419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1494137520562869030529117 560301570211075886448419)
                ·
                  refine ⟨840452355316613829672629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 560301570211075886448419 840452355316613829672629)
                  ·
                    refine ⟨78792408310932546531809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 840452355316613829672629 78792408310932546531809)
                    ·
                      rfl

theorem cell23_460343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 5].length) (baseStart_460343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460343 prefixEnd_460343 := by exact prefixLift 460343
  have htrace : WordTrace (prefixWord ++ tailWord_460343) baseStart_460343 baseEnd_460343 := by
    simpa [prefixWord, tailWord_460343, baseEnd_460343] using wordTrace_append hprefix tailTrace_460343
  have hstable : (prefixWord ++ tailWord_460343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460343).length < 2 ^ (prefixWord ++ tailWord_460343).sum := by decide
  have hdescent : baseEnd_460343 < baseStart_460343 := by decide
  rcases family_descends (prefixWord ++ tailWord_460343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460380 : List Nat := [2, 2, 4, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_460380 : Nat := 118140960795 + 460380 * 2 ^ 59
def prefixEnd_460380 : Nat := 4983230072969 + 3 ^ 40 * 460380 * 2
def baseEnd_460380 : Nat := 236396223717013994832757

theorem tailTrace_460380 : CollatzResearch.WordTrace tailWord_460380 prefixEnd_460380 236396223717013994832757 := by
  unfold tailWord_460380
  simp only [CollatzResearch.WordTrace]
  refine ⟨8395719036064680744661297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11194292048086240992881729 8395719036064680744661297)
  ·
    refine ⟨6296789277048510558495973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8395719036064680744661297 6296789277048510558495973)
    ·
      refine ⟨1180647989446595729717995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6296789277048510558495973 1180647989446595729717995)
      ·
        refine ⟨1770971984169893594576993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1180647989446595729717995 1770971984169893594576993)
        ·
          refine ⟨1328228988127420195932745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1770971984169893594576993 1328228988127420195932745)
          ·
            refine ⟨996171741095565146949559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1328228988127420195932745 996171741095565146949559)
            ·
              refine ⟨1494257611643347720424339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996171741095565146949559 1494257611643347720424339)
              ·
                refine ⟨2241386417465021580636509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1494257611643347720424339 2241386417465021580636509)
                ·
                  refine ⟨840519906549383092738691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2241386417465021580636509 840519906549383092738691)
                  ·
                    refine ⟨1260779859824074639108037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 840519906549383092738691 1260779859824074639108037)
                    ·
                      refine ⟨236396223717013994832757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1260779859824074639108037 236396223717013994832757)
                      ·
                        rfl

theorem cell23_460380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_460380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460380 prefixEnd_460380 := by exact prefixLift 460380
  have htrace : WordTrace (prefixWord ++ tailWord_460380) baseStart_460380 baseEnd_460380 := by
    simpa [prefixWord, tailWord_460380, baseEnd_460380] using wordTrace_append hprefix tailTrace_460380
  have hstable : (prefixWord ++ tailWord_460380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460380).length < 2 ^ (prefixWord ++ tailWord_460380).sum := by decide
  have hdescent : baseEnd_460380 < baseStart_460380 := by decide
  rcases family_descends (prefixWord ++ tailWord_460380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460400 : List Nat := [2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 5]
def baseStart_460400 : Nat := 118140960795 + 460400 * 2 ^ 59
def prefixEnd_460400 : Nat := 4983230072969 + 3 ^ 40 * 460400 * 2
def baseEnd_460400 : Nat := 236406493330103916582665

theorem tailTrace_460400 : CollatzResearch.WordTrace tailWord_460400 prefixEnd_460400 236406493330103916582665 := by
  unfold tailWord_460400
  simp only [CollatzResearch.WordTrace]
  refine ⟨8396083766028452452525327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11194778354704603270033769 8396083766028452452525327)
  ·
    refine ⟨12594125649042678678787991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8396083766028452452525327 12594125649042678678787991)
    ·
      refine ⟨18891188473564018018181987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12594125649042678678787991 18891188473564018018181987)
      ·
        refine ⟨28336782710346027027272981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18891188473564018018181987 28336782710346027027272981)
        ·
          refine ⟨1328286689547470016903421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28336782710346027027272981 1328286689547470016903421)
          ·
            refine ⟨498107508580301256338783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1328286689547470016903421 498107508580301256338783)
            ·
              refine ⟨747161262870451884508175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498107508580301256338783 747161262870451884508175)
              ·
                refine ⟨1120741894305677826762263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747161262870451884508175 1120741894305677826762263)
                ·
                  refine ⟨1681112841458516740143395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1120741894305677826762263 1681112841458516740143395)
                  ·
                    refine ⟨2521669262187775110215093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1681112841458516740143395 2521669262187775110215093)
                    ·
                      refine ⟨236406493330103916582665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2521669262187775110215093 236406493330103916582665)
                      ·
                        rfl

theorem cell23_460400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 5].length) (baseStart_460400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460400 prefixEnd_460400 := by exact prefixLift 460400
  have htrace : WordTrace (prefixWord ++ tailWord_460400) baseStart_460400 baseEnd_460400 := by
    simpa [prefixWord, tailWord_460400, baseEnd_460400] using wordTrace_append hprefix tailTrace_460400
  have hstable : (prefixWord ++ tailWord_460400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460400).length < 2 ^ (prefixWord ++ tailWord_460400).sum := by decide
  have hdescent : baseEnd_460400 < baseStart_460400 := by decide
  rcases family_descends (prefixWord ++ tailWord_460400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460416 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 1, 9]
def baseStart_460416 : Nat := 118140960795 + 460416 * 2 ^ 59
def prefixEnd_460416 : Nat := 4983230072969 + 3 ^ 40 * 460416 * 2
def baseEnd_460416 : Nat := 78804903006858617994197

theorem tailTrace_460416 : CollatzResearch.WordTrace tailWord_460416 prefixEnd_460416 78804903006858617994197 := by
  unfold tailWord_460416
  simp only [CollatzResearch.WordTrace]
  refine ⟨8396375549999469818816551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11195167399999293091755401 8396375549999469818816551)
  ·
    refine ⟨12594563324999204728224827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8396375549999469818816551 12594563324999204728224827)
    ·
      refine ⟨18891844987498807092337241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12594563324999204728224827 18891844987498807092337241)
      ·
        refine ⟨14168883740624105319252931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18891844987498807092337241 14168883740624105319252931)
        ·
          refine ⟨21253325610936157978879397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14168883740624105319252931 21253325610936157978879397)
          ·
            refine ⟨3984998552050529621039887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21253325610936157978879397 3984998552050529621039887)
            ·
              refine ⟨5977497828075794431559831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3984998552050529621039887 5977497828075794431559831)
              ·
                refine ⟨8966246742113691647339747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5977497828075794431559831 8966246742113691647339747)
                ·
                  refine ⟨13449370113170537471009621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8966246742113691647339747 13449370113170537471009621)
                  ·
                    refine ⟨78804903006858617994197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 13449370113170537471009621 78804903006858617994197)
                    ·
                      rfl

theorem cell23_460416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 1, 9].length) (baseStart_460416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460416 prefixEnd_460416 := by exact prefixLift 460416
  have htrace : WordTrace (prefixWord ++ tailWord_460416) baseStart_460416 baseEnd_460416 := by
    simpa [prefixWord, tailWord_460416, baseEnd_460416] using wordTrace_append hprefix tailTrace_460416
  have hstable : (prefixWord ++ tailWord_460416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460416).length < 2 ^ (prefixWord ++ tailWord_460416).sum := by decide
  have hdescent : baseEnd_460416 < baseStart_460416 := by decide
  rcases family_descends (prefixWord ++ tailWord_460416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460420 : List Nat := [2, 3, 2, 1, 4, 2, 1, 8]
def baseStart_460420 : Nat := 118140960795 + 460420 * 2 ^ 59
def prefixEnd_460420 : Nat := 4983230072969 + 3 ^ 40 * 460420 * 2
def baseEnd_460420 : Nat := 8756176405303475493799

theorem tailTrace_460420 : CollatzResearch.WordTrace tailWord_460420 prefixEnd_460420 8756176405303475493799 := by
  unfold tailWord_460420
  simp only [CollatzResearch.WordTrace]
  refine ⟨8396448495992224160389357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11195264661322965547185809 8396448495992224160389357)
  ·
    refine ⟨3148668185997084060146009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8396448495992224160389357 3148668185997084060146009)
    ·
      refine ⟨2361501139497813045109507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3148668185997084060146009 2361501139497813045109507)
      ·
        refine ⟨3542251709246719567664261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2361501139497813045109507 3542251709246719567664261)
        ·
          refine ⟨664172195483759918937049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3542251709246719567664261 664172195483759918937049)
          ·
            refine ⟨498129146612819939202787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 664172195483759918937049 498129146612819939202787)
            ·
              refine ⟨747193719919229908804181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498129146612819939202787 747193719919229908804181)
              ·
                refine ⟨8756176405303475493799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 747193719919229908804181 8756176405303475493799)
                ·
                  rfl

theorem cell23_460420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 8].length) (baseStart_460420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460420 prefixEnd_460420 := by exact prefixLift 460420
  have htrace : WordTrace (prefixWord ++ tailWord_460420) baseStart_460420 baseEnd_460420 := by
    simpa [prefixWord, tailWord_460420, baseEnd_460420] using wordTrace_append hprefix tailTrace_460420
  have hstable : (prefixWord ++ tailWord_460420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460420).length < 2 ^ (prefixWord ++ tailWord_460420).sum := by decide
  have hdescent : baseEnd_460420 < baseStart_460420 := by decide
  rcases family_descends (prefixWord ++ tailWord_460420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460430 : List Nat := [4, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3]
def baseStart_460430 : Nat := 118140960795 + 460430 * 2 ^ 59
def prefixEnd_460430 : Nat := 4983230072969 + 3 ^ 40 * 460430 * 2
def baseEnd_460430 : Nat := 236421897749738799207527

theorem tailTrace_460430 : CollatzResearch.WordTrace tailWord_460430 prefixEnd_460430 236421897749738799207527 := by
  unfold tailWord_460430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2099157715243527503580343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11195507814632146685761829 2099157715243527503580343)
  ·
    refine ⟨3148736572865291255370515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2099157715243527503580343 3148736572865291255370515)
    ·
      refine ⟨4723104859297936883055773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3148736572865291255370515 4723104859297936883055773)
      ·
        refine ⟨1771164322236726331145915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4723104859297936883055773 1771164322236726331145915)
        ·
          refine ⟨2656746483355089496718873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1771164322236726331145915 2656746483355089496718873)
          ·
            refine ⟨1992559862516317122539155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2656746483355089496718873 1992559862516317122539155)
            ·
              refine ⟨2988839793774475683808733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1992559862516317122539155 2988839793774475683808733)
              ·
                refine ⟨1120814922665428381428275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2988839793774475683808733 1120814922665428381428275)
                ·
                  refine ⟨1681222383998142572142413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1120814922665428381428275 1681222383998142572142413)
                  ·
                    refine ⟨630458393999303464553405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1681222383998142572142413 630458393999303464553405)
                    ·
                      refine ⟨236421897749738799207527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 630458393999303464553405 236421897749738799207527)
                      ·
                        rfl

theorem cell23_460430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_460430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460430 prefixEnd_460430 := by exact prefixLift 460430
  have htrace : WordTrace (prefixWord ++ tailWord_460430) baseStart_460430 baseEnd_460430 := by
    simpa [prefixWord, tailWord_460430, baseEnd_460430] using wordTrace_append hprefix tailTrace_460430
  have hstable : (prefixWord ++ tailWord_460430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460430).length < 2 ^ (prefixWord ++ tailWord_460430).sum := by decide
  have hdescent : baseEnd_460430 < baseStart_460430 := by decide
  rcases family_descends (prefixWord ++ tailWord_460430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460473 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 1, 6, 3]
def baseStart_460473 : Nat := 118140960795 + 460473 * 2 ^ 59
def prefixEnd_460473 : Nat := 4983230072969 + 3 ^ 40 * 460473 * 2
def baseEnd_460473 : Nat := 236443977417882130969829

theorem tailTrace_460473 : CollatzResearch.WordTrace tailWord_460473 prefixEnd_460473 236443977417882130969829 := by
  unfold tailWord_460473
  simp only [CollatzResearch.WordTrace]
  refine ⟨16794830060792438372458073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11196553373861625581638715 16794830060792438372458073)
  ·
    refine ⟨12596122545594328779343555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16794830060792438372458073 12596122545594328779343555)
    ·
      refine ⟨18894183818391493169015333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12596122545594328779343555 18894183818391493169015333)
      ·
        refine ⟨3542659465948404969190375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18894183818391493169015333 3542659465948404969190375)
        ·
          refine ⟨5313989198922607453785563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3542659465948404969190375 5313989198922607453785563)
          ·
            refine ⟨7970983798383911180678345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5313989198922607453785563 7970983798383911180678345)
            ·
              refine ⟨5978237848787933385508759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7970983798383911180678345 5978237848787933385508759)
              ·
                refine ⟨8967356773181900078263139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5978237848787933385508759 8967356773181900078263139)
                ·
                  refine ⟨13451035159772850117394709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8967356773181900078263139 13451035159772850117394709)
                  ·
                    refine ⟨630517273114352349252877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13451035159772850117394709 630517273114352349252877)
                    ·
                      refine ⟨236443977417882130969829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 630517273114352349252877 236443977417882130969829)
                      ·
                        rfl

theorem cell23_460473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_460473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460473 prefixEnd_460473 := by exact prefixLift 460473
  have htrace : WordTrace (prefixWord ++ tailWord_460473) baseStart_460473 baseEnd_460473 := by
    simpa [prefixWord, tailWord_460473, baseEnd_460473] using wordTrace_append hprefix tailTrace_460473
  have hstable : (prefixWord ++ tailWord_460473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460473).length < 2 ^ (prefixWord ++ tailWord_460473).sum := by decide
  have hdescent : baseEnd_460473 < baseStart_460473 := by decide
  rcases family_descends (prefixWord ++ tailWord_460473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460523 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 4, 5]
def baseStart_460523 : Nat := 118140960795 + 460523 * 2 ^ 59
def prefixEnd_460523 : Nat := 4983230072969 + 3 ^ 40 * 460523 * 2
def baseEnd_460523 : Nat := 78823217150202311781533

theorem tailTrace_460523 : CollatzResearch.WordTrace tailWord_460523 prefixEnd_460523 78823217150202311781533 := by
  unfold tailWord_460523
  simp only [CollatzResearch.WordTrace]
  refine ⟨16796653710611296911778223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11197769140407531274518815 16796653710611296911778223)
  ·
    refine ⟨25194980565916945367667335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16796653710611296911778223 25194980565916945367667335)
    ·
      refine ⟨37792470848875418051501003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25194980565916945367667335 37792470848875418051501003)
      ·
        refine ⟨56688706273313127077251505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37792470848875418051501003 56688706273313127077251505)
        ·
          refine ⟨42516529704984845307938629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56688706273313127077251505 42516529704984845307938629)
          ·
            refine ⟨7971849319684658495238493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42516529704984845307938629 7971849319684658495238493)
            ·
              refine ⟨2989443494881746935714435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7971849319684658495238493 2989443494881746935714435)
              ·
                refine ⟨4484165242322620403571653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2989443494881746935714435 4484165242322620403571653)
                ·
                  refine ⟨840780982935491325669685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4484165242322620403571653 840780982935491325669685)
                  ·
                    refine ⟨78823217150202311781533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 840780982935491325669685 78823217150202311781533)
                    ·
                      rfl

theorem cell23_460523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 5].length) (baseStart_460523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460523 prefixEnd_460523 := by exact prefixLift 460523
  have htrace : WordTrace (prefixWord ++ tailWord_460523) baseStart_460523 baseEnd_460523 := by
    simpa [prefixWord, tailWord_460523, baseEnd_460523] using wordTrace_append hprefix tailTrace_460523
  have hstable : (prefixWord ++ tailWord_460523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460523).length < 2 ^ (prefixWord ++ tailWord_460523).sum := by decide
  have hdescent : baseEnd_460523 < baseStart_460523 := by decide
  rcases family_descends (prefixWord ++ tailWord_460523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460527 : List Nat := [1, 1, 2, 1, 5, 1, 5, 2, 5]
def baseStart_460527 : Nat := 118140960795 + 460527 * 2 ^ 59
def prefixEnd_460527 : Nat := 4983230072969 + 3 ^ 40 * 460527 * 2
def baseEnd_460527 : Nat := 26274633930358324410509

theorem tailTrace_460527 : CollatzResearch.WordTrace tailWord_460527 prefixEnd_460527 26274633930358324410509 := by
  unfold tailWord_460527
  simp only [CollatzResearch.WordTrace]
  refine ⟨16796799602596805594923835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11197866401731203729949223 16796799602596805594923835)
  ·
    refine ⟨25195199403895208392385753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16796799602596805594923835 25195199403895208392385753)
    ·
      refine ⟨18896399552921406294289315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25195199403895208392385753 18896399552921406294289315)
      ·
        refine ⟨28344599329382109441433973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18896399552921406294289315 28344599329382109441433973)
        ·
          refine ⟨2657306187129572760134435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28344599329382109441433973 2657306187129572760134435)
          ·
            refine ⟨3985959280694359140201653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2657306187129572760134435 3985959280694359140201653)
            ·
              refine ⟨373683682565096169393905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3985959280694359140201653 373683682565096169393905)
              ·
                refine ⟨280262761923822127045429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373683682565096169393905 280262761923822127045429)
                ·
                  refine ⟨26274633930358324410509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 280262761923822127045429 26274633930358324410509)
                  ·
                    rfl

theorem cell23_460527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2, 5].length) (baseStart_460527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460527 prefixEnd_460527 := by exact prefixLift 460527
  have htrace : WordTrace (prefixWord ++ tailWord_460527) baseStart_460527 baseEnd_460527 := by
    simpa [prefixWord, tailWord_460527, baseEnd_460527] using wordTrace_append hprefix tailTrace_460527
  have hstable : (prefixWord ++ tailWord_460527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460527).length < 2 ^ (prefixWord ++ tailWord_460527).sum := by decide
  have hdescent : baseEnd_460527 < baseStart_460527 := by decide
  rcases family_descends (prefixWord ++ tailWord_460527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460543 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 4]
def baseStart_460543 : Nat := 118140960795 + 460543 * 2 ^ 59
def prefixEnd_460543 : Nat := 4983230072969 + 3 ^ 40 * 460543 * 2
def baseEnd_460543 : Nat := 236479921063696857094507

theorem tailTrace_460543 : CollatzResearch.WordTrace tailWord_460543 prefixEnd_460543 236479921063696857094507 := by
  unfold tailWord_460543
  simp only [CollatzResearch.WordTrace]
  refine ⟨16797383170538840327506283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11198255447025893551670855 16797383170538840327506283)
  ·
    refine ⟨25196074755808260491259425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16797383170538840327506283 25196074755808260491259425)
    ·
      refine ⟨18897056066856195368444569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25196074755808260491259425 18897056066856195368444569)
      ·
        refine ⟨14172792050142146526333427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18897056066856195368444569 14172792050142146526333427)
        ·
          refine ⟨21259188075213219789500141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14172792050142146526333427 21259188075213219789500141)
          ·
            refine ⟨7972195528204957421062553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21259188075213219789500141 7972195528204957421062553)
            ·
              refine ⟨5979146646153718065796915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7972195528204957421062553 5979146646153718065796915)
              ·
                refine ⟨8968719969230577098695373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5979146646153718065796915 8968719969230577098695373)
                ·
                  refine ⟨3363269988461466412010765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8968719969230577098695373 3363269988461466412010765)
                  ·
                    refine ⟨1261226245673049904504037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3363269988461466412010765 1261226245673049904504037)
                    ·
                      refine ⟨236479921063696857094507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1261226245673049904504037 236479921063696857094507)
                      ·
                        rfl

theorem cell23_460543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_460543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460543 prefixEnd_460543 := by exact prefixLift 460543
  have htrace : WordTrace (prefixWord ++ tailWord_460543) baseStart_460543 baseEnd_460543 := by
    simpa [prefixWord, tailWord_460543, baseEnd_460543] using wordTrace_append hprefix tailTrace_460543
  have hstable : (prefixWord ++ tailWord_460543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460543).length < 2 ^ (prefixWord ++ tailWord_460543).sum := by decide
  have hdescent : baseEnd_460543 < baseStart_460543 := by decide
  rcases family_descends (prefixWord ++ tailWord_460543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460600 : List Nat := [2, 1, 2, 1, 3, 3, 2, 3, 6]
def baseStart_460600 : Nat := 118140960795 + 460600 * 2 ^ 59
def prefixEnd_460600 : Nat := 4983230072969 + 3 ^ 40 * 460600 * 2
def baseEnd_460600 : Nat := 26278798829000348231305

theorem tailTrace_460600 : CollatzResearch.WordTrace tailWord_460600 prefixEnd_460600 26278798829000348231305 := by
  unfold tailWord_460600
  simp only [CollatzResearch.WordTrace]
  refine ⟨8399731065666169531165627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11199641420888226041554169 8399731065666169531165627)
  ·
    refine ⟨12599596598499254296748441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8399731065666169531165627 12599596598499254296748441)
    ·
      refine ⟨9449697448874440722561331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12599596598499254296748441 9449697448874440722561331)
      ·
        refine ⟨14174546173311661083841997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9449697448874440722561331 14174546173311661083841997)
        ·
          refine ⟨5315454814991872906440749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14174546173311661083841997 5315454814991872906440749)
          ·
            refine ⟨1993295555621952339915281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5315454814991872906440749 1993295555621952339915281)
            ·
              refine ⟨1494971666716464254936461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1993295555621952339915281 1494971666716464254936461)
              ·
                refine ⟨560614375018674095601173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1494971666716464254936461 560614375018674095601173)
                ·
                  refine ⟨26278798829000348231305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 560614375018674095601173 26278798829000348231305)
                  ·
                    rfl

theorem cell23_460600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 6].length) (baseStart_460600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460600 prefixEnd_460600 := by exact prefixLift 460600
  have htrace : WordTrace (prefixWord ++ tailWord_460600) baseStart_460600 baseEnd_460600 := by
    simpa [prefixWord, tailWord_460600, baseEnd_460600] using wordTrace_append hprefix tailTrace_460600
  have hstable : (prefixWord ++ tailWord_460600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460600).length < 2 ^ (prefixWord ++ tailWord_460600).sum := by decide
  have hdescent : baseEnd_460600 < baseStart_460600 := by decide
  rcases family_descends (prefixWord ++ tailWord_460600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460621 : List Nat := [1, 6, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_460621 : Nat := 118140960795 + 460621 * 2 ^ 59
def prefixEnd_460621 : Nat := 4983230072969 + 3 ^ 40 * 460621 * 2
def baseEnd_460621 : Nat := 78839990851582517306383

theorem tailTrace_460621 : CollatzResearch.WordTrace tailWord_460621 prefixEnd_460621 78839990851582517306383 := by
  unfold tailWord_460621
  simp only [CollatzResearch.WordTrace]
  refine ⟨16800228064256259648845717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11200152042837506432563811 16800228064256259648845717)
  ·
    refine ⟨787510690512012171039643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16800228064256259648845717 787510690512012171039643)
    ·
      refine ⟨1181266035768018256559465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 787510690512012171039643 1181266035768018256559465)
      ·
        refine ⟨885949526826013692419599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1181266035768018256559465 885949526826013692419599)
        ·
          refine ⟨1328924290239020538629399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 885949526826013692419599 1328924290239020538629399)
          ·
            refine ⟨1993386435358530807944099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1328924290239020538629399 1993386435358530807944099)
            ·
              refine ⟨2990079653037796211916149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1993386435358530807944099 2990079653037796211916149)
              ·
                refine ⟨280319967472293394867139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2990079653037796211916149 280319967472293394867139)
                ·
                  refine ⟨420479951208440092300709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 280319967472293394867139 420479951208440092300709)
                  ·
                    refine ⟨78839990851582517306383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 420479951208440092300709 78839990851582517306383)
                    ·
                      rfl

theorem cell23_460621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_460621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460621 prefixEnd_460621 := by exact prefixLift 460621
  have htrace : WordTrace (prefixWord ++ tailWord_460621) baseStart_460621 baseEnd_460621 := by
    simpa [prefixWord, tailWord_460621, baseEnd_460621] using wordTrace_append hprefix tailTrace_460621
  have hstable : (prefixWord ++ tailWord_460621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460621).length < 2 ^ (prefixWord ++ tailWord_460621).sum := by decide
  have hdescent : baseEnd_460621 < baseStart_460621 := by decide
  rcases family_descends (prefixWord ++ tailWord_460621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460654 : List Nat := [4, 1, 2, 3, 1, 1, 1, 2, 1, 5, 2]
def baseStart_460654 : Nat := 118140960795 + 460654 * 2 ^ 59
def prefixEnd_460654 : Nat := 4983230072969 + 3 ^ 40 * 460654 * 2
def baseEnd_460654 : Nat := 236536917416345922806497

theorem tailTrace_460654 : CollatzResearch.WordTrace tailWord_460654 prefixEnd_460654 236536917416345922806497 := by
  unfold tailWord_460654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2100178959142088285599627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11200954448757804189864677 2100178959142088285599627)
  ·
    refine ⟨3150268438713132428399441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2100178959142088285599627 3150268438713132428399441)
    ·
      refine ⟨2362701329034849321299581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3150268438713132428399441 2362701329034849321299581)
      ·
        refine ⟨886012998388068495487343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2362701329034849321299581 886012998388068495487343)
        ·
          refine ⟨1329019497582102743231015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 886012998388068495487343 1329019497582102743231015)
          ·
            refine ⟨1993529246373154114846523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1329019497582102743231015 1993529246373154114846523)
            ·
              refine ⟨2990293869559731172269785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1993529246373154114846523 2990293869559731172269785)
              ·
                refine ⟨2242720402169798379202339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2990293869559731172269785 2242720402169798379202339)
                ·
                  refine ⟨3364080603254697568803509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2242720402169798379202339 3364080603254697568803509)
                  ·
                    refine ⟨315382556555127897075329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3364080603254697568803509 315382556555127897075329)
                    ·
                      refine ⟨236536917416345922806497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 315382556555127897075329 236536917416345922806497)
                      ·
                        rfl

theorem cell23_460654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_460654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460654 prefixEnd_460654 := by exact prefixLift 460654
  have htrace : WordTrace (prefixWord ++ tailWord_460654) baseStart_460654 baseEnd_460654 := by
    simpa [prefixWord, tailWord_460654, baseEnd_460654] using wordTrace_append hprefix tailTrace_460654
  have hstable : (prefixWord ++ tailWord_460654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460654).length < 2 ^ (prefixWord ++ tailWord_460654).sum := by decide
  have hdescent : baseEnd_460654 < baseStart_460654 := by decide
  rcases family_descends (prefixWord ++ tailWord_460654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460701 : List Nat := [1, 4, 2, 1, 2, 2, 3, 1, 3, 2, 2]
def baseStart_460701 : Nat := 118140960795 + 460701 * 2 ^ 59
def prefixEnd_460701 : Nat := 4983230072969 + 3 ^ 40 * 460701 * 2
def baseEnd_460701 : Nat := 236561051007107238918781

theorem tailTrace_460701 : CollatzResearch.WordTrace tailWord_460701 prefixEnd_460701 236561051007107238918781 := by
  unfold tailWord_460701
  simp only [CollatzResearch.WordTrace]
  refine ⟨16803145903966433311757957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11202097269310955541171971 16803145903966433311757957)
  ·
    refine ⟨3150589856993706245954617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16803145903966433311757957 3150589856993706245954617)
    ·
      refine ⟨2362942392745279684465963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3150589856993706245954617 2362942392745279684465963)
      ·
        refine ⟨3544413589117919526698945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2362942392745279684465963 3544413589117919526698945)
        ·
          refine ⟨2658310191838439645024209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3544413589117919526698945 2658310191838439645024209)
          ·
            refine ⟨1993732643878829733768157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2658310191838439645024209 1993732643878829733768157)
            ·
              refine ⟨747649741454561150163059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1993732643878829733768157 747649741454561150163059)
              ·
                refine ⟨1121474612181841725244589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747649741454561150163059 1121474612181841725244589)
                ·
                  refine ⟨420552979568190646966721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1121474612181841725244589 420552979568190646966721)
                  ·
                    refine ⟨315414734676142985225041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 420552979568190646966721 315414734676142985225041)
                    ·
                      refine ⟨236561051007107238918781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 315414734676142985225041 236561051007107238918781)
                      ·
                        rfl

theorem cell23_460701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_460701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460701 prefixEnd_460701 := by exact prefixLift 460701
  have htrace : WordTrace (prefixWord ++ tailWord_460701) baseStart_460701 baseEnd_460701 := by
    simpa [prefixWord, tailWord_460701, baseEnd_460701] using wordTrace_append hprefix tailTrace_460701
  have hstable : (prefixWord ++ tailWord_460701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460701).length < 2 ^ (prefixWord ++ tailWord_460701).sum := by decide
  have hdescent : baseEnd_460701 < baseStart_460701 := by decide
  rcases family_descends (prefixWord ++ tailWord_460701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460711 : List Nat := [1, 1, 6, 1, 2, 1, 4, 1, 2, 4]
def baseStart_460711 : Nat := 118140960795 + 460711 * 2 ^ 59
def prefixEnd_460711 : Nat := 4983230072969 + 3 ^ 40 * 460711 * 2
def baseEnd_460711 : Nat := 78855395271217399931245

theorem tailTrace_460711 : CollatzResearch.WordTrace tailWord_460711 prefixEnd_460711 78855395271217399931245 := by
  unfold tailWord_460711
  simp only [CollatzResearch.WordTrace]
  refine ⟨16803510633930205019621987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11202340422620136679747991 16803510633930205019621987)
  ·
    refine ⟨25205265950895307529432981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16803510633930205019621987 25205265950895307529432981)
    ·
      refine ⟨1181496841448217540442171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25205265950895307529432981 1181496841448217540442171)
      ·
        refine ⟨1772245262172326310663257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1181496841448217540442171 1772245262172326310663257)
        ·
          refine ⟨1329183946629244732997443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1772245262172326310663257 1329183946629244732997443)
          ·
            refine ⟨1993775919943867099496165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1329183946629244732997443 1993775919943867099496165)
            ·
              refine ⟨373832984989475081155531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1993775919943867099496165 373832984989475081155531)
              ·
                refine ⟨560749477484212621733297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373832984989475081155531 560749477484212621733297)
                ·
                  refine ⟨420562108113159466299973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 560749477484212621733297 420562108113159466299973)
                  ·
                    refine ⟨78855395271217399931245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 420562108113159466299973 78855395271217399931245)
                    ·
                      rfl

theorem cell23_460711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_460711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460711 prefixEnd_460711 := by exact prefixLift 460711
  have htrace : WordTrace (prefixWord ++ tailWord_460711) baseStart_460711 baseEnd_460711 := by
    simpa [prefixWord, tailWord_460711, baseEnd_460711] using wordTrace_append hprefix tailTrace_460711
  have hstable : (prefixWord ++ tailWord_460711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460711).length < 2 ^ (prefixWord ++ tailWord_460711).sum := by decide
  have hdescent : baseEnd_460711 < baseStart_460711 := by decide
  rcases family_descends (prefixWord ++ tailWord_460711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460718 : List Nat := [4, 1, 5, 1, 1, 1, 1, 1, 3, 1, 4]
def baseStart_460718 : Nat := 118140960795 + 460718 * 2 ^ 59
def prefixEnd_460718 : Nat := 4983230072969 + 3 ^ 40 * 460718 * 2
def baseEnd_460718 : Nat := 236569780178233672406203

theorem tailTrace_460718 : CollatzResearch.WordTrace tailWord_460718 prefixEnd_460718 236569780178233672406203 := by
  unfold tailWord_460718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2100470743113105651890851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11202510629936563476751205 2100470743113105651890851)
  ·
    refine ⟨3150706114669658477836277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2100470743113105651890851 3150706114669658477836277)
    ·
      refine ⟨295378698250280482297151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3150706114669658477836277 295378698250280482297151)
      ·
        refine ⟨443068047375420723445727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295378698250280482297151 443068047375420723445727)
        ·
          refine ⟨664602071063131085168591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443068047375420723445727 664602071063131085168591)
          ·
            refine ⟨996903106594696627752887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664602071063131085168591 996903106594696627752887)
            ·
              refine ⟨1495354659892044941629331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996903106594696627752887 1495354659892044941629331)
              ·
                refine ⟨2243031989838067412443997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1495354659892044941629331 2243031989838067412443997)
                ·
                  refine ⟨841136996189275279666499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2243031989838067412443997 841136996189275279666499)
                  ·
                    refine ⟨1261705494283912919499749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 841136996189275279666499 1261705494283912919499749)
                    ·
                      refine ⟨236569780178233672406203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1261705494283912919499749 236569780178233672406203)
                      ·
                        rfl

theorem cell23_460718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_460718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460718 prefixEnd_460718 := by exact prefixLift 460718
  have htrace : WordTrace (prefixWord ++ tailWord_460718) baseStart_460718 baseEnd_460718 := by
    simpa [prefixWord, tailWord_460718, baseEnd_460718] using wordTrace_append hprefix tailTrace_460718
  have hstable : (prefixWord ++ tailWord_460718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460718).length < 2 ^ (prefixWord ++ tailWord_460718).sum := by decide
  have hdescent : baseEnd_460718 < baseStart_460718 := by decide
  rcases family_descends (prefixWord ++ tailWord_460718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460721 : List Nat := [1, 2, 2, 4, 2, 3, 1, 2, 1, 2, 3]
def baseStart_460721 : Nat := 118140960795 + 460721 * 2 ^ 59
def prefixEnd_460721 : Nat := 4983230072969 + 3 ^ 40 * 460721 * 2
def baseEnd_460721 : Nat := 236571320620197160668689

theorem tailTrace_460721 : CollatzResearch.WordTrace tailWord_460721 prefixEnd_460721 236571320620197160668689 := by
  unfold tailWord_460721
  simp only [CollatzResearch.WordTrace]
  refine ⟨16803875363893976727486017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11202583575929317818324011 16803875363893976727486017)
  ·
    refine ⟨12602906522920482545614513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16803875363893976727486017 12602906522920482545614513)
    ·
      refine ⟨9452179892190361909210885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12602906522920482545614513 9452179892190361909210885)
      ·
        refine ⟨1772283729785692857977041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9452179892190361909210885 1772283729785692857977041)
        ·
          refine ⟨1329212797339269643482781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1772283729785692857977041 1329212797339269643482781)
          ·
            refine ⟨498454799002226116306043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1329212797339269643482781 498454799002226116306043)
            ·
              refine ⟨747682198503339174459065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498454799002226116306043 747682198503339174459065)
              ·
                refine ⟨560761648877504380844299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 747682198503339174459065 560761648877504380844299)
                ·
                  refine ⟨841142473316256571266449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 560761648877504380844299 841142473316256571266449)
                  ·
                    refine ⟨630856854987192428449837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 841142473316256571266449 630856854987192428449837)
                    ·
                      refine ⟨236571320620197160668689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 630856854987192428449837 236571320620197160668689)
                      ·
                        rfl

theorem cell23_460721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_460721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460721 prefixEnd_460721 := by exact prefixLift 460721
  have htrace : WordTrace (prefixWord ++ tailWord_460721) baseStart_460721 baseEnd_460721 := by
    simpa [prefixWord, tailWord_460721, baseEnd_460721] using wordTrace_append hprefix tailTrace_460721
  have hstable : (prefixWord ++ tailWord_460721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460721).length < 2 ^ (prefixWord ++ tailWord_460721).sum := by decide
  have hdescent : baseEnd_460721 < baseStart_460721 := by decide
  rcases family_descends (prefixWord ++ tailWord_460721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460730 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5]
def baseStart_460730 : Nat := 118140960795 + 460730 * 2 ^ 59
def prefixEnd_460730 : Nat := 4983230072969 + 3 ^ 40 * 460730 * 2
def baseEnd_460730 : Nat := 236575941946087625456147

theorem tailTrace_460730 : CollatzResearch.WordTrace tailWord_460730 prefixEnd_460730 236575941946087625456147 := by
  unfold tailWord_460730
  simp only [CollatzResearch.WordTrace]
  refine ⟨4201050905215342816140911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11202802413907580843042429 4201050905215342816140911)
  ·
    refine ⟨6301576357823014224211367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4201050905215342816140911 6301576357823014224211367)
    ·
      refine ⟨9452364536734521336317051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6301576357823014224211367 9452364536734521336317051)
      ·
        refine ⟨14178546805101782004475577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9452364536734521336317051 14178546805101782004475577)
        ·
          refine ⟨10633910103826336503356683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14178546805101782004475577 10633910103826336503356683)
          ·
            refine ⟨15950865155739504755035025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10633910103826336503356683 15950865155739504755035025)
            ·
              refine ⟨11963148866804628566276269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15950865155739504755035025 11963148866804628566276269)
              ·
                refine ⟨4486180825051735712353601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11963148866804628566276269 4486180825051735712353601)
                ·
                  refine ⟨3364635618788801784265201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4486180825051735712353601 3364635618788801784265201)
                  ·
                    refine ⟨2523476714091601338198901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3364635618788801784265201 2523476714091601338198901)
                    ·
                      refine ⟨236575941946087625456147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2523476714091601338198901 236575941946087625456147)
                      ·
                        rfl

theorem cell23_460730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_460730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460730 prefixEnd_460730 := by exact prefixLift 460730
  have htrace : WordTrace (prefixWord ++ tailWord_460730) baseStart_460730 baseEnd_460730 := by
    simpa [prefixWord, tailWord_460730, baseEnd_460730] using wordTrace_append hprefix tailTrace_460730
  have hstable : (prefixWord ++ tailWord_460730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460730).length < 2 ^ (prefixWord ++ tailWord_460730).sum := by decide
  have hdescent : baseEnd_460730 < baseStart_460730 := by decide
  rcases family_descends (prefixWord ++ tailWord_460730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460734 : List Nat := [4, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3]
def baseStart_460734 : Nat := 118140960795 + 460734 * 2 ^ 59
def prefixEnd_460734 : Nat := 4983230072969 + 3 ^ 40 * 460734 * 2
def baseEnd_460734 : Nat := 236577995868705609806129

theorem tailTrace_460734 : CollatzResearch.WordTrace tailWord_460734 prefixEnd_460734 236577995868705609806129 := by
  unfold tailWord_460734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2100543689105859993463657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11202899675231253298472837 2100543689105859993463657)
  ·
    refine ⟨1575407766829394995097743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2100543689105859993463657 1575407766829394995097743)
    ·
      refine ⟨2363111650244092492646615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1575407766829394995097743 2363111650244092492646615)
      ·
        refine ⟨3544667475366138738969923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2363111650244092492646615 3544667475366138738969923)
        ·
          refine ⟨5317001213049208108454885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3544667475366138738969923 5317001213049208108454885)
          ·
            refine ⟨996937727446726520335291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5317001213049208108454885 996937727446726520335291)
            ·
              refine ⟨1495406591170089780502937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996937727446726520335291 1495406591170089780502937)
              ·
                refine ⟨1121554943377567335377203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1495406591170089780502937 1121554943377567335377203)
                ·
                  refine ⟨1682332415066351003065805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1121554943377567335377203 1682332415066351003065805)
                  ·
                    refine ⟨630874655649881626149677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1682332415066351003065805 630874655649881626149677)
                    ·
                      refine ⟨236577995868705609806129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 630874655649881626149677 236577995868705609806129)
                      ·
                        rfl

theorem cell23_460734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_460734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460734 prefixEnd_460734 := by exact prefixLift 460734
  have htrace : WordTrace (prefixWord ++ tailWord_460734) baseStart_460734 baseEnd_460734 := by
    simpa [prefixWord, tailWord_460734, baseEnd_460734] using wordTrace_append hprefix tailTrace_460734
  have hstable : (prefixWord ++ tailWord_460734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460734).length < 2 ^ (prefixWord ++ tailWord_460734).sum := by decide
  have hdescent : baseEnd_460734 < baseStart_460734 := by decide
  rcases family_descends (prefixWord ++ tailWord_460734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460757 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 2, 3, 4]
def baseStart_460757 : Nat := 118140960795 + 460757 * 2 ^ 59
def prefixEnd_460757 : Nat := 4983230072969 + 3 ^ 40 * 460757 * 2
def baseEnd_460757 : Nat := 236589805923759019818523

theorem tailTrace_460757 : CollatzResearch.WordTrace tailWord_460757 prefixEnd_460757 236589805923759019818523 := by
  unfold tailWord_460757
  simp only [CollatzResearch.WordTrace]
  refine ⟨16805188391763554875796525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11203458927842369917197683 16805188391763554875796525)
  ·
    refine ⟨6301945646911333078423697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16805188391763554875796525 6301945646911333078423697)
    ·
      refine ⟨4726459235183499808817773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6301945646911333078423697 4726459235183499808817773)
      ·
        refine ⟨1772422213193812428306665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4726459235183499808817773 1772422213193812428306665)
        ·
          refine ⟨1329316659895359321229999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1772422213193812428306665 1329316659895359321229999)
          ·
            refine ⟨1993974989843038981844999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1329316659895359321229999 1993974989843038981844999)
            ·
              refine ⟨2990962484764558472767499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1993974989843038981844999 2990962484764558472767499)
              ·
                refine ⟨4486443727146837709151249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2990962484764558472767499 4486443727146837709151249)
                ·
                  refine ⟨3364832795360128281863437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4486443727146837709151249 3364832795360128281863437)
                  ·
                    refine ⟨1261812298260048105698789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3364832795360128281863437 1261812298260048105698789)
                    ·
                      refine ⟨236589805923759019818523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1261812298260048105698789 236589805923759019818523)
                      ·
                        rfl

theorem cell23_460757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_460757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460757 prefixEnd_460757 := by exact prefixLift 460757
  have htrace : WordTrace (prefixWord ++ tailWord_460757) baseStart_460757 baseEnd_460757 := by
    simpa [prefixWord, tailWord_460757, baseEnd_460757] using wordTrace_append hprefix tailTrace_460757
  have hstable : (prefixWord ++ tailWord_460757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460757).length < 2 ^ (prefixWord ++ tailWord_460757).sum := by decide
  have hdescent : baseEnd_460757 < baseStart_460757 := by decide
  rcases family_descends (prefixWord ++ tailWord_460757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460767 : List Nat := [1, 1, 2, 3, 4, 2, 1, 1, 2, 6]
def baseStart_460767 : Nat := 118140960795 + 460767 * 2 ^ 59
def prefixEnd_460767 : Nat := 4983230072969 + 3 ^ 40 * 460767 * 2
def baseEnd_460767 : Nat := 78864980243434660231159

theorem tailTrace_460767 : CollatzResearch.WordTrace tailWord_460767 prefixEnd_460767 78864980243434660231159 := by
  unfold tailWord_460767
  simp only [CollatzResearch.WordTrace]
  refine ⟨16805553121727326583660555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11203702081151551055773703 16805553121727326583660555)
  ·
    refine ⟨25208329682590989875490833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16805553121727326583660555 25208329682590989875490833)
    ·
      refine ⟨18906247261943242406618125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25208329682590989875490833 18906247261943242406618125)
      ·
        refine ⟨7089842723228715902481797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18906247261943242406618125 7089842723228715902481797)
        ·
          refine ⟨1329345510605384231715337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7089842723228715902481797 1329345510605384231715337)
          ·
            refine ⟨997009132954038173786503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1329345510605384231715337 997009132954038173786503)
            ·
              refine ⟨1495513699431057260679755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 997009132954038173786503 1495513699431057260679755)
              ·
                refine ⟨2243270549146585891019633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1495513699431057260679755 2243270549146585891019633)
                ·
                  refine ⟨1682452911859939418264725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2243270549146585891019633 1682452911859939418264725)
                  ·
                    refine ⟨78864980243434660231159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1682452911859939418264725 78864980243434660231159)
                    ·
                      rfl

theorem cell23_460767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 6].length) (baseStart_460767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460767 prefixEnd_460767 := by exact prefixLift 460767
  have htrace : WordTrace (prefixWord ++ tailWord_460767) baseStart_460767 baseEnd_460767 := by
    simpa [prefixWord, tailWord_460767, baseEnd_460767] using wordTrace_append hprefix tailTrace_460767
  have hstable : (prefixWord ++ tailWord_460767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460767).length < 2 ^ (prefixWord ++ tailWord_460767).sum := by decide
  have hdescent : baseEnd_460767 < baseStart_460767 := by decide
  rcases family_descends (prefixWord ++ tailWord_460767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460814 : List Nat := [4, 1, 1, 2, 2, 1, 1, 6, 5]
def baseStart_460814 : Nat := 118140960795 + 460814 * 2 ^ 59
def prefixEnd_460814 : Nat := 4983230072969 + 3 ^ 40 * 460814 * 2
def baseEnd_460814 : Nat := 26291008257896144089529

theorem tailTrace_460814 : CollatzResearch.WordTrace tailWord_460814 prefixEnd_460814 26291008257896144089529 := by
  unfold tailWord_460814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2100908419069631701327687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11204844901704702407080997 2100908419069631701327687)
  ·
    refine ⟨3151362628604447551991531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2100908419069631701327687 3151362628604447551991531)
    ·
      refine ⟨4727043942906671327987297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3151362628604447551991531 4727043942906671327987297)
      ·
        refine ⟨3545282957180003495990473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4727043942906671327987297 3545282957180003495990473)
        ·
          refine ⟨2658962217885002621992855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3545282957180003495990473 2658962217885002621992855)
          ·
            refine ⟨3988443326827503932989283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2658962217885002621992855 3988443326827503932989283)
            ·
              refine ⟨5982664990241255899483925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3988443326827503932989283 5982664990241255899483925)
              ·
                refine ⟨280437421417558870288309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5982664990241255899483925 280437421417558870288309)
                ·
                  refine ⟨26291008257896144089529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 280437421417558870288309 26291008257896144089529)
                  ·
                    rfl

theorem cell23_460814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_460814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460814 prefixEnd_460814 := by exact prefixLift 460814
  have htrace : WordTrace (prefixWord ++ tailWord_460814) baseStart_460814 baseEnd_460814 := by
    simpa [prefixWord, tailWord_460814, baseEnd_460814] using wordTrace_append hprefix tailTrace_460814
  have hstable : (prefixWord ++ tailWord_460814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460814).length < 2 ^ (prefixWord ++ tailWord_460814).sum := by decide
  have hdescent : baseEnd_460814 < baseStart_460814 := by decide
  rcases family_descends (prefixWord ++ tailWord_460814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460854 : List Nat := [5, 1, 2, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_460854 : Nat := 118140960795 + 460854 * 2 ^ 59
def prefixEnd_460854 : Nat := 4983230072969 + 3 ^ 40 * 460854 * 2
def baseEnd_460854 : Nat := 236639613547245140305577

theorem tailTrace_460854 : CollatzResearch.WordTrace tailWord_460854 prefixEnd_460854 236639613547245140305577 := by
  unfold tailWord_460854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1050545392025758777629851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11205817514941426961385077 1050545392025758777629851)
  ·
    refine ⟨1575818088038638166444777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1050545392025758777629851 1575818088038638166444777)
    ·
      refine ⟨1181863566028978624833583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1575818088038638166444777 1181863566028978624833583)
      ·
        refine ⟨1772795349043467937250375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1181863566028978624833583 1772795349043467937250375)
        ·
          refine ⟨2659193023565201905875563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1772795349043467937250375 2659193023565201905875563)
          ·
            refine ⟨3988789535347802858813345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2659193023565201905875563 3988789535347802858813345)
            ·
              refine ⟨2991592151510852144110009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3988789535347802858813345 2991592151510852144110009)
              ·
                refine ⟨2243694113633139108082507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2991592151510852144110009 2243694113633139108082507)
                ·
                  refine ⟨3365541170449708662123761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2243694113633139108082507 3365541170449708662123761)
                  ·
                    refine ⟨2524155877837281496592821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3365541170449708662123761 2524155877837281496592821)
                    ·
                      refine ⟨236639613547245140305577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2524155877837281496592821 236639613547245140305577)
                      ·
                        rfl

theorem cell23_460854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_460854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460854 prefixEnd_460854 := by exact prefixLift 460854
  have htrace : WordTrace (prefixWord ++ tailWord_460854) baseStart_460854 baseEnd_460854 := by
    simpa [prefixWord, tailWord_460854, baseEnd_460854] using wordTrace_append hprefix tailTrace_460854
  have hstable : (prefixWord ++ tailWord_460854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460854).length < 2 ^ (prefixWord ++ tailWord_460854).sum := by decide
  have hdescent : baseEnd_460854 < baseStart_460854 := by decide
  rcases family_descends (prefixWord ++ tailWord_460854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460864 : List Nat := [2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 4]
def baseStart_460864 : Nat := 118140960795 + 460864 * 2 ^ 59
def prefixEnd_460864 : Nat := 4983230072969 + 3 ^ 40 * 460864 * 2
def baseEnd_460864 : Nat := 236644748353790101180531

theorem tailTrace_460864 : CollatzResearch.WordTrace tailWord_460864 prefixEnd_460864 236644748353790101180531 := by
  unfold tailWord_460864
  simp only [CollatzResearch.WordTrace]
  refine ⟨8404545501187956074970823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11206060668250608099961097 8404545501187956074970823)
  ·
    refine ⟨12606818251781934112456235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8404545501187956074970823 12606818251781934112456235)
    ·
      refine ⟨18910227377672901168684353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12606818251781934112456235 18910227377672901168684353)
      ·
        refine ⟨14182670533254675876513265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18910227377672901168684353 14182670533254675876513265)
        ·
          refine ⟨10637002899941006907384949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14182670533254675876513265 10637002899941006907384949)
          ·
            refine ⟨997219021869469397567339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10637002899941006907384949 997219021869469397567339)
            ·
              refine ⟨1495828532804204096351009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 997219021869469397567339 1495828532804204096351009)
              ·
                refine ⟨1121871399603153072263257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1495828532804204096351009 1121871399603153072263257)
                ·
                  refine ⟨841403549702364804197443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1121871399603153072263257 841403549702364804197443)
                  ·
                    refine ⟨1262105324553547206296165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 841403549702364804197443 1262105324553547206296165)
                    ·
                      refine ⟨236644748353790101180531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1262105324553547206296165 236644748353790101180531)
                      ·
                        rfl

theorem cell23_460864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_460864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460864 prefixEnd_460864 := by exact prefixLift 460864
  have htrace : WordTrace (prefixWord ++ tailWord_460864) baseStart_460864 baseEnd_460864 := by
    simpa [prefixWord, tailWord_460864, baseEnd_460864] using wordTrace_append hprefix tailTrace_460864
  have hstable : (prefixWord ++ tailWord_460864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460864).length < 2 ^ (prefixWord ++ tailWord_460864).sum := by decide
  have hdescent : baseEnd_460864 < baseStart_460864 := by decide
  rcases family_descends (prefixWord ++ tailWord_460864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460867 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 3, 4, 3]
def baseStart_460867 : Nat := 118140960795 + 460867 * 2 ^ 59
def prefixEnd_460867 : Nat := 4983230072969 + 3 ^ 40 * 460867 * 2
def baseEnd_460867 : Nat := 236646288795753589443017

theorem tailTrace_460867 : CollatzResearch.WordTrace tailWord_460867 prefixEnd_460867 236646288795753589443017 := by
  unfold tailWord_460867
  simp only [CollatzResearch.WordTrace]
  refine ⟨16809200421365043662300855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11206133614243362441533903 16809200421365043662300855)
  ·
    refine ⟨25213800632047565493451283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16809200421365043662300855 25213800632047565493451283)
    ·
      refine ⟨37820700948071348240176925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25213800632047565493451283 37820700948071348240176925)
      ·
        refine ⟨14182762855526755590066347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37820700948071348240176925 14182762855526755590066347)
        ·
          refine ⟨21274144283290133385099521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14182762855526755590066347 21274144283290133385099521)
          ·
            refine ⟨15955608212467600038824641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21274144283290133385099521 15955608212467600038824641)
            ·
              refine ⟨11966706159350700029118481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15955608212467600038824641 11966706159350700029118481)
              ·
                refine ⟨8975029619513025021838861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11966706159350700029118481 8975029619513025021838861)
                ·
                  refine ⟨3365636107317384383189573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8975029619513025021838861 3365636107317384383189573)
                  ·
                    refine ⟨631056770122009571848045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3365636107317384383189573 631056770122009571848045)
                    ·
                      refine ⟨236646288795753589443017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 631056770122009571848045 236646288795753589443017)
                      ·
                        rfl

theorem cell23_460867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4, 3].length) (baseStart_460867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460867 prefixEnd_460867 := by exact prefixLift 460867
  have htrace : WordTrace (prefixWord ++ tailWord_460867) baseStart_460867 baseEnd_460867 := by
    simpa [prefixWord, tailWord_460867, baseEnd_460867] using wordTrace_append hprefix tailTrace_460867
  have hstable : (prefixWord ++ tailWord_460867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460867).length < 2 ^ (prefixWord ++ tailWord_460867).sum := by decide
  have hdescent : baseEnd_460867 < baseStart_460867 := by decide
  rcases family_descends (prefixWord ++ tailWord_460867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460884 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 6, 2, 3]
def baseStart_460884 : Nat := 118140960795 + 460884 * 2 ^ 59
def prefixEnd_460884 : Nat := 4983230072969 + 3 ^ 40 * 460884 * 2
def baseEnd_460884 : Nat := 236655017966880022930439

theorem tailTrace_460884 : CollatzResearch.WordTrace tailWord_460884 prefixEnd_460884 236655017966880022930439 := by
  unfold tailWord_460884
  simp only [CollatzResearch.WordTrace]
  refine ⟨8404910231151727782834853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11206546974868970377113137 8404910231151727782834853)
  ·
    refine ⟨1575920668340948959281535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8404910231151727782834853 1575920668340948959281535)
    ·
      refine ⟨2363881002511423438922303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1575920668340948959281535 2363881002511423438922303)
      ·
        refine ⟨3545821503767135158383455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2363881002511423438922303 3545821503767135158383455)
        ·
          refine ⟨5318732255650702737575183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3545821503767135158383455 5318732255650702737575183)
          ·
            refine ⟨7978098383476054106362775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5318732255650702737575183 7978098383476054106362775)
            ·
              refine ⟨11967147575214081159544163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7978098383476054106362775 11967147575214081159544163)
              ·
                refine ⟨17950721362821121739316245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11967147575214081159544163 17950721362821121739316245)
                ·
                  refine ⟨841440063882240081530449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17950721362821121739316245 841440063882240081530449)
                  ·
                    refine ⟨631080047911680061147837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 841440063882240081530449 631080047911680061147837)
                    ·
                      refine ⟨236655017966880022930439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 631080047911680061147837 236655017966880022930439)
                      ·
                        rfl

theorem cell23_460884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_460884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460884 prefixEnd_460884 := by exact prefixLift 460884
  have htrace : WordTrace (prefixWord ++ tailWord_460884) baseStart_460884 baseEnd_460884 := by
    simpa [prefixWord, tailWord_460884, baseEnd_460884] using wordTrace_append hprefix tailTrace_460884
  have hstable : (prefixWord ++ tailWord_460884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460884).length < 2 ^ (prefixWord ++ tailWord_460884).sum := by decide
  have hdescent : baseEnd_460884 < baseStart_460884 := by decide
  rcases family_descends (prefixWord ++ tailWord_460884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460898 : List Nat := [3, 3, 2, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_460898 : Nat := 118140960795 + 460898 * 2 ^ 59
def prefixEnd_460898 : Nat := 4983230072969 + 3 ^ 40 * 460898 * 2
def baseEnd_460898 : Nat := 236662206696042968155375

theorem tailTrace_460898 : CollatzResearch.WordTrace tailWord_460898 prefixEnd_460898 236662206696042968155375 := by
  unfold tailWord_460898
  simp only [CollatzResearch.WordTrace]
  refine ⟨4202582771063183989169837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11206887389501823971119565 4202582771063183989169837)
  ·
    refine ⟨1575968539148693995938689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4202582771063183989169837 1575968539148693995938689)
    ·
      refine ⟨1181976404361520496954017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1575968539148693995938689 1181976404361520496954017)
      ·
        refine ⟨886482303271140372715513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1181976404361520496954017 886482303271140372715513)
        ·
          refine ⟨664861727453355279536635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 886482303271140372715513 664861727453355279536635)
          ·
            refine ⟨997292591180032919304953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664861727453355279536635 997292591180032919304953)
            ·
              refine ⟨747969443385024689478715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 997292591180032919304953 747969443385024689478715)
              ·
                refine ⟨1121954165077537034218073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747969443385024689478715 1121954165077537034218073)
                ·
                  refine ⟨841465623808152775663555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1121954165077537034218073 841465623808152775663555)
                  ·
                    refine ⟨1262198435712229163495333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 841465623808152775663555 1262198435712229163495333)
                    ·
                      refine ⟨236662206696042968155375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1262198435712229163495333 236662206696042968155375)
                      ·
                        rfl

theorem cell23_460898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_460898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460898 prefixEnd_460898 := by exact prefixLift 460898
  have htrace : WordTrace (prefixWord ++ tailWord_460898) baseStart_460898 baseEnd_460898 := by
    simpa [prefixWord, tailWord_460898, baseEnd_460898] using wordTrace_append hprefix tailTrace_460898
  have hstable : (prefixWord ++ tailWord_460898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460898).length < 2 ^ (prefixWord ++ tailWord_460898).sum := by decide
  have hdescent : baseEnd_460898 < baseStart_460898 := by decide
  rcases family_descends (prefixWord ++ tailWord_460898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460901 : List Nat := [1, 3, 1, 3, 2, 3, 2, 1, 2, 2, 3]
def baseStart_460901 : Nat := 118140960795 + 460901 * 2 ^ 59
def prefixEnd_460901 : Nat := 4983230072969 + 3 ^ 40 * 460901 * 2
def baseEnd_460901 : Nat := 236663747138006456417861

theorem tailTrace_460901 : CollatzResearch.WordTrace tailWord_460901 prefixEnd_460901 236663747138006456417861 := by
  unfold tailWord_460901
  simp only [CollatzResearch.WordTrace]
  refine ⟨16810440503241867469038557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11206960335494578312692371 16810440503241867469038557)
  ·
    refine ⟨6303915188715700300889459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16810440503241867469038557 6303915188715700300889459)
    ·
      refine ⟨9455872783073550451334189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6303915188715700300889459 9455872783073550451334189)
      ·
        refine ⟨3545952293652581419250321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9455872783073550451334189 3545952293652581419250321)
        ·
          refine ⟨2659464220239436064437741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3545952293652581419250321 2659464220239436064437741)
          ·
            refine ⟨997299082589788524164153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2659464220239436064437741 997299082589788524164153)
            ·
              refine ⟨747974311942341393123115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 997299082589788524164153 747974311942341393123115)
              ·
                refine ⟨1121961467913512089684673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747974311942341393123115 1121961467913512089684673)
                ·
                  refine ⟨841471100935134067263505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1121961467913512089684673 841471100935134067263505)
                  ·
                    refine ⟨631103325701350550447629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 841471100935134067263505 631103325701350550447629)
                    ·
                      refine ⟨236663747138006456417861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 631103325701350550447629 236663747138006456417861)
                      ·
                        rfl

theorem cell23_460901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_460901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460901 prefixEnd_460901 := by exact prefixLift 460901
  have htrace : WordTrace (prefixWord ++ tailWord_460901) baseStart_460901 baseEnd_460901 := by
    simpa [prefixWord, tailWord_460901, baseEnd_460901] using wordTrace_append hprefix tailTrace_460901
  have hstable : (prefixWord ++ tailWord_460901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460901).length < 2 ^ (prefixWord ++ tailWord_460901).sum := by decide
  have hdescent : baseEnd_460901 < baseStart_460901 := by decide
  rcases family_descends (prefixWord ++ tailWord_460901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460925 : List Nat := [1, 4, 1, 1, 3, 4, 2, 2, 1, 4]
def baseStart_460925 : Nat := 118140960795 + 460925 * 2 ^ 59
def prefixEnd_460925 : Nat := 4983230072969 + 3 ^ 40 * 460925 * 2
def baseEnd_460925 : Nat := 78892023557904787505917

theorem tailTrace_460925 : CollatzResearch.WordTrace tailWord_460925 prefixEnd_460925 78892023557904787505917 := by
  unfold tailWord_460925
  simp only [CollatzResearch.WordTrace]
  refine ⟨16811315855154919567912229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11207543903436613045274819 16811315855154919567912229)
  ·
    refine ⟨3152121722841547418983543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16811315855154919567912229 3152121722841547418983543)
    ·
      refine ⟨4728182584262321128475315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3152121722841547418983543 4728182584262321128475315)
      ·
        refine ⟨7092273876393481692712973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4728182584262321128475315 7092273876393481692712973)
        ·
          refine ⟨2659602703647555634767365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7092273876393481692712973 2659602703647555634767365)
          ·
            refine ⟨498675506933916681518881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2659602703647555634767365 498675506933916681518881)
            ·
              refine ⟨374006630200437511139161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 498675506933916681518881 374006630200437511139161)
              ·
                refine ⟨280504972650328133354371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 374006630200437511139161 280504972650328133354371)
                ·
                  refine ⟨420757458975492200031557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 280504972650328133354371 420757458975492200031557)
                  ·
                    refine ⟨78892023557904787505917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 420757458975492200031557 78892023557904787505917)
                    ·
                      rfl

theorem cell23_460925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_460925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_460925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_460925 prefixEnd_460925 := by exact prefixLift 460925
  have htrace : WordTrace (prefixWord ++ tailWord_460925) baseStart_460925 baseEnd_460925 := by
    simpa [prefixWord, tailWord_460925, baseEnd_460925] using wordTrace_append hprefix tailTrace_460925
  have hstable : (prefixWord ++ tailWord_460925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460925).length < 2 ^ (prefixWord ++ tailWord_460925).sum := by decide
  have hdescent : baseEnd_460925 < baseStart_460925 := by decide
  rcases family_descends (prefixWord ++ tailWord_460925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461034 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_461034 : Nat := 118140960795 + 461034 * 2 ^ 59
def prefixEnd_461034 : Nat := 4983230072969 + 3 ^ 40 * 461034 * 2
def baseEnd_461034 : Nat := 236732040065054436054749

theorem tailTrace_461034 : CollatzResearch.WordTrace tailWord_461034 prefixEnd_461034 236732040065054436054749 := by
  unfold tailWord_461034
  simp only [CollatzResearch.WordTrace]
  refine ⟨4203822852940007795907539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11210194274506687455753437 4203822852940007795907539)
  ·
    refine ⟨6305734279410011693861309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4203822852940007795907539 6305734279410011693861309)
    ·
      refine ⟨2364650354778754385197991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6305734279410011693861309 2364650354778754385197991)
      ·
        refine ⟨3546975532168131577796987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2364650354778754385197991 3546975532168131577796987)
        ·
          refine ⟨5320463298252197366695481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3546975532168131577796987 5320463298252197366695481)
          ·
            refine ⟨3990347473689148025021611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5320463298252197366695481 3990347473689148025021611)
            ·
              refine ⟨5985521210533722037532417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3990347473689148025021611 5985521210533722037532417)
              ·
                refine ⟨4489140907900291528149313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5985521210533722037532417 4489140907900291528149313)
                ·
                  refine ⟨3366855680925218646111985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4489140907900291528149313 3366855680925218646111985)
                  ·
                    refine ⟨2525141760693913984583989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3366855680925218646111985 2525141760693913984583989)
                    ·
                      refine ⟨236732040065054436054749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2525141760693913984583989 236732040065054436054749)
                      ·
                        rfl

theorem cell23_461034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_461034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461034 prefixEnd_461034 := by exact prefixLift 461034
  have htrace : WordTrace (prefixWord ++ tailWord_461034) baseStart_461034 baseEnd_461034 := by
    simpa [prefixWord, tailWord_461034, baseEnd_461034] using wordTrace_append hprefix tailTrace_461034
  have hstable : (prefixWord ++ tailWord_461034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461034).length < 2 ^ (prefixWord ++ tailWord_461034).sum := by decide
  have hdescent : baseEnd_461034 < baseStart_461034 := by decide
  rcases family_descends (prefixWord ++ tailWord_461034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461038 : List Nat := [4, 1, 2, 1, 1, 1, 1, 6, 2, 1, 3]
def baseStart_461038 : Nat := 118140960795 + 461038 * 2 ^ 59
def prefixEnd_461038 : Nat := 4983230072969 + 3 ^ 40 * 461038 * 2
def baseEnd_461038 : Nat := 236734093987672420404731

theorem tailTrace_461038 : CollatzResearch.WordTrace tailWord_461038 prefixEnd_461038 236734093987672420404731 := by
  unfold tailWord_461038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2101929662968192483346971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11210291535830359911183845 2101929662968192483346971)
  ·
    refine ⟨3152894494452288725020457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2101929662968192483346971 3152894494452288725020457)
    ·
      refine ⟨2364670870839216543765343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3152894494452288725020457 2364670870839216543765343)
      ·
        refine ⟨3547006306258824815648015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2364670870839216543765343 3547006306258824815648015)
        ·
          refine ⟨5320509459388237223472023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3547006306258824815648015 5320509459388237223472023)
          ·
            refine ⟨7980764189082355835208035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5320509459388237223472023 7980764189082355835208035)
            ·
              refine ⟨11971146283623533752812053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7980764189082355835208035 11971146283623533752812053)
              ·
                refine ⟨561147482044853144663065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11971146283623533752812053 561147482044853144663065)
                ·
                  refine ⟨420860611533639858497299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 561147482044853144663065 420860611533639858497299)
                  ·
                    refine ⟨631290917300459787745949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 420860611533639858497299 631290917300459787745949)
                    ·
                      refine ⟨236734093987672420404731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 631290917300459787745949 236734093987672420404731)
                      ·
                        rfl

theorem cell23_461038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_461038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461038 prefixEnd_461038 := by exact prefixLift 461038
  have htrace : WordTrace (prefixWord ++ tailWord_461038) baseStart_461038 baseEnd_461038 := by
    simpa [prefixWord, tailWord_461038, baseEnd_461038] using wordTrace_append hprefix tailTrace_461038
  have hstable : (prefixWord ++ tailWord_461038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461038).length < 2 ^ (prefixWord ++ tailWord_461038).sum := by decide
  have hdescent : baseEnd_461038 < baseStart_461038 := by decide
  rcases family_descends (prefixWord ++ tailWord_461038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461065 : List Nat := [1, 2, 1, 1, 3, 6, 1, 2, 1, 3, 2]
def baseStart_461065 : Nat := 118140960795 + 461065 * 2 ^ 59
def prefixEnd_461065 : Nat := 4983230072969 + 3 ^ 40 * 461065 * 2
def baseEnd_461065 : Nat := 236747957965343814767107

theorem tailTrace_461065 : CollatzResearch.WordTrace tailWord_461065 prefixEnd_461065 236747957965343814767107 := by
  unfold tailWord_461065
  simp only [CollatzResearch.WordTrace]
  refine ⟨16816422074647723478008649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11210948049765148985339099 16816422074647723478008649)
  ·
    refine ⟨12612316555985792608506487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16816422074647723478008649 12612316555985792608506487)
    ·
      refine ⟨18918474833978688912759731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12612316555985792608506487 18918474833978688912759731)
      ·
        refine ⟨28377712250968033369139597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18918474833978688912759731 28377712250968033369139597)
        ·
          refine ⟨10641642094113012513427349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28377712250968033369139597 10641642094113012513427349)
          ·
            refine ⟨498826973161547461566907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10641642094113012513427349 498826973161547461566907)
            ·
              refine ⟨748240459742321192350361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498826973161547461566907 748240459742321192350361)
              ·
                refine ⟨561180344806740894262771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 748240459742321192350361 561180344806740894262771)
                ·
                  refine ⟨841770517210111341394157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 561180344806740894262771 841770517210111341394157)
                  ·
                    refine ⟨315663943953791753022809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 841770517210111341394157 315663943953791753022809)
                    ·
                      refine ⟨236747957965343814767107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 315663943953791753022809 236747957965343814767107)
                      ·
                        rfl

theorem cell23_461065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 3, 2].length) (baseStart_461065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461065 prefixEnd_461065 := by exact prefixLift 461065
  have htrace : WordTrace (prefixWord ++ tailWord_461065) baseStart_461065 baseEnd_461065 := by
    simpa [prefixWord, tailWord_461065, baseEnd_461065] using wordTrace_append hprefix tailTrace_461065
  have hstable : (prefixWord ++ tailWord_461065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461065).length < 2 ^ (prefixWord ++ tailWord_461065).sum := by decide
  have hdescent : baseEnd_461065 < baseStart_461065 := by decide
  rcases family_descends (prefixWord ++ tailWord_461065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461082 : List Nat := [3, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2]
def baseStart_461082 : Nat := 118140960795 + 461082 * 2 ^ 59
def prefixEnd_461082 : Nat := 4983230072969 + 3 ^ 40 * 461082 * 2
def baseEnd_461082 : Nat := 236756687136470248254529

theorem tailTrace_461082 : CollatzResearch.WordTrace tailWord_461082 prefixEnd_461082 236756687136470248254529 := by
  unfold tailWord_461082
  simp only [CollatzResearch.WordTrace]
  refine ⟨4204260528896533845344375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11211361410390756920918333 4204260528896533845344375)
  ·
    refine ⟨6306390793344800768016563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4204260528896533845344375 6306390793344800768016563)
    ·
      refine ⟨9459586190017201152024845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6306390793344800768016563 9459586190017201152024845)
      ·
        refine ⟨3547344821256450432009317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9459586190017201152024845 3547344821256450432009317)
        ·
          refine ⟨665127153985584456001747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3547344821256450432009317 665127153985584456001747)
          ·
            refine ⟨997690730978376684002621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665127153985584456001747 997690730978376684002621)
            ·
              refine ⟨374134024116891256500983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 997690730978376684002621 374134024116891256500983)
              ·
                refine ⟨561201036175336884751475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374134024116891256500983 561201036175336884751475)
                ·
                  refine ⟨841801554263005327127213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 561201036175336884751475 841801554263005327127213)
                  ·
                    refine ⟨315675582848626997672705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 841801554263005327127213 315675582848626997672705)
                    ·
                      refine ⟨236756687136470248254529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 315675582848626997672705 236756687136470248254529)
                      ·
                        rfl

theorem cell23_461082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_461082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461082 prefixEnd_461082 := by exact prefixLift 461082
  have htrace : WordTrace (prefixWord ++ tailWord_461082) baseStart_461082 baseEnd_461082 := by
    simpa [prefixWord, tailWord_461082, baseEnd_461082] using wordTrace_append hprefix tailTrace_461082
  have hstable : (prefixWord ++ tailWord_461082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461082).length < 2 ^ (prefixWord ++ tailWord_461082).sum := by decide
  have hdescent : baseEnd_461082 < baseStart_461082 := by decide
  rcases family_descends (prefixWord ++ tailWord_461082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461108 : List Nat := [2, 5, 1, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_461108 : Nat := 118140960795 + 461108 * 2 ^ 59
def prefixEnd_461108 : Nat := 4983230072969 + 3 ^ 40 * 461108 * 2
def baseEnd_461108 : Nat := 236770037633487146529409

theorem tailTrace_461108 : CollatzResearch.WordTrace tailWord_461108 prefixEnd_461108 236770037633487146529409 := by
  unfold tailWord_461108
  simp only [CollatzResearch.WordTrace]
  refine ⟨8408995206745970910911989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11211993608994627881215985 8408995206745970910911989)
  ·
    refine ⟨788343300632434772897999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8408995206745970910911989 788343300632434772897999)
    ·
      refine ⟨1182514950948652159346999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 788343300632434772897999 1182514950948652159346999)
      ·
        refine ⟨1773772426422978239020499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1182514950948652159346999 1773772426422978239020499)
        ·
          refine ⟨2660658639634467358530749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1773772426422978239020499 2660658639634467358530749)
          ·
            refine ⟨997746989862925259449031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2660658639634467358530749 997746989862925259449031)
            ·
              refine ⟨1496620484794387889173547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 997746989862925259449031 1496620484794387889173547)
              ·
                refine ⟨2244930727191581833760321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1496620484794387889173547 2244930727191581833760321)
                ·
                  refine ⟨1683698045393686375320241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2244930727191581833760321 1683698045393686375320241)
                  ·
                    refine ⟨1262773534045264781490181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1683698045393686375320241 1262773534045264781490181)
                    ·
                      refine ⟨236770037633487146529409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1262773534045264781490181 236770037633487146529409)
                      ·
                        rfl

theorem cell23_461108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_461108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461108 prefixEnd_461108 := by exact prefixLift 461108
  have htrace : WordTrace (prefixWord ++ tailWord_461108) baseStart_461108 baseEnd_461108 := by
    simpa [prefixWord, tailWord_461108, baseEnd_461108] using wordTrace_append hprefix tailTrace_461108
  have hstable : (prefixWord ++ tailWord_461108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461108).length < 2 ^ (prefixWord ++ tailWord_461108).sum := by decide
  have hdescent : baseEnd_461108 < baseStart_461108 := by decide
  rcases family_descends (prefixWord ++ tailWord_461108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461151 : List Nat := [1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 4]
def baseStart_461151 : Nat := 118140960795 + 461151 * 2 ^ 59
def prefixEnd_461151 : Nat := 4983230072969 + 3 ^ 40 * 461151 * 2
def baseEnd_461151 : Nat := 236792117301630478291711

theorem tailTrace_461151 : CollatzResearch.WordTrace tailWord_461151 prefixEnd_461151 236792117301630478291711 := by
  unfold tailWord_461151
  simp only [CollatzResearch.WordTrace]
  refine ⟨16819558752336160165639307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11213039168224106777092871 16819558752336160165639307)
  ·
    refine ⟨25229338128504240248458961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16819558752336160165639307 25229338128504240248458961)
    ·
      refine ⟨18922003596378180186344221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25229338128504240248458961 18922003596378180186344221)
      ·
        refine ⟨7095751348641817569879083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18922003596378180186344221 7095751348641817569879083)
        ·
          refine ⟨10643627022962726354818625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7095751348641817569879083 10643627022962726354818625)
          ·
            refine ⟨7982720267222044766113969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10643627022962726354818625 7982720267222044766113969)
            ·
              refine ⟨5987040200416533574585477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7982720267222044766113969 5987040200416533574585477)
              ·
                refine ⟨1122570037578100045234777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5987040200416533574585477 1122570037578100045234777)
                ·
                  refine ⟨841927528183575033926083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1122570037578100045234777 841927528183575033926083)
                  ·
                    refine ⟨1262891292275362550889125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 841927528183575033926083 1262891292275362550889125)
                    ·
                      refine ⟨236792117301630478291711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1262891292275362550889125 236792117301630478291711)
                      ·
                        rfl

theorem cell23_461151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_461151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461151 prefixEnd_461151 := by exact prefixLift 461151
  have htrace : WordTrace (prefixWord ++ tailWord_461151) baseStart_461151 baseEnd_461151 := by
    simpa [prefixWord, tailWord_461151, baseEnd_461151] using wordTrace_append hprefix tailTrace_461151
  have hstable : (prefixWord ++ tailWord_461151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461151).length < 2 ^ (prefixWord ++ tailWord_461151).sum := by decide
  have hdescent : baseEnd_461151 < baseStart_461151 := by decide
  rcases family_descends (prefixWord ++ tailWord_461151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461168 : List Nat := [2, 1, 1, 1, 4, 3, 2, 1, 2, 4, 2]
def baseStart_461168 : Nat := 118140960795 + 461168 * 2 ^ 59
def prefixEnd_461168 : Nat := 4983230072969 + 3 ^ 40 * 461168 * 2
def baseEnd_461168 : Nat := 236800846472756911779133

theorem tailTrace_461168 : CollatzResearch.WordTrace tailWord_461168 prefixEnd_461168 236800846472756911779133 := by
  unfold tailWord_461168
  simp only [CollatzResearch.WordTrace]
  refine ⟨8410089396637286034504079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11213452528849714712672105 8410089396637286034504079)
  ·
    refine ⟨12615134094955929051756119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8410089396637286034504079 12615134094955929051756119)
    ·
      refine ⟨18922701142433893577634179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12615134094955929051756119 18922701142433893577634179)
      ·
        refine ⟨28384051713650840366451269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18922701142433893577634179 28384051713650840366451269)
        ·
          refine ⟨5322009696309532568709613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28384051713650840366451269 5322009696309532568709613)
          ·
            refine ⟨1995753636116074713266105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5322009696309532568709613 1995753636116074713266105)
            ·
              refine ⟨1496815227087056034949579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1995753636116074713266105 1496815227087056034949579)
              ·
                refine ⟨2245222840630584052424369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1496815227087056034949579 2245222840630584052424369)
                ·
                  refine ⟨1683917130472938039318277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2245222840630584052424369 1683917130472938039318277)
                  ·
                    refine ⟨315734461963675882372177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1683917130472938039318277 315734461963675882372177)
                    ·
                      refine ⟨236800846472756911779133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 315734461963675882372177 236800846472756911779133)
                      ·
                        rfl

theorem cell23_461168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 2, 4, 2].length) (baseStart_461168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461168 prefixEnd_461168 := by exact prefixLift 461168
  have htrace : WordTrace (prefixWord ++ tailWord_461168) baseStart_461168 baseEnd_461168 := by
    simpa [prefixWord, tailWord_461168, baseEnd_461168] using wordTrace_append hprefix tailTrace_461168
  have hstable : (prefixWord ++ tailWord_461168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461168).length < 2 ^ (prefixWord ++ tailWord_461168).sum := by decide
  have hdescent : baseEnd_461168 < baseStart_461168 := by decide
  rcases family_descends (prefixWord ++ tailWord_461168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461171 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 4, 2, 3]
def baseStart_461171 : Nat := 118140960795 + 461171 * 2 ^ 59
def prefixEnd_461171 : Nat := 4983230072969 + 3 ^ 40 * 461171 * 2
def baseEnd_461171 : Nat := 236802386914720400041619

theorem tailTrace_461171 : CollatzResearch.WordTrace tailWord_461171 prefixEnd_461171 236802386914720400041619 := by
  unfold tailWord_461171
  simp only [CollatzResearch.WordTrace]
  refine ⟨16820288212263703581367367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11213525474842469054244911 16820288212263703581367367)
  ·
    refine ⟨25230432318395555372051051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16820288212263703581367367 25230432318395555372051051)
    ·
      refine ⟨37845648477593333058076577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25230432318395555372051051 37845648477593333058076577)
      ·
        refine ⟨28384236358194999793557433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37845648477593333058076577 28384236358194999793557433)
        ·
          refine ⟨21288177268646249845168075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28384236358194999793557433 21288177268646249845168075)
          ·
            refine ⟨31932265902969374767752113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21288177268646249845168075 31932265902969374767752113)
            ·
              refine ⟨23949199427227031075814085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31932265902969374767752113 23949199427227031075814085)
              ·
                refine ⟨4490474892605068326715141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23949199427227031075814085 4490474892605068326715141)
                ·
                  refine ⟨841964042363450311259089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4490474892605068326715141 841964042363450311259089)
                  ·
                    refine ⟨631473031772587733444317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 841964042363450311259089 631473031772587733444317)
                    ·
                      refine ⟨236802386914720400041619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 631473031772587733444317 236802386914720400041619)
                      ·
                        rfl

theorem cell23_461171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2, 3].length) (baseStart_461171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461171 prefixEnd_461171 := by exact prefixLift 461171
  have htrace : WordTrace (prefixWord ++ tailWord_461171) baseStart_461171 baseEnd_461171 := by
    simpa [prefixWord, tailWord_461171, baseEnd_461171] using wordTrace_append hprefix tailTrace_461171
  have hstable : (prefixWord ++ tailWord_461171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461171).length < 2 ^ (prefixWord ++ tailWord_461171).sum := by decide
  have hdescent : baseEnd_461171 < baseStart_461171 := by decide
  rcases family_descends (prefixWord ++ tailWord_461171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461184 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 9]
def baseStart_461184 : Nat := 118140960795 + 461184 * 2 ^ 59
def prefixEnd_461184 : Nat := 4983230072969 + 3 ^ 40 * 461184 * 2
def baseEnd_461184 : Nat := 236809062163228849179059

theorem tailTrace_461184 : CollatzResearch.WordTrace tailWord_461184 prefixEnd_461184 236809062163228849179059 := by
  unfold tailWord_461184
  simp only [CollatzResearch.WordTrace]
  refine ⟨8410381180608303400795303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11213841574144404534393737 8410381180608303400795303)
  ·
    refine ⟨12615571770912455101192955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8410381180608303400795303 12615571770912455101192955)
    ·
      refine ⟨18923357656368682651789433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12615571770912455101192955 18923357656368682651789433)
      ·
        refine ⟨14192518242276511988842075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18923357656368682651789433 14192518242276511988842075)
        ·
          refine ⟨21288777363414767983263113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14192518242276511988842075 21288777363414767983263113)
          ·
            refine ⟨15966583022561075987447335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21288777363414767983263113 15966583022561075987447335)
            ·
              refine ⟨23949874533841613981171003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15966583022561075987447335 23949874533841613981171003)
              ·
                refine ⟨35924811800762420971756505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23949874533841613981171003 35924811800762420971756505)
                ·
                  refine ⟨26943608850571815728817379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35924811800762420971756505 26943608850571815728817379)
                  ·
                    refine ⟨40415413275857723593226069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26943608850571815728817379 40415413275857723593226069)
                    ·
                      refine ⟨236809062163228849179059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 40415413275857723593226069 236809062163228849179059)
                      ·
                        rfl

theorem cell23_461184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_461184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461184 prefixEnd_461184 := by exact prefixLift 461184
  have htrace : WordTrace (prefixWord ++ tailWord_461184) baseStart_461184 baseEnd_461184 := by
    simpa [prefixWord, tailWord_461184, baseEnd_461184] using wordTrace_append hprefix tailTrace_461184
  have hstable : (prefixWord ++ tailWord_461184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461184).length < 2 ^ (prefixWord ++ tailWord_461184).sum := by decide
  have hdescent : baseEnd_461184 < baseStart_461184 := by decide
  rcases family_descends (prefixWord ++ tailWord_461184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461188 : List Nat := [2, 3, 2, 1, 1, 2, 2, 3, 2, 2, 3]
def baseStart_461188 : Nat := 118140960795 + 461188 * 2 ^ 59
def prefixEnd_461188 : Nat := 4983230072969 + 3 ^ 40 * 461188 * 2
def baseEnd_461188 : Nat := 236811116085846833529041

theorem tailTrace_461188 : CollatzResearch.WordTrace tailWord_461188 prefixEnd_461188 236811116085846833529041 := by
  unfold tailWord_461188
  simp only [CollatzResearch.WordTrace]
  refine ⟨8410454126601057742368109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11213938835468076989824145 8410454126601057742368109)
  ·
    refine ⟨3153920297475396653388041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8410454126601057742368109 3153920297475396653388041)
    ·
      refine ⟨2365440223106547490041031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3153920297475396653388041 2365440223106547490041031)
      ·
        refine ⟨3548160334659821235061547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2365440223106547490041031 3548160334659821235061547)
        ·
          refine ⟨5322240501989731852592321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3548160334659821235061547 5322240501989731852592321)
          ·
            refine ⟨3991680376492298889444241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5322240501989731852592321 3991680376492298889444241)
            ·
              refine ⟨2993760282369224167083181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3991680376492298889444241 2993760282369224167083181)
              ·
                refine ⟨1122660105888459062656193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2993760282369224167083181 1122660105888459062656193)
                ·
                  refine ⟨841995079416344296992145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1122660105888459062656193 841995079416344296992145)
                  ·
                    refine ⟨631496309562258222744109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 841995079416344296992145 631496309562258222744109)
                    ·
                      refine ⟨236811116085846833529041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 631496309562258222744109 236811116085846833529041)
                      ·
                        rfl

theorem cell23_461188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_461188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461188 prefixEnd_461188 := by exact prefixLift 461188
  have htrace : WordTrace (prefixWord ++ tailWord_461188) baseStart_461188 baseEnd_461188 := by
    simpa [prefixWord, tailWord_461188, baseEnd_461188] using wordTrace_append hprefix tailTrace_461188
  have hstable : (prefixWord ++ tailWord_461188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461188).length < 2 ^ (prefixWord ++ tailWord_461188).sum := by decide
  have hdescent : baseEnd_461188 < baseStart_461188 := by decide
  rcases family_descends (prefixWord ++ tailWord_461188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461195 : List Nat := [1, 1, 1, 1, 4, 4, 3, 3, 1, 4]
def baseStart_461195 : Nat := 118140960795 + 461195 * 2 ^ 59
def prefixEnd_461195 : Nat := 4983230072969 + 3 ^ 40 * 461195 * 2
def baseEnd_461195 : Nat := 78938236816809435380503

theorem tailTrace_461195 : CollatzResearch.WordTrace tailWord_461195 prefixEnd_461195 78938236816809435380503 := by
  unfold tailWord_461195
  simp only [CollatzResearch.WordTrace]
  refine ⟨16821163564176755680241039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11214109042784503786827359 16821163564176755680241039)
  ·
    refine ⟨25231745346265133520361559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16821163564176755680241039 25231745346265133520361559)
    ·
      refine ⟨37847618019397700280542339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25231745346265133520361559 37847618019397700280542339)
      ·
        refine ⟨56771427029096550420813509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37847618019397700280542339 56771427029096550420813509)
        ·
          refine ⟨10644642567955603203902533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56771427029096550420813509 10644642567955603203902533)
          ·
            refine ⟨1995870481491675600731725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10644642567955603203902533 1995870481491675600731725)
            ·
              refine ⟨748451430559378350274397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1995870481491675600731725 748451430559378350274397)
              ·
                refine ⟨280669286459766881352899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 748451430559378350274397 280669286459766881352899)
                ·
                  refine ⟨421003929689650322029349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 280669286459766881352899 421003929689650322029349)
                  ·
                    refine ⟨78938236816809435380503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 421003929689650322029349 78938236816809435380503)
                    ·
                      rfl

theorem cell23_461195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3, 1, 4].length) (baseStart_461195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461195 prefixEnd_461195 := by exact prefixLift 461195
  have htrace : WordTrace (prefixWord ++ tailWord_461195) baseStart_461195 baseEnd_461195 := by
    simpa [prefixWord, tailWord_461195, baseEnd_461195] using wordTrace_append hprefix tailTrace_461195
  have hstable : (prefixWord ++ tailWord_461195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461195).length < 2 ^ (prefixWord ++ tailWord_461195).sum := by decide
  have hdescent : baseEnd_461195 < baseStart_461195 := by decide
  rcases family_descends (prefixWord ++ tailWord_461195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461221 : List Nat := [1, 3, 1, 2, 1, 1, 4, 2, 3, 5]
def baseStart_461221 : Nat := 118140960795 + 461221 * 2 ^ 59
def prefixEnd_461221 : Nat := 4983230072969 + 3 ^ 40 * 461221 * 2
def baseEnd_461221 : Nat := 78942686982481734805463

theorem tailTrace_461221 : CollatzResearch.WordTrace tailWord_461221 prefixEnd_461221 78942686982481734805463 := by
  unfold tailWord_461221
  simp only [CollatzResearch.WordTrace]
  refine ⟨16822111862082562120687517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11214741241388374747125011 16822111862082562120687517)
  ·
    refine ⟨6308291948280960795257819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16822111862082562120687517 6308291948280960795257819)
    ·
      refine ⟨9462437922421441192886729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6308291948280960795257819 9462437922421441192886729)
      ·
        refine ⟨7096828441816080894665047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9462437922421441192886729 7096828441816080894665047)
        ·
          refine ⟨10645242662724121341997571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7096828441816080894665047 10645242662724121341997571)
          ·
            refine ⟨15967863994086182012996357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10645242662724121341997571 15967863994086182012996357)
            ·
              refine ⟨2993974498891159127436817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15967863994086182012996357 2993974498891159127436817)
              ·
                refine ⟨2245480874168369345577613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2993974498891159127436817 2245480874168369345577613)
                ·
                  refine ⟨842055327813138504591605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2245480874168369345577613 842055327813138504591605)
                  ·
                    refine ⟨78942686982481734805463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 842055327813138504591605 78942686982481734805463)
                    ·
                      rfl

theorem cell23_461221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 5].length) (baseStart_461221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461221 prefixEnd_461221 := by exact prefixLift 461221
  have htrace : WordTrace (prefixWord ++ tailWord_461221) baseStart_461221 baseEnd_461221 := by
    simpa [prefixWord, tailWord_461221, baseEnd_461221] using wordTrace_append hprefix tailTrace_461221
  have hstable : (prefixWord ++ tailWord_461221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461221).length < 2 ^ (prefixWord ++ tailWord_461221).sum := by decide
  have hdescent : baseEnd_461221 < baseStart_461221 := by decide
  rcases family_descends (prefixWord ++ tailWord_461221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461228 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 6, 3, 2]
def baseStart_461228 : Nat := 118140960795 + 461228 * 2 ^ 59
def prefixEnd_461228 : Nat := 4983230072969 + 3 ^ 40 * 461228 * 2
def baseEnd_461228 : Nat := 236831655312026677028857

theorem tailTrace_461228 : CollatzResearch.WordTrace tailWord_461228 prefixEnd_461228 236831655312026677028857 := by
  unfold tailWord_461228
  simp only [CollatzResearch.WordTrace]
  refine ⟨8411183586528601158096169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11214911448704801544128225 8411183586528601158096169)
  ·
    refine ⟨6308387689896450868572127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8411183586528601158096169 6308387689896450868572127)
    ·
      refine ⟨9462581534844676302858191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6308387689896450868572127 9462581534844676302858191)
      ·
        refine ⟨14193872302267014454287287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9462581534844676302858191 14193872302267014454287287)
        ·
          refine ⟨21290808453400521681430931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14193872302267014454287287 21290808453400521681430931)
          ·
            refine ⟨31936212680100782522146397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21290808453400521681430931 31936212680100782522146397)
            ·
              refine ⟨11976079755037793445804899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31936212680100782522146397 11976079755037793445804899)
              ·
                refine ⟨17964119632556690168707349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11976079755037793445804899 17964119632556690168707349)
                ·
                  refine ⟨842068107776094851658157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17964119632556690168707349 842068107776094851658157)
                  ·
                    refine ⟨315775540416035569371809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 842068107776094851658157 315775540416035569371809)
                    ·
                      refine ⟨236831655312026677028857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 315775540416035569371809 236831655312026677028857)
                      ·
                        rfl

theorem cell23_461228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 3, 2].length) (baseStart_461228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461228 prefixEnd_461228 := by exact prefixLift 461228
  have htrace : WordTrace (prefixWord ++ tailWord_461228) baseStart_461228 baseEnd_461228 := by
    simpa [prefixWord, tailWord_461228, baseEnd_461228] using wordTrace_append hprefix tailTrace_461228
  have hstable : (prefixWord ++ tailWord_461228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461228).length < 2 ^ (prefixWord ++ tailWord_461228).sum := by decide
  have hdescent : baseEnd_461228 < baseStart_461228 := by decide
  rcases family_descends (prefixWord ++ tailWord_461228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461245 : List Nat := [1, 4, 1, 2, 2, 2, 1, 3, 2, 3, 2]
def baseStart_461245 : Nat := 118140960795 + 461245 * 2 ^ 59
def prefixEnd_461245 : Nat := 4983230072969 + 3 ^ 40 * 461245 * 2
def baseEnd_461245 : Nat := 236840384483153110516279

theorem tailTrace_461245 : CollatzResearch.WordTrace tailWord_461245 prefixEnd_461245 236840384483153110516279 := by
  unfold tailWord_461245
  simp only [CollatzResearch.WordTrace]
  refine ⟨16822987213995614219561189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11215324809330409479707459 16822987213995614219561189)
  ·
    refine ⟨3154310102624177666167723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16822987213995614219561189 3154310102624177666167723)
    ·
      refine ⟨4731465153936266499251585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3154310102624177666167723 4731465153936266499251585)
      ·
        refine ⟨3548598865452199874438689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4731465153936266499251585 3548598865452199874438689)
        ·
          refine ⟨2661449149089149905829017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3548598865452199874438689 2661449149089149905829017)
          ·
            refine ⟨1996086861816862429371763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2661449149089149905829017 1996086861816862429371763)
            ·
              refine ⟨2994130292725293644057645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1996086861816862429371763 2994130292725293644057645)
              ·
                refine ⟨1122798859771985116521617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2994130292725293644057645 1122798859771985116521617)
                ·
                  refine ⟨842099144828988837391213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1122798859771985116521617 842099144828988837391213)
                  ·
                    refine ⟨315787179310870814021705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 842099144828988837391213 315787179310870814021705)
                    ·
                      refine ⟨236840384483153110516279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 315787179310870814021705 236840384483153110516279)
                      ·
                        rfl

theorem cell23_461245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_461245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461245 prefixEnd_461245 := by exact prefixLift 461245
  have htrace : WordTrace (prefixWord ++ tailWord_461245) baseStart_461245 baseEnd_461245 := by
    simpa [prefixWord, tailWord_461245, baseEnd_461245] using wordTrace_append hprefix tailTrace_461245
  have hstable : (prefixWord ++ tailWord_461245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461245).length < 2 ^ (prefixWord ++ tailWord_461245).sum := by decide
  have hdescent : baseEnd_461245 < baseStart_461245 := by decide
  rcases family_descends (prefixWord ++ tailWord_461245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461255 : List Nat := [1, 1, 4, 1, 1, 5, 3, 1, 1, 5]
def baseStart_461255 : Nat := 118140960795 + 461255 * 2 ^ 59
def prefixEnd_461255 : Nat := 4983230072969 + 3 ^ 40 * 461255 * 2
def baseEnd_461255 : Nat := 78948506429899357130411

theorem tailTrace_461255 : CollatzResearch.WordTrace tailWord_461255 prefixEnd_461255 78948506429899357130411 := by
  unfold tailWord_461255
  simp only [CollatzResearch.WordTrace]
  refine ⟨16823351943959385927425219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11215567962639590618283479 16823351943959385927425219)
  ·
    refine ⟨25235027915939078891137829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16823351943959385927425219 25235027915939078891137829)
    ·
      refine ⟨4731567734238577292088343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25235027915939078891137829 4731567734238577292088343)
      ·
        refine ⟨7097351601357865938132515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4731567734238577292088343 7097351601357865938132515)
        ·
          refine ⟨10646027402036798907198773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7097351601357865938132515 10646027402036798907198773)
          ·
            refine ⟨998065068940949897549885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10646027402036798907198773 998065068940949897549885)
            ·
              refine ⟨374274400852856211581207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 998065068940949897549885 374274400852856211581207)
              ·
                refine ⟨561411601279284317371811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374274400852856211581207 561411601279284317371811)
                ·
                  refine ⟨842117401918926476057717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 561411601279284317371811 842117401918926476057717)
                  ·
                    refine ⟨78948506429899357130411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 842117401918926476057717 78948506429899357130411)
                    ·
                      rfl

theorem cell23_461255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_461255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461255 prefixEnd_461255 := by exact prefixLift 461255
  have htrace : WordTrace (prefixWord ++ tailWord_461255) baseStart_461255 baseEnd_461255 := by
    simpa [prefixWord, tailWord_461255, baseEnd_461255] using wordTrace_append hprefix tailTrace_461255
  have hstable : (prefixWord ++ tailWord_461255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461255).length < 2 ^ (prefixWord ++ tailWord_461255).sum := by decide
  have hdescent : baseEnd_461255 < baseStart_461255 := by decide
  rcases family_descends (prefixWord ++ tailWord_461255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461269 : List Nat := [1, 3, 2, 3, 1, 2, 4, 2, 1, 1, 3]
def baseStart_461269 : Nat := 118140960795 + 461269 * 2 ^ 59
def prefixEnd_461269 : Nat := 4983230072969 + 3 ^ 40 * 461269 * 2
def baseEnd_461269 : Nat := 236852708018861016616169

theorem tailTrace_461269 : CollatzResearch.WordTrace tailWord_461269 prefixEnd_461269 236852708018861016616169 := by
  unfold tailWord_461269
  simp only [CollatzResearch.WordTrace]
  refine ⟨16823862565908666318434861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11215908377272444212289907 16823862565908666318434861)
  ·
    refine ⟨6308948462215749869413073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16823862565908666318434861 6308948462215749869413073)
    ·
      refine ⟨4731711346661812402059805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6308948462215749869413073 4731711346661812402059805)
      ·
        refine ⟨1774391754998179650772427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4731711346661812402059805 1774391754998179650772427)
        ·
          refine ⟨2661587632497269476158641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1774391754998179650772427 2661587632497269476158641)
          ·
            refine ⟨1996190724372952107118981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2661587632497269476158641 1996190724372952107118981)
            ·
              refine ⟨374285760819928520084809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1996190724372952107118981 374285760819928520084809)
              ·
                refine ⟨280714320614946390063607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 374285760819928520084809 280714320614946390063607)
                ·
                  refine ⟨421071480922419585095411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 280714320614946390063607 421071480922419585095411)
                  ·
                    refine ⟨631607221383629377643117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 421071480922419585095411 631607221383629377643117)
                    ·
                      refine ⟨236852708018861016616169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 631607221383629377643117 236852708018861016616169)
                      ·
                        rfl

theorem cell23_461269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_461269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461269 prefixEnd_461269 := by exact prefixLift 461269
  have htrace : WordTrace (prefixWord ++ tailWord_461269) baseStart_461269 baseEnd_461269 := by
    simpa [prefixWord, tailWord_461269, baseEnd_461269] using wordTrace_append hprefix tailTrace_461269
  have hstable : (prefixWord ++ tailWord_461269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461269).length < 2 ^ (prefixWord ++ tailWord_461269).sum := by decide
  have hdescent : baseEnd_461269 < baseStart_461269 := by decide
  rcases family_descends (prefixWord ++ tailWord_461269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461285 : List Nat := [1, 3, 1, 5, 2, 1, 2, 1, 1, 6]
def baseStart_461285 : Nat := 118140960795 + 461285 * 2 ^ 59
def prefixEnd_461285 : Nat := 4983230072969 + 3 ^ 40 * 461285 * 2
def baseEnd_461285 : Nat := 78953641236444318005365

theorem tailTrace_461285 : CollatzResearch.WordTrace tailWord_461285 prefixEnd_461285 78953641236444318005365 := by
  unfold tailWord_461285
  simp only [CollatzResearch.WordTrace]
  refine ⟨16824446133850701051017309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11216297422567134034011539 16824446133850701051017309)
  ·
    refine ⟨6309167300194012894131491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16824446133850701051017309 6309167300194012894131491)
    ·
      refine ⟨9463750950291019341197237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6309167300194012894131491 9463750950291019341197237)
      ·
        refine ⟨887226651589783063237241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9463750950291019341197237 887226651589783063237241)
        ·
          refine ⟨665419988692337297427931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 887226651589783063237241 665419988692337297427931)
          ·
            refine ⟨998129983038505946141897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665419988692337297427931 998129983038505946141897)
            ·
              refine ⟨748597487278879459606423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 998129983038505946141897 748597487278879459606423)
              ·
                refine ⟨1122896230918319189409635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748597487278879459606423 1122896230918319189409635)
                ·
                  refine ⟨1684344346377478784114453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1122896230918319189409635 1684344346377478784114453)
                  ·
                    refine ⟨78953641236444318005365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1684344346377478784114453 78953641236444318005365)
                    ·
                      rfl

theorem cell23_461285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 6].length) (baseStart_461285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461285 prefixEnd_461285 := by exact prefixLift 461285
  have htrace : WordTrace (prefixWord ++ tailWord_461285) baseStart_461285 baseEnd_461285 := by
    simpa [prefixWord, tailWord_461285, baseEnd_461285] using wordTrace_append hprefix tailTrace_461285
  have hstable : (prefixWord ++ tailWord_461285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461285).length < 2 ^ (prefixWord ++ tailWord_461285).sum := by decide
  have hdescent : baseEnd_461285 < baseStart_461285 := by decide
  rcases family_descends (prefixWord ++ tailWord_461285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461288 : List Nat := [2, 1, 4, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_461288 : Nat := 118140960795 + 461288 * 2 ^ 59
def prefixEnd_461288 : Nat := 4983230072969 + 3 ^ 40 * 461288 * 2
def baseEnd_461288 : Nat := 236862464151296442278581

theorem tailTrace_461288 : CollatzResearch.WordTrace tailWord_461288 prefixEnd_461288 236862464151296442278581 := by
  unfold tailWord_461288
  simp only [CollatzResearch.WordTrace]
  refine ⟨8412277776419916281688259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11216370368559888375584345 8412277776419916281688259)
  ·
    refine ⟨12618416664629874422532389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8412277776419916281688259 12618416664629874422532389)
    ·
      refine ⟨2365953124618101454224823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12618416664629874422532389 2365953124618101454224823)
      ·
        refine ⟨3548929686927152181337235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2365953124618101454224823 3548929686927152181337235)
        ·
          refine ⟨5323394530390728272005853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3548929686927152181337235 5323394530390728272005853)
          ·
            refine ⟨1996272948896523102002195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5323394530390728272005853 1996272948896523102002195)
            ·
              refine ⟨2994409423344784653003293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1996272948896523102002195 2994409423344784653003293)
              ·
                refine ⟨1122903533754294244876235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2994409423344784653003293 1122903533754294244876235)
                ·
                  refine ⟨1684355300631441367314353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1122903533754294244876235 1684355300631441367314353)
                  ·
                    refine ⟨1263266475473581025485765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1684355300631441367314353 1263266475473581025485765)
                    ·
                      refine ⟨236862464151296442278581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1263266475473581025485765 236862464151296442278581)
                      ·
                        rfl

theorem cell23_461288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_461288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461288 prefixEnd_461288 := by exact prefixLift 461288
  have htrace : WordTrace (prefixWord ++ tailWord_461288) baseStart_461288 baseEnd_461288 := by
    simpa [prefixWord, tailWord_461288, baseEnd_461288] using wordTrace_append hprefix tailTrace_461288
  have hstable : (prefixWord ++ tailWord_461288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461288).length < 2 ^ (prefixWord ++ tailWord_461288).sum := by decide
  have hdescent : baseEnd_461288 < baseStart_461288 := by decide
  rcases family_descends (prefixWord ++ tailWord_461288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461309 : List Nat := [1, 4, 1, 1, 1, 3, 4, 3, 1, 2, 2]
def baseStart_461309 : Nat := 118140960795 + 461309 * 2 ^ 59
def prefixEnd_461309 : Nat := 4983230072969 + 3 ^ 40 * 461309 * 2
def baseEnd_461309 : Nat := 236873247245040860115985

theorem tailTrace_461309 : CollatzResearch.WordTrace tailWord_461309 prefixEnd_461309 236873247245040860115985 := by
  unfold tailWord_461309
  simp only [CollatzResearch.WordTrace]
  refine ⟨16825321485763753149890981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11216880990509168766593987 16825321485763753149890981)
  ·
    refine ⟨3154747778580703715604559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16825321485763753149890981 3154747778580703715604559)
    ·
      refine ⟨4732121667871055573406839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3154747778580703715604559 4732121667871055573406839)
      ·
        refine ⟨7098182501806583360110259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4732121667871055573406839 7098182501806583360110259)
        ·
          refine ⟨10647273752709875040165389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7098182501806583360110259 10647273752709875040165389)
          ·
            refine ⟨3992727657266203140062021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10647273752709875040165389 3992727657266203140062021)
            ·
              refine ⟨748636435737413088761629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3992727657266203140062021 748636435737413088761629)
              ·
                refine ⟨280738663401529908285611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 748636435737413088761629 280738663401529908285611)
                ·
                  refine ⟨421107995102294862428417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 280738663401529908285611 421107995102294862428417)
                  ·
                    refine ⟨315830996326721146821313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 421107995102294862428417 315830996326721146821313)
                    ·
                      refine ⟨236873247245040860115985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 315830996326721146821313 236873247245040860115985)
                      ·
                        rfl

theorem cell23_461309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3, 1, 2, 2].length) (baseStart_461309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461309 prefixEnd_461309 := by exact prefixLift 461309
  have htrace : WordTrace (prefixWord ++ tailWord_461309) baseStart_461309 baseEnd_461309 := by
    simpa [prefixWord, tailWord_461309, baseEnd_461309] using wordTrace_append hprefix tailTrace_461309
  have hstable : (prefixWord ++ tailWord_461309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461309).length < 2 ^ (prefixWord ++ tailWord_461309).sum := by decide
  have hdescent : baseEnd_461309 < baseStart_461309 := by decide
  rcases family_descends (prefixWord ++ tailWord_461309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461319 : List Nat := [1, 1, 4, 3, 4, 1, 1, 2, 2, 4]
def baseStart_461319 : Nat := 118140960795 + 461319 * 2 ^ 59
def prefixEnd_461319 : Nat := 4983230072969 + 3 ^ 40 * 461319 * 2
def baseEnd_461319 : Nat := 78959460683861940330313

theorem tailTrace_461319 : CollatzResearch.WordTrace tailWord_461319 prefixEnd_461319 78959460683861940330313 := by
  unfold tailWord_461319
  simp only [CollatzResearch.WordTrace]
  refine ⟨16825686215727524857755011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11217124143818349905170007 16825686215727524857755011)
  ·
    refine ⟨25238529323591287286632517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16825686215727524857755011 25238529323591287286632517)
    ·
      refine ⟨4732224248173366366243597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25238529323591287286632517 4732224248173366366243597)
      ·
        refine ⟨1774584093065012387341349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4732224248173366366243597 1774584093065012387341349)
        ·
          refine ⟨332734517449689822626503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1774584093065012387341349 332734517449689822626503)
          ·
            refine ⟨499101776174534733939755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332734517449689822626503 499101776174534733939755)
            ·
              refine ⟨748652664261802100909633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499101776174534733939755 748652664261802100909633)
              ·
                refine ⟨561489498196351575682225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 748652664261802100909633 561489498196351575682225)
                ·
                  refine ⟨421117123647263681761669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 561489498196351575682225 421117123647263681761669)
                  ·
                    refine ⟨78959460683861940330313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 421117123647263681761669 78959460683861940330313)
                    ·
                      rfl

theorem cell23_461319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_461319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461319 prefixEnd_461319 := by exact prefixLift 461319
  have htrace : WordTrace (prefixWord ++ tailWord_461319) baseStart_461319 baseEnd_461319 := by
    simpa [prefixWord, tailWord_461319, baseEnd_461319] using wordTrace_append hprefix tailTrace_461319
  have hstable : (prefixWord ++ tailWord_461319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461319).length < 2 ^ (prefixWord ++ tailWord_461319).sum := by decide
  have hdescent : baseEnd_461319 < baseStart_461319 := by decide
  rcases family_descends (prefixWord ++ tailWord_461319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461321 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 4, 2, 5]
def baseStart_461321 : Nat := 118140960795 + 461321 * 2 ^ 59
def prefixEnd_461321 : Nat := 4983230072969 + 3 ^ 40 * 461321 * 2
def baseEnd_461321 : Nat := 236879409012894813165929

theorem tailTrace_461321 : CollatzResearch.WordTrace tailWord_461321 prefixEnd_461321 236879409012894813165929 := by
  unfold tailWord_461321
  simp only [CollatzResearch.WordTrace]
  refine ⟨16825759161720279199327817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11217172774480186132885211 16825759161720279199327817)
  ·
    refine ⟨12619319371290209399495863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16825759161720279199327817 12619319371290209399495863)
    ·
      refine ⟨18928979056935314099243795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12619319371290209399495863 18928979056935314099243795)
      ·
        refine ⟨28393468585402971148865693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18928979056935314099243795 28393468585402971148865693)
        ·
          refine ⟨10647550719526114180824635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28393468585402971148865693 10647550719526114180824635)
          ·
            refine ⟨15971326079289171271236953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10647550719526114180824635 15971326079289171271236953)
            ·
              refine ⟨11978494559466878453427715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15971326079289171271236953 11978494559466878453427715)
              ·
                refine ⟨17967741839200317680141573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11978494559466878453427715 17967741839200317680141573)
                ·
                  refine ⟨3368951594850059565026545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17967741839200317680141573 3368951594850059565026545)
                  ·
                    refine ⟨2526713696137544673769909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3368951594850059565026545 2526713696137544673769909)
                    ·
                      refine ⟨236879409012894813165929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2526713696137544673769909 236879409012894813165929)
                      ·
                        rfl

theorem cell23_461321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 2, 5].length) (baseStart_461321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461321 prefixEnd_461321 := by exact prefixLift 461321
  have htrace : WordTrace (prefixWord ++ tailWord_461321) baseStart_461321 baseEnd_461321 := by
    simpa [prefixWord, tailWord_461321, baseEnd_461321] using wordTrace_append hprefix tailTrace_461321
  have hstable : (prefixWord ++ tailWord_461321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461321).length < 2 ^ (prefixWord ++ tailWord_461321).sum := by decide
  have hdescent : baseEnd_461321 < baseStart_461321 := by decide
  rcases family_descends (prefixWord ++ tailWord_461321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461365 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 3, 4, 2]
def baseStart_461365 : Nat := 118140960795 + 461365 * 2 ^ 59
def prefixEnd_461365 : Nat := 4983230072969 + 3 ^ 40 * 461365 * 2
def baseEnd_461365 : Nat := 236902002161692641015727

theorem tailTrace_461365 : CollatzResearch.WordTrace tailWord_461365 prefixEnd_461365 236902002161692641015727 := by
  unfold tailWord_461365
  simp only [CollatzResearch.WordTrace]
  refine ⟨16827363973560874713929549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11218242649040583142619699 16827363973560874713929549)
  ·
    refine ⟨6310261490085328017723581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16827363973560874713929549 6310261490085328017723581)
    ·
      refine ⟨2366348058781998006646343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6310261490085328017723581 2366348058781998006646343)
      ·
        refine ⟨3549522088172997009969515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2366348058781998006646343 3549522088172997009969515)
        ·
          refine ⟨5324283132259495514954273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3549522088172997009969515 5324283132259495514954273)
          ·
            refine ⟨3993212349194621636215705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5324283132259495514954273 3993212349194621636215705)
            ·
              refine ⟨2994909261895966227161779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3993212349194621636215705 2994909261895966227161779)
              ·
                refine ⟨4492363892843949340742669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2994909261895966227161779 4492363892843949340742669)
                ·
                  refine ⟨1684636459816481002778501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4492363892843949340742669 1684636459816481002778501)
                  ·
                    refine ⟨315869336215590188020969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1684636459816481002778501 315869336215590188020969)
                    ·
                      refine ⟨236902002161692641015727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 315869336215590188020969 236902002161692641015727)
                      ·
                        rfl

theorem cell23_461365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_461365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461365 prefixEnd_461365 := by exact prefixLift 461365
  have htrace : WordTrace (prefixWord ++ tailWord_461365) baseStart_461365 baseEnd_461365 := by
    simpa [prefixWord, tailWord_461365, baseEnd_461365] using wordTrace_append hprefix tailTrace_461365
  have hstable : (prefixWord ++ tailWord_461365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461365).length < 2 ^ (prefixWord ++ tailWord_461365).sum := by decide
  have hdescent : baseEnd_461365 < baseStart_461365 := by decide
  rcases family_descends (prefixWord ++ tailWord_461365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461368 : List Nat := [2, 1, 2, 1, 4, 1, 3, 1, 2, 1, 5]
def baseStart_461368 : Nat := 118140960795 + 461368 * 2 ^ 59
def prefixEnd_461368 : Nat := 4983230072969 + 3 ^ 40 * 461368 * 2
def baseEnd_461368 : Nat := 236903542603656129278213

theorem tailTrace_461368 : CollatzResearch.WordTrace tailWord_461368 prefixEnd_461368 236903542603656129278213 := by
  unfold tailWord_461368
  simp only [CollatzResearch.WordTrace]
  refine ⟨8413736696275003113144379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11218315595033337484192505 8413736696275003113144379)
  ·
    refine ⟨12620605044412504669716569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8413736696275003113144379 12620605044412504669716569)
    ·
      refine ⟨9465453783309378502287427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12620605044412504669716569 9465453783309378502287427)
      ·
        refine ⟨14198180674964067753431141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9465453783309378502287427 14198180674964067753431141)
        ·
          refine ⟨2662158876555762703768339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14198180674964067753431141 2662158876555762703768339)
          ·
            refine ⟨3993238314833644055652509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2662158876555762703768339 3993238314833644055652509)
            ·
              refine ⟨1497464368062616520869691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3993238314833644055652509 1497464368062616520869691)
              ·
                refine ⟨2246196552093924781304537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1497464368062616520869691 2246196552093924781304537)
                ·
                  refine ⟨1684647414070443585978403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2246196552093924781304537 1684647414070443585978403)
                  ·
                    refine ⟨2526971121105665378967605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1684647414070443585978403 2526971121105665378967605)
                    ·
                      refine ⟨236903542603656129278213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2526971121105665378967605 236903542603656129278213)
                      ·
                        rfl

theorem cell23_461368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_461368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461368 prefixEnd_461368 := by exact prefixLift 461368
  have htrace : WordTrace (prefixWord ++ tailWord_461368) baseStart_461368 baseEnd_461368 := by
    simpa [prefixWord, tailWord_461368, baseEnd_461368] using wordTrace_append hprefix tailTrace_461368
  have hstable : (prefixWord ++ tailWord_461368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461368).length < 2 ^ (prefixWord ++ tailWord_461368).sum := by decide
  have hdescent : baseEnd_461368 < baseStart_461368 := by decide
  rcases family_descends (prefixWord ++ tailWord_461368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461455 : List Nat := [1, 1, 2, 1, 1, 1, 1, 7, 2, 4, 2]
def baseStart_461455 : Nat := 118140960795 + 461455 * 2 ^ 59
def prefixEnd_461455 : Nat := 4983230072969 + 3 ^ 40 * 461455 * 2
def baseEnd_461455 : Nat := 236948215420597288890313

theorem tailTrace_461455 : CollatzResearch.WordTrace tailWord_461455 prefixEnd_461455 236948215420597288890313 := by
  unfold tailWord_461455
  simp only [CollatzResearch.WordTrace]
  refine ⟨16830646543234820084705819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11220431028823213389803879 16830646543234820084705819)
  ·
    refine ⟨25245969814852230127058729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16830646543234820084705819 25245969814852230127058729)
    ·
      refine ⟨18934477361139172595294047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25245969814852230127058729 18934477361139172595294047)
      ·
        refine ⟨28401716041708758892941071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18934477361139172595294047 28401716041708758892941071)
        ·
          refine ⟨42602574062563138339411607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28401716041708758892941071 42602574062563138339411607)
          ·
            refine ⟨63903861093844707509117411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42602574062563138339411607 63903861093844707509117411)
            ·
              refine ⟨95855791640767061263676117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63903861093844707509117411 95855791640767061263676117)
              ·
                refine ⟨2246620116580477998367409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 95855791640767061263676117 2246620116580477998367409)
                ·
                  refine ⟨1684965087435358498775557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2246620116580477998367409 1684965087435358498775557)
                  ·
                    refine ⟨315930953894129718520417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1684965087435358498775557 315930953894129718520417)
                    ·
                      refine ⟨236948215420597288890313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 315930953894129718520417 236948215420597288890313)
                      ·
                        rfl

theorem cell23_461455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 4, 2].length) (baseStart_461455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461455 prefixEnd_461455 := by exact prefixLift 461455
  have htrace : WordTrace (prefixWord ++ tailWord_461455) baseStart_461455 baseEnd_461455 := by
    simpa [prefixWord, tailWord_461455, baseEnd_461455] using wordTrace_append hprefix tailTrace_461455
  have hstable : (prefixWord ++ tailWord_461455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461455).length < 2 ^ (prefixWord ++ tailWord_461455).sum := by decide
  have hdescent : baseEnd_461455 < baseStart_461455 := by decide
  rcases family_descends (prefixWord ++ tailWord_461455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461465 : List Nat := [1, 2, 1, 2, 1, 2, 5, 2, 3, 4]
def baseStart_461465 : Nat := 118140960795 + 461465 * 2 ^ 59
def prefixEnd_461465 : Nat := 4983230072969 + 3 ^ 40 * 461465 * 2
def baseEnd_461465 : Nat := 78984450075714083255089

theorem tailTrace_461465 : CollatzResearch.WordTrace tailWord_461465 prefixEnd_461465 78984450075714083255089 := by
  unfold tailWord_461465
  simp only [CollatzResearch.WordTrace]
  refine ⟨16831011273198591792569849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11220674182132394528379899 16831011273198591792569849)
  ·
    refine ⟨12623258454898943844427387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16831011273198591792569849 12623258454898943844427387)
    ·
      refine ⟨18934887682348415766641081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12623258454898943844427387 18934887682348415766641081)
      ·
        refine ⟨14201165761761311824980811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18934887682348415766641081 14201165761761311824980811)
        ·
          refine ⟨21301748642641967737471217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14201165761761311824980811 21301748642641967737471217)
          ·
            refine ⟨15976311481981475803103413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21301748642641967737471217 15976311481981475803103413)
            ·
              refine ⟨1497779201435763356540945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15976311481981475803103413 1497779201435763356540945)
              ·
                refine ⟨1123334401076822517405709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1497779201435763356540945 1123334401076822517405709)
                ·
                  refine ⟨421250400403808444027141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1123334401076822517405709 421250400403808444027141)
                  ·
                    refine ⟨78984450075714083255089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 421250400403808444027141 78984450075714083255089)
                    ·
                      rfl

theorem cell23_461465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3, 4].length) (baseStart_461465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461465 prefixEnd_461465 := by exact prefixLift 461465
  have htrace : WordTrace (prefixWord ++ tailWord_461465) baseStart_461465 baseEnd_461465 := by
    simpa [prefixWord, tailWord_461465, baseEnd_461465] using wordTrace_append hprefix tailTrace_461465
  have hstable : (prefixWord ++ tailWord_461465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461465).length < 2 ^ (prefixWord ++ tailWord_461465).sum := by decide
  have hdescent : baseEnd_461465 < baseStart_461465 := by decide
  rcases family_descends (prefixWord ++ tailWord_461465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461475 : List Nat := [1, 1, 1, 4, 1, 1, 2, 5, 2, 2, 3]
def baseStart_461475 : Nat := 118140960795 + 461475 * 2 ^ 59
def prefixEnd_461475 : Nat := 4983230072969 + 3 ^ 40 * 461475 * 2
def baseEnd_461475 : Nat := 236958485033687210640221

theorem tailTrace_461475 : CollatzResearch.WordTrace tailWord_461475 prefixEnd_461475 236958485033687210640221 := by
  unfold tailWord_461475
  simp only [CollatzResearch.WordTrace]
  refine ⟨16831376003162363500433879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11220917335441575666955919 16831376003162363500433879)
  ·
    refine ⟨25247064004743545250650819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16831376003162363500433879 25247064004743545250650819)
    ·
      refine ⟨37870596007115317875976229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25247064004743545250650819 37870596007115317875976229)
      ·
        refine ⟨7100736751334122101745543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37870596007115317875976229 7100736751334122101745543)
        ·
          refine ⟨10651105127001183152618315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7100736751334122101745543 10651105127001183152618315)
          ·
            refine ⟨15976657690501774728927473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10651105127001183152618315 15976657690501774728927473)
            ·
              refine ⟨11982493267876331046695605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15976657690501774728927473 11982493267876331046695605)
              ·
                refine ⟨1123358743863406035627713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11982493267876331046695605 1123358743863406035627713)
                ·
                  refine ⟨842519057897554526720785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1123358743863406035627713 842519057897554526720785)
                  ·
                    refine ⟨631889293423165895040589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 842519057897554526720785 631889293423165895040589)
                    ·
                      refine ⟨236958485033687210640221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 631889293423165895040589 236958485033687210640221)
                      ·
                        rfl

theorem cell23_461475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_461475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461475 prefixEnd_461475 := by exact prefixLift 461475
  have htrace : WordTrace (prefixWord ++ tailWord_461475) baseStart_461475 baseEnd_461475 := by
    simpa [prefixWord, tailWord_461475, baseEnd_461475] using wordTrace_append hprefix tailTrace_461475
  have hstable : (prefixWord ++ tailWord_461475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461475).length < 2 ^ (prefixWord ++ tailWord_461475).sum := by decide
  have hdescent : baseEnd_461475 < baseStart_461475 := by decide
  rcases family_descends (prefixWord ++ tailWord_461475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461485 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_461485 : Nat := 118140960795 + 461485 * 2 ^ 59
def prefixEnd_461485 : Nat := 4983230072969 + 3 ^ 40 * 461485 * 2
def baseEnd_461485 : Nat := 236963619840232171515175

theorem tailTrace_461485 : CollatzResearch.WordTrace tailWord_461485 prefixEnd_461485 236963619840232171515175 := by
  unfold tailWord_461485
  simp only [CollatzResearch.WordTrace]
  refine ⟨16831740733126135208297909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11221160488750756805531939 16831740733126135208297909)
  ·
    refine ⟨1577975693730575175777929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16831740733126135208297909 1577975693730575175777929)
    ·
      refine ⟨1183481770297931381833447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1577975693730575175777929 1183481770297931381833447)
      ·
        refine ⟨1775222655446897072750171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1183481770297931381833447 1775222655446897072750171)
        ·
          refine ⟨2662833983170345609125257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1775222655446897072750171 2662833983170345609125257)
          ·
            refine ⟨1997125487377759206843943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2662833983170345609125257 1997125487377759206843943)
            ·
              refine ⟨2995688231066638810265915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1997125487377759206843943 2995688231066638810265915)
              ·
                refine ⟨4493532346599958215398873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2995688231066638810265915 4493532346599958215398873)
                ·
                  refine ⟨3370149259949968661549155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4493532346599958215398873 3370149259949968661549155)
                  ·
                    refine ⟨5055223889924952992323733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3370149259949968661549155 5055223889924952992323733)
                    ·
                      refine ⟨236963619840232171515175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5055223889924952992323733 236963619840232171515175)
                      ·
                        rfl

theorem cell23_461485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_461485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461485 prefixEnd_461485 := by exact prefixLift 461485
  have htrace : WordTrace (prefixWord ++ tailWord_461485) baseStart_461485 baseEnd_461485 := by
    simpa [prefixWord, tailWord_461485, baseEnd_461485] using wordTrace_append hprefix tailTrace_461485
  have hstable : (prefixWord ++ tailWord_461485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461485).length < 2 ^ (prefixWord ++ tailWord_461485).sum := by decide
  have hdescent : baseEnd_461485 < baseStart_461485 := by decide
  rcases family_descends (prefixWord ++ tailWord_461485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461495 : List Nat := [1, 1, 3, 1, 6, 1, 1, 1, 8]
def baseStart_461495 : Nat := 118140960795 + 461495 * 2 ^ 59
def prefixEnd_461495 : Nat := 4983230072969 + 3 ^ 40 * 461495 * 2
def baseEnd_461495 : Nat := 26329861627419681376681

theorem tailTrace_461495 : CollatzResearch.WordTrace tailWord_461495 prefixEnd_461495 26329861627419681376681 := by
  unfold tailWord_461495
  simp only [CollatzResearch.WordTrace]
  refine ⟨16832105463089906916161939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11221403642059937944107959 16832105463089906916161939)
  ·
    refine ⟨25248158194634860374242909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16832105463089906916161939 25248158194634860374242909)
    ·
      refine ⟨9468059322988072640341091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25248158194634860374242909 9468059322988072640341091)
      ·
        refine ⟨14202088984482108960511637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9468059322988072640341091 14202088984482108960511637)
        ·
          refine ⟨665722921147598857523983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14202088984482108960511637 665722921147598857523983)
          ·
            refine ⟨998584381721398286285975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665722921147598857523983 998584381721398286285975)
            ·
              refine ⟨1497876572582097429428963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 998584381721398286285975 1497876572582097429428963)
              ·
                refine ⟨2246814858873146144143445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1497876572582097429428963 2246814858873146144143445)
                ·
                  refine ⟨26329861627419681376681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2246814858873146144143445 26329861627419681376681)
                  ·
                    rfl

theorem cell23_461495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 8].length) (baseStart_461495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461495 prefixEnd_461495 := by exact prefixLift 461495
  have htrace : WordTrace (prefixWord ++ tailWord_461495) baseStart_461495 baseEnd_461495 := by
    simpa [prefixWord, tailWord_461495, baseEnd_461495] using wordTrace_append hprefix tailTrace_461495
  have hstable : (prefixWord ++ tailWord_461495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461495).length < 2 ^ (prefixWord ++ tailWord_461495).sum := by decide
  have hdescent : baseEnd_461495 < baseStart_461495 := by decide
  rcases family_descends (prefixWord ++ tailWord_461495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461498 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8]
def baseStart_461498 : Nat := 118140960795 + 461498 * 2 ^ 59
def prefixEnd_461498 : Nat := 4983230072969 + 3 ^ 40 * 461498 * 2
def baseEnd_461498 : Nat := 236970295088740620652615

theorem tailTrace_461498 : CollatzResearch.WordTrace tailWord_461498 prefixEnd_461498 236970295088740620652615 := by
  unfold tailWord_461498
  simp only [CollatzResearch.WordTrace]
  refine ⟨4208053720519759607130287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11221476588052692285680765 4208053720519759607130287)
  ·
    refine ⟨6312080580779639410695431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4208053720519759607130287 6312080580779639410695431)
    ·
      refine ⟨9468120871169459116043147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6312080580779639410695431 9468120871169459116043147)
      ·
        refine ⟨14202181306754188674064721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9468120871169459116043147 14202181306754188674064721)
        ·
          refine ⟨10651635980065641505548541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14202181306754188674064721 10651635980065641505548541)
          ·
            refine ⟨3994363492524615564580703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10651635980065641505548541 3994363492524615564580703)
            ·
              refine ⟨5991545238786923346871055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3994363492524615564580703 5991545238786923346871055)
              ·
                refine ⟨8987317858180385020306583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5991545238786923346871055 8987317858180385020306583)
                ·
                  refine ⟨13480976787270577530459875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8987317858180385020306583 13480976787270577530459875)
                  ·
                    refine ⟨20221465180905866295689813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13480976787270577530459875 20221465180905866295689813)
                    ·
                      refine ⟨236970295088740620652615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 20221465180905866295689813 236970295088740620652615)
                      ·
                        rfl

theorem cell23_461498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_461498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461498 prefixEnd_461498 := by exact prefixLift 461498
  have htrace : WordTrace (prefixWord ++ tailWord_461498) baseStart_461498 baseEnd_461498 := by
    simpa [prefixWord, tailWord_461498, baseEnd_461498] using wordTrace_append hprefix tailTrace_461498
  have hstable : (prefixWord ++ tailWord_461498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461498).length < 2 ^ (prefixWord ++ tailWord_461498).sum := by decide
  have hdescent : baseEnd_461498 < baseStart_461498 := by decide
  rcases family_descends (prefixWord ++ tailWord_461498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461512 : List Nat := [2, 1, 3, 1, 2, 4, 3, 1, 6]
def baseStart_461512 : Nat := 118140960795 + 461512 * 2 ^ 59
def prefixEnd_461512 : Nat := 4983230072969 + 3 ^ 40 * 461512 * 2
def baseEnd_461512 : Nat := 26330831535322618430839

theorem tailTrace_461512 : CollatzResearch.WordTrace tailWord_461512 prefixEnd_461512 26330831535322618430839 := by
  unfold tailWord_461512
  simp only [CollatzResearch.WordTrace]
  refine ⟨8416362752014159409765395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11221817002685545879687193 8416362752014159409765395)
  ·
    refine ⟨12624544128021239114648093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8416362752014159409765395 12624544128021239114648093)
    ·
      refine ⟨4734204048007964667993035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12624544128021239114648093 4734204048007964667993035)
      ·
        refine ⟨7101306072011947001989553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4734204048007964667993035 7101306072011947001989553)
        ·
          refine ⟨5325979554008960251492165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7101306072011947001989553 5325979554008960251492165)
          ·
            refine ⟨998621166376680047154781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5325979554008960251492165 998621166376680047154781)
            ·
              refine ⟨374482937391255017683043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 998621166376680047154781 374482937391255017683043)
              ·
                refine ⟨561724406086882526524565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374482937391255017683043 561724406086882526524565)
                ·
                  refine ⟨26330831535322618430839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 561724406086882526524565 26330831535322618430839)
                  ·
                    rfl

theorem cell23_461512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 6].length) (baseStart_461512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461512 prefixEnd_461512 := by exact prefixLift 461512
  have htrace : WordTrace (prefixWord ++ tailWord_461512) baseStart_461512 baseEnd_461512 := by
    simpa [prefixWord, tailWord_461512, baseEnd_461512] using wordTrace_append hprefix tailTrace_461512
  have hstable : (prefixWord ++ tailWord_461512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461512).length < 2 ^ (prefixWord ++ tailWord_461512).sum := by decide
  have hdescent : baseEnd_461512 < baseStart_461512 := by decide
  rcases family_descends (prefixWord ++ tailWord_461512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461549 : List Nat := [1, 5, 1, 2, 1, 1, 3, 2, 2, 3, 2]
def baseStart_461549 : Nat := 118140960795 + 461549 * 2 ^ 59
def prefixEnd_461549 : Nat := 4983230072969 + 3 ^ 40 * 461549 * 2
def baseEnd_461549 : Nat := 236996482602119921114881

theorem tailTrace_461549 : CollatzResearch.WordTrace tailWord_461549 prefixEnd_461549 236996482602119921114881 := by
  unfold tailWord_461549
  simp only [CollatzResearch.WordTrace]
  refine ⟨16834075004894274138627701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11222716669929516092418467 16834075004894274138627701)
  ·
    refine ⟨1578194531708838200496347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16834075004894274138627701 1578194531708838200496347)
    ·
      refine ⟨2367291797563257300744521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1578194531708838200496347 2367291797563257300744521)
      ·
        refine ⟨1775468848172442975558391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2367291797563257300744521 1775468848172442975558391)
        ·
          refine ⟨2663203272258664463337587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1775468848172442975558391 2663203272258664463337587)
          ·
            refine ⟨3994804908387996695006381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2663203272258664463337587 3994804908387996695006381)
            ·
              refine ⟨1498051840645498760627393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3994804908387996695006381 1498051840645498760627393)
              ·
                refine ⟨1123538880484124070470545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1498051840645498760627393 1123538880484124070470545)
                ·
                  refine ⟨842654160363093052852909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1123538880484124070470545 842654160363093052852909)
                  ·
                    refine ⟨315995310136159894819841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 842654160363093052852909 315995310136159894819841)
                    ·
                      refine ⟨236996482602119921114881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 315995310136159894819841 236996482602119921114881)
                      ·
                        rfl

theorem cell23_461549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_461549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461549 prefixEnd_461549 := by exact prefixLift 461549
  have htrace : WordTrace (prefixWord ++ tailWord_461549) baseStart_461549 baseEnd_461549 := by
    simpa [prefixWord, tailWord_461549, baseEnd_461549] using wordTrace_append hprefix tailTrace_461549
  have hstable : (prefixWord ++ tailWord_461549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461549).length < 2 ^ (prefixWord ++ tailWord_461549).sum := by decide
  have hdescent : baseEnd_461549 < baseStart_461549 := by decide
  rcases family_descends (prefixWord ++ tailWord_461549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461565 : List Nat := [1, 4, 1, 1, 1, 1, 3, 4, 1, 1, 5]
def baseStart_461565 : Nat := 118140960795 + 461565 * 2 ^ 59
def prefixEnd_461565 : Nat := 4983230072969 + 3 ^ 40 * 461565 * 2
def baseEnd_461565 : Nat := 237004698292591858514807

theorem tailTrace_461565 : CollatzResearch.WordTrace tailWord_461565 prefixEnd_461565 237004698292591858514807 := by
  unfold tailWord_461565
  simp only [CollatzResearch.WordTrace]
  refine ⟨16834658572836308871210149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11223105715224205914140099 16834658572836308871210149)
  ·
    refine ⟨3156498482406807913351903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16834658572836308871210149 3156498482406807913351903)
    ·
      refine ⟨4734747723610211870027855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3156498482406807913351903 4734747723610211870027855)
      ·
        refine ⟨7102121585415317805041783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4734747723610211870027855 7102121585415317805041783)
        ·
          refine ⟨10653182378122976707562675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7102121585415317805041783 10653182378122976707562675)
          ·
            refine ⟨15979773567184465061344013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10653182378122976707562675 15979773567184465061344013)
            ·
              refine ⟨5992415087694174398004005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15979773567184465061344013 5992415087694174398004005)
              ·
                refine ⟨1123577828942657699625751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5992415087694174398004005 1123577828942657699625751)
                ·
                  refine ⟨1685366743413986549438627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1123577828942657699625751 1685366743413986549438627)
                  ·
                    refine ⟨2528050115120979824157941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1685366743413986549438627 2528050115120979824157941)
                    ·
                      refine ⟨237004698292591858514807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2528050115120979824157941 237004698292591858514807)
                      ·
                        rfl

theorem cell23_461565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_461565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461565 prefixEnd_461565 := by exact prefixLift 461565
  have htrace : WordTrace (prefixWord ++ tailWord_461565) baseStart_461565 baseEnd_461565 := by
    simpa [prefixWord, tailWord_461565, baseEnd_461565] using wordTrace_append hprefix tailTrace_461565
  have hstable : (prefixWord ++ tailWord_461565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461565).length < 2 ^ (prefixWord ++ tailWord_461565).sum := by decide
  have hdescent : baseEnd_461565 < baseStart_461565 := by decide
  rcases family_descends (prefixWord ++ tailWord_461565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461635 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 4]
def baseStart_461635 : Nat := 118140960795 + 461635 * 2 ^ 59
def prefixEnd_461635 : Nat := 4983230072969 + 3 ^ 40 * 461635 * 2
def baseEnd_461635 : Nat := 237040641938406584639485

theorem tailTrace_461635 : CollatzResearch.WordTrace tailWord_461635 prefixEnd_461635 237040641938406584639485 := by
  unfold tailWord_461635
  simp only [CollatzResearch.WordTrace]
  refine ⟨16837211682582710826258359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11224807788388473884172239 16837211682582710826258359)
  ·
    refine ⟨25255817523874066239387539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16837211682582710826258359 25255817523874066239387539)
    ·
      refine ⟨37883726285811099359081309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25255817523874066239387539 37883726285811099359081309)
      ·
        refine ⟨14206397357179162259655491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37883726285811099359081309 14206397357179162259655491)
        ·
          refine ⟨21309596035768743389483237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14206397357179162259655491 21309596035768743389483237)
          ·
            refine ⟨3995549256706639385528107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21309596035768743389483237 3995549256706639385528107)
            ·
              refine ⟨5993323885059959078292161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3995549256706639385528107 5993323885059959078292161)
              ·
                refine ⟨4494992913794969308719121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5993323885059959078292161 4494992913794969308719121)
                ·
                  refine ⟨3371244685346226981539341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4494992913794969308719121 3371244685346226981539341)
                  ·
                    refine ⟨1264216757004835118077253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3371244685346226981539341 1264216757004835118077253)
                    ·
                      refine ⟨237040641938406584639485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1264216757004835118077253 237040641938406584639485)
                      ·
                        rfl

theorem cell23_461635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_461635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461635 prefixEnd_461635 := by exact prefixLift 461635
  have htrace : WordTrace (prefixWord ++ tailWord_461635) baseStart_461635 baseEnd_461635 := by
    simpa [prefixWord, tailWord_461635, baseEnd_461635] using wordTrace_append hprefix tailTrace_461635
  have hstable : (prefixWord ++ tailWord_461635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461635).length < 2 ^ (prefixWord ++ tailWord_461635).sum := by decide
  have hdescent : baseEnd_461635 < baseStart_461635 := by decide
  rcases family_descends (prefixWord ++ tailWord_461635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461636 : List Nat := [2, 3, 4, 2, 1, 1, 3, 7]
def baseStart_461636 : Nat := 118140960795 + 461636 * 2 ^ 59
def prefixEnd_461636 : Nat := 4983230072969 + 3 ^ 40 * 461636 * 2
def baseEnd_461636 : Nat := 8779302052557817804703

theorem tailTrace_461636 : CollatzResearch.WordTrace tailWord_461636 prefixEnd_461636 8779302052557817804703 := by
  unfold tailWord_461636
  simp only [CollatzResearch.WordTrace]
  refine ⟨8418624077789543998522381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11224832103719391998029841 8418624077789543998522381)
  ·
    refine ⟨3156984029171078999445893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8418624077789543998522381 3156984029171078999445893)
    ·
      refine ⟨591934505469577312396105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3156984029171078999445893 591934505469577312396105)
      ·
        refine ⟨443950879102182984297079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591934505469577312396105 443950879102182984297079)
        ·
          refine ⟨665926318653274476445619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443950879102182984297079 665926318653274476445619)
          ·
            refine ⟨998889477979911714668429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665926318653274476445619 998889477979911714668429)
            ·
              refine ⟨374583554242466893000661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 998889477979911714668429 374583554242466893000661)
              ·
                refine ⟨8779302052557817804703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 374583554242466893000661 8779302052557817804703)
                ·
                  rfl

theorem cell23_461636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 7].length) (baseStart_461636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461636 prefixEnd_461636 := by exact prefixLift 461636
  have htrace : WordTrace (prefixWord ++ tailWord_461636) baseStart_461636 baseEnd_461636 := by
    simpa [prefixWord, tailWord_461636, baseEnd_461636] using wordTrace_append hprefix tailTrace_461636
  have hstable : (prefixWord ++ tailWord_461636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461636).length < 2 ^ (prefixWord ++ tailWord_461636).sum := by decide
  have hdescent : baseEnd_461636 < baseStart_461636 := by decide
  rcases family_descends (prefixWord ++ tailWord_461636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461639 : List Nat := [1, 1, 4, 1, 2, 1, 1, 6, 1, 3, 2]
def baseStart_461639 : Nat := 118140960795 + 461639 * 2 ^ 59
def prefixEnd_461639 : Nat := 4983230072969 + 3 ^ 40 * 461639 * 2
def baseEnd_461639 : Nat := 237042695861024568989467

theorem tailTrace_461639 : CollatzResearch.WordTrace tailWord_461639 prefixEnd_461639 237042695861024568989467 := by
  unfold tailWord_461639
  simp only [CollatzResearch.WordTrace]
  refine ⟨16837357574568219509403971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11224905049712146339602647 16837357574568219509403971)
  ·
    refine ⟨25256036361852329264105957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16837357574568219509403971 25256036361852329264105957)
    ·
      refine ⟨4735506817847311737019867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25256036361852329264105957 4735506817847311737019867)
      ·
        refine ⟨7103260226770967605529801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4735506817847311737019867 7103260226770967605529801)
        ·
          refine ⟨5327445170078225704147351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7103260226770967605529801 5327445170078225704147351)
          ·
            refine ⟨7991167755117338556221027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5327445170078225704147351 7991167755117338556221027)
            ·
              refine ⟨11986751632676007834331541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7991167755117338556221027 11986751632676007834331541)
              ·
                refine ⟨561878982781687867234291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11986751632676007834331541 561878982781687867234291)
                ·
                  refine ⟨842818474172531800851437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 561878982781687867234291 842818474172531800851437)
                  ·
                    refine ⟨316056927814699425319289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 842818474172531800851437 316056927814699425319289)
                    ·
                      refine ⟨237042695861024568989467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 316056927814699425319289 237042695861024568989467)
                      ·
                        rfl

theorem cell23_461639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 3, 2].length) (baseStart_461639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461639 prefixEnd_461639 := by exact prefixLift 461639
  have htrace : WordTrace (prefixWord ++ tailWord_461639) baseStart_461639 baseEnd_461639 := by
    simpa [prefixWord, tailWord_461639, baseEnd_461639] using wordTrace_append hprefix tailTrace_461639
  have hstable : (prefixWord ++ tailWord_461639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461639).length < 2 ^ (prefixWord ++ tailWord_461639).sum := by decide
  have hdescent : baseEnd_461639 < baseStart_461639 := by decide
  rcases family_descends (prefixWord ++ tailWord_461639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461675 : List Nat := [1, 1, 1, 1, 2, 2, 5, 3, 7]
def baseStart_461675 : Nat := 118140960795 + 461675 * 2 ^ 59
def prefixEnd_461675 : Nat := 4983230072969 + 3 ^ 40 * 461675 * 2
def baseEnd_461675 : Nat := 26340131240509603126589

theorem tailTrace_461675 : CollatzResearch.WordTrace tailWord_461675 prefixEnd_461675 26340131240509603126589 := by
  unfold tailWord_461675
  simp only [CollatzResearch.WordTrace]
  refine ⟨16838670602437797657714479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11225780401625198438476319 16838670602437797657714479)
  ·
    refine ⟨25258005903656696486571719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16838670602437797657714479 25258005903656696486571719)
    ·
      refine ⟨37887008855485044729857579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25258005903656696486571719 37887008855485044729857579)
      ·
        refine ⟨56830513283227567094786369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37887008855485044729857579 56830513283227567094786369)
        ·
          refine ⟨42622884962420675321089777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56830513283227567094786369 42622884962420675321089777)
          ·
            refine ⟨31967163721815506490817333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42622884962420675321089777 31967163721815506490817333)
            ·
              refine ⟨2996921598920203733514125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31967163721815506490817333 2996921598920203733514125)
              ·
                refine ⟨1123845599595076400067797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2996921598920203733514125 1123845599595076400067797)
                ·
                  refine ⟨26340131240509603126589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1123845599595076400067797 26340131240509603126589)
                  ·
                    rfl

theorem cell23_461675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 7].length) (baseStart_461675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461675 prefixEnd_461675 := by exact prefixLift 461675
  have htrace : WordTrace (prefixWord ++ tailWord_461675) baseStart_461675 baseEnd_461675 := by
    simpa [prefixWord, tailWord_461675, baseEnd_461675] using wordTrace_append hprefix tailTrace_461675
  have hstable : (prefixWord ++ tailWord_461675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461675).length < 2 ^ (prefixWord ++ tailWord_461675).sum := by decide
  have hdescent : baseEnd_461675 < baseStart_461675 := by decide
  rcases family_descends (prefixWord ++ tailWord_461675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461682 : List Nat := [3, 2, 1, 2, 1, 1, 4, 1, 2, 2, 4]
def baseStart_461682 : Nat := 118140960795 + 461682 * 2 ^ 59
def prefixEnd_461682 : Nat := 4983230072969 + 3 ^ 40 * 461682 * 2
def baseEnd_461682 : Nat := 237064775529167900751769

theorem tailTrace_461682 : CollatzResearch.WordTrace tailWord_461682 prefixEnd_461682 237064775529167900751769 := by
  unfold tailWord_461682
  simp only [CollatzResearch.WordTrace]
  refine ⟨4209731478353109463304825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11225950608941625235479533 4209731478353109463304825)
  ·
    refine ⟨3157298608764832097478619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4209731478353109463304825 3157298608764832097478619)
    ·
      refine ⟨4735947913147248146217929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3157298608764832097478619 4735947913147248146217929)
      ·
        refine ⟨3551960934860436109663447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4735947913147248146217929 3551960934860436109663447)
        ·
          refine ⟨5327941402290654164495171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3551960934860436109663447 5327941402290654164495171)
          ·
            refine ⟨7991912103435981246742757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5327941402290654164495171 7991912103435981246742757)
            ·
              refine ⟨1498483519394246483764267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7991912103435981246742757 1498483519394246483764267)
              ·
                refine ⟨2247725279091369725646401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1498483519394246483764267 2247725279091369725646401)
                ·
                  refine ⟨1685793959318527294234801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2247725279091369725646401 1685793959318527294234801)
                  ·
                    refine ⟨1264345469488895470676101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1685793959318527294234801 1264345469488895470676101)
                    ·
                      refine ⟨237064775529167900751769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1264345469488895470676101 237064775529167900751769)
                      ·
                        rfl

theorem cell23_461682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_461682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461682 prefixEnd_461682 := by exact prefixLift 461682
  have htrace : WordTrace (prefixWord ++ tailWord_461682) baseStart_461682 baseEnd_461682 := by
    simpa [prefixWord, tailWord_461682, baseEnd_461682] using wordTrace_append hprefix tailTrace_461682
  have hstable : (prefixWord ++ tailWord_461682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461682).length < 2 ^ (prefixWord ++ tailWord_461682).sum := by decide
  have hdescent : baseEnd_461682 < baseStart_461682 := by decide
  rcases family_descends (prefixWord ++ tailWord_461682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461732 : List Nat := [2, 3, 1, 2, 1, 2, 3, 1, 1, 2, 5]
def baseStart_461732 : Nat := 118140960795 + 461732 * 2 ^ 59
def prefixEnd_461732 : Nat := 4983230072969 + 3 ^ 40 * 461732 * 2
def baseEnd_461732 : Nat := 237090449561892705126539

theorem tailTrace_461732 : CollatzResearch.WordTrace tailWord_461732 prefixEnd_461732 237090449561892705126539 := by
  unfold tailWord_461732
  simp only [CollatzResearch.WordTrace]
  refine ⟨8420374781615648196269725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11227166375487530928359633 8420374781615648196269725)
  ·
    refine ⟨3157640543105868073601147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8420374781615648196269725 3157640543105868073601147)
    ·
      refine ⟨4736460814658802110401721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3157640543105868073601147 4736460814658802110401721)
      ·
        refine ⟨3552345610994101582801291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4736460814658802110401721 3552345610994101582801291)
        ·
          refine ⟨5328518416491152374201937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3552345610994101582801291 5328518416491152374201937)
          ·
            refine ⟨3996388812368364280651453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5328518416491152374201937 3996388812368364280651453)
            ·
              refine ⟨1498645804638136605244295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3996388812368364280651453 1498645804638136605244295)
              ·
                refine ⟨2247968706957204907866443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1498645804638136605244295 2247968706957204907866443)
                ·
                  refine ⟨3371953060435807361799665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2247968706957204907866443 3371953060435807361799665)
                  ·
                    refine ⟨2528964795326855521349749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3371953060435807361799665 2528964795326855521349749)
                    ·
                      refine ⟨237090449561892705126539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2528964795326855521349749 237090449561892705126539)
                      ·
                        rfl

theorem cell23_461732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_461732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461732 prefixEnd_461732 := by exact prefixLift 461732
  have htrace : WordTrace (prefixWord ++ tailWord_461732) baseStart_461732 baseEnd_461732 := by
    simpa [prefixWord, tailWord_461732, baseEnd_461732] using wordTrace_append hprefix tailTrace_461732
  have hstable : (prefixWord ++ tailWord_461732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461732).length < 2 ^ (prefixWord ++ tailWord_461732).sum := by decide
  have hdescent : baseEnd_461732 < baseStart_461732 := by decide
  rcases family_descends (prefixWord ++ tailWord_461732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461772 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 2, 1, 6]
def baseStart_461772 : Nat := 118140960795 + 461772 * 2 ^ 59
def prefixEnd_461772 : Nat := 4983230072969 + 3 ^ 40 * 461772 * 2
def baseEnd_461772 : Nat := 237110988788072548626355

theorem tailTrace_461772 : CollatzResearch.WordTrace tailWord_461772 prefixEnd_461772 237110988788072548626355 := by
  unfold tailWord_461772
  simp only [CollatzResearch.WordTrace]
  refine ⟨8421104241543191611997785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11228138988724255482663713 8421104241543191611997785)
  ·
    refine ⟨6315828181157393708998339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8421104241543191611997785 6315828181157393708998339)
    ·
      refine ⟨9473742271736090563497509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6315828181157393708998339 9473742271736090563497509)
      ·
        refine ⟨1776326675950516980655783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9473742271736090563497509 1776326675950516980655783)
        ·
          refine ⟨2664490013925775470983675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1776326675950516980655783 2664490013925775470983675)
          ·
            refine ⟨3996735020888663206475513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2664490013925775470983675 3996735020888663206475513)
            ·
              refine ⟨2997551265666497404856635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3996735020888663206475513 2997551265666497404856635)
              ·
                refine ⟨4496326898499746107284953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2997551265666497404856635 4496326898499746107284953)
                ·
                  refine ⟨3372245173874809580463715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4496326898499746107284953 3372245173874809580463715)
                  ·
                    refine ⟨5058367760812214370695573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3372245173874809580463715 5058367760812214370695573)
                    ·
                      refine ⟨237110988788072548626355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5058367760812214370695573 237110988788072548626355)
                      ·
                        rfl

theorem cell23_461772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_461772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461772 prefixEnd_461772 := by exact prefixLift 461772
  have htrace : WordTrace (prefixWord ++ tailWord_461772) baseStart_461772 baseEnd_461772 := by
    simpa [prefixWord, tailWord_461772, baseEnd_461772] using wordTrace_append hprefix tailTrace_461772
  have hstable : (prefixWord ++ tailWord_461772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461772).length < 2 ^ (prefixWord ++ tailWord_461772).sum := by decide
  have hdescent : baseEnd_461772 < baseStart_461772 := by decide
  rcases family_descends (prefixWord ++ tailWord_461772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461792 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 3]
def baseStart_461792 : Nat := 118140960795 + 461792 * 2 ^ 59
def prefixEnd_461792 : Nat := 4983230072969 + 3 ^ 40 * 461792 * 2
def baseEnd_461792 : Nat := 237121258401162470376263

theorem tailTrace_461792 : CollatzResearch.WordTrace tailWord_461792 prefixEnd_461792 237121258401162470376263 := by
  unfold tailWord_461792
  simp only [CollatzResearch.WordTrace]
  refine ⟨8421468971506963319861815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11228625295342617759815753 8421468971506963319861815)
  ·
    refine ⟨12632203457260444979792723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8421468971506963319861815 12632203457260444979792723)
    ·
      refine ⟨18948305185890667469689085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12632203457260444979792723 18948305185890667469689085)
      ·
        refine ⟨7105614444709000301133407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18948305185890667469689085 7105614444709000301133407)
        ·
          refine ⟨10658421667063500451700111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7105614444709000301133407 10658421667063500451700111)
          ·
            refine ⟨15987632500595250677550167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10658421667063500451700111 15987632500595250677550167)
            ·
              refine ⟨23981448750892876016325251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15987632500595250677550167 23981448750892876016325251)
              ·
                refine ⟨35972173126339314024487877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23981448750892876016325251 35972173126339314024487877)
                ·
                  refine ⟨6744782461188621379591477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35972173126339314024487877 6744782461188621379591477)
                  ·
                    refine ⟨632323355736433254336701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6744782461188621379591477 632323355736433254336701)
                    ·
                      refine ⟨237121258401162470376263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 632323355736433254336701 237121258401162470376263)
                      ·
                        rfl

theorem cell23_461792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_461792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461792 prefixEnd_461792 := by exact prefixLift 461792
  have htrace : WordTrace (prefixWord ++ tailWord_461792) baseStart_461792 baseEnd_461792 := by
    simpa [prefixWord, tailWord_461792, baseEnd_461792] using wordTrace_append hprefix tailTrace_461792
  have hstable : (prefixWord ++ tailWord_461792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461792).length < 2 ^ (prefixWord ++ tailWord_461792).sum := by decide
  have hdescent : baseEnd_461792 < baseStart_461792 := by decide
  rcases family_descends (prefixWord ++ tailWord_461792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461799 : List Nat := [1, 1, 5, 2, 2, 1, 2, 3, 6]
def baseStart_461799 : Nat := 118140960795 + 461799 * 2 ^ 59
def prefixEnd_461799 : Nat := 4983230072969 + 3 ^ 40 * 461799 * 2
def baseEnd_461799 : Nat := 26347205862860438109859

theorem tailTrace_461799 : CollatzResearch.WordTrace tailWord_461799 prefixEnd_461799 26347205862860438109859 := by
  unfold tailWord_461799
  simp only [CollatzResearch.WordTrace]
  refine ⟨16843193253988566835228451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11228795502659044556818967 16843193253988566835228451)
  ·
    refine ⟨25264789880982850252842677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16843193253988566835228451 25264789880982850252842677)
    ·
      refine ⟨2368574051342142211204001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25264789880982850252842677 2368574051342142211204001)
      ·
        refine ⟨1776430538506606658403001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2368574051342142211204001 1776430538506606658403001)
        ·
          refine ⟨1332322903879954993802251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1776430538506606658403001 1332322903879954993802251)
          ·
            refine ⟨1998484355819932490703377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1332322903879954993802251 1998484355819932490703377)
            ·
              refine ⟨1498863266864949368027533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1998484355819932490703377 1498863266864949368027533)
              ·
                refine ⟨562073725074356013010325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1498863266864949368027533 562073725074356013010325)
                ·
                  refine ⟨26347205862860438109859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 562073725074356013010325 26347205862860438109859)
                  ·
                    rfl

theorem cell23_461799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 6].length) (baseStart_461799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461799 prefixEnd_461799 := by exact prefixLift 461799
  have htrace : WordTrace (prefixWord ++ tailWord_461799) baseStart_461799 baseEnd_461799 := by
    simpa [prefixWord, tailWord_461799, baseEnd_461799] using wordTrace_append hprefix tailTrace_461799
  have hstable : (prefixWord ++ tailWord_461799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461799).length < 2 ^ (prefixWord ++ tailWord_461799).sum := by decide
  have hdescent : baseEnd_461799 < baseStart_461799 := by decide
  rcases family_descends (prefixWord ++ tailWord_461799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461810 : List Nat := [3, 2, 1, 5, 2, 1, 1, 1, 2, 1, 4]
def baseStart_461810 : Nat := 118140960795 + 461810 * 2 ^ 59
def prefixEnd_461810 : Nat := 4983230072969 + 3 ^ 40 * 461810 * 2
def baseEnd_461810 : Nat := 237130501052943399951181

theorem tailTrace_461810 : CollatzResearch.WordTrace tailWord_461810 prefixEnd_461810 237130501052943399951181 := by
  unfold tailWord_461810
  simp only [CollatzResearch.WordTrace]
  refine ⟨4210898614237178928469721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11229062971299143809252589 4210898614237178928469721)
  ·
    refine ⟨3158173960677884196352291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4210898614237178928469721 3158173960677884196352291)
    ·
      refine ⟨4737260941016826294528437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3158173960677884196352291 4737260941016826294528437)
      ·
        refine ⟨444118213220327465112041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4737260941016826294528437 444118213220327465112041)
        ·
          refine ⟨333088659915245598834031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444118213220327465112041 333088659915245598834031)
          ·
            refine ⟨499632989872868398251047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333088659915245598834031 499632989872868398251047)
            ·
              refine ⟨749449484809302597376571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499632989872868398251047 749449484809302597376571)
              ·
                refine ⟨1124174227213953896064857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 749449484809302597376571 1124174227213953896064857)
                ·
                  refine ⟨843130670410465422048643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1124174227213953896064857 843130670410465422048643)
                  ·
                    refine ⟨1264696005615698133072965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 843130670410465422048643 1264696005615698133072965)
                    ·
                      refine ⟨237130501052943399951181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1264696005615698133072965 237130501052943399951181)
                      ·
                        rfl

theorem cell23_461810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_461810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461810 prefixEnd_461810 := by exact prefixLift 461810
  have htrace : WordTrace (prefixWord ++ tailWord_461810) baseStart_461810 baseEnd_461810 := by
    simpa [prefixWord, tailWord_461810, baseEnd_461810] using wordTrace_append hprefix tailTrace_461810
  have hstable : (prefixWord ++ tailWord_461810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461810).length < 2 ^ (prefixWord ++ tailWord_461810).sum := by decide
  have hdescent : baseEnd_461810 < baseStart_461810 := by decide
  rcases family_descends (prefixWord ++ tailWord_461810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461813 : List Nat := [1, 3, 5, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_461813 : Nat := 118140960795 + 461813 * 2 ^ 59
def prefixEnd_461813 : Nat := 4983230072969 + 3 ^ 40 * 461813 * 2
def baseEnd_461813 : Nat := 237132041494906888213667

theorem tailTrace_461813 : CollatzResearch.WordTrace tailWord_461813 prefixEnd_461813 237132041494906888213667 := by
  unfold tailWord_461813
  simp only [CollatzResearch.WordTrace]
  refine ⟨16843703875937847226238093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11229135917291898150825395 16843703875937847226238093)
  ·
    refine ⟨6316388953476692709839285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16843703875937847226238093 6316388953476692709839285)
    ·
      refine ⟨592161464388439941547433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6316388953476692709839285 592161464388439941547433)
      ·
        refine ⟨444121098291329956160575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592161464388439941547433 444121098291329956160575)
        ·
          refine ⟨666181647436994934240863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444121098291329956160575 666181647436994934240863)
          ·
            refine ⟨999272471155492401361295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666181647436994934240863 999272471155492401361295)
            ·
              refine ⟨1498908706733238602041943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999272471155492401361295 1498908706733238602041943)
              ·
                refine ⟨2248363060099857903062915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1498908706733238602041943 2248363060099857903062915)
                ·
                  refine ⟨3372544590149786854594373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2248363060099857903062915 3372544590149786854594373)
                  ·
                    refine ⟨632352110653085035236445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3372544590149786854594373 632352110653085035236445)
                    ·
                      refine ⟨237132041494906888213667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 632352110653085035236445 237132041494906888213667)
                      ·
                        rfl

theorem cell23_461813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_461813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461813 prefixEnd_461813 := by exact prefixLift 461813
  have htrace : WordTrace (prefixWord ++ tailWord_461813) baseStart_461813 baseEnd_461813 := by
    simpa [prefixWord, tailWord_461813, baseEnd_461813] using wordTrace_append hprefix tailTrace_461813
  have hstable : (prefixWord ++ tailWord_461813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461813).length < 2 ^ (prefixWord ++ tailWord_461813).sum := by decide
  have hdescent : baseEnd_461813 < baseStart_461813 := by decide
  rcases family_descends (prefixWord ++ tailWord_461813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461829 : List Nat := [1, 3, 1, 1, 2, 3, 3, 3, 1, 5]
def baseStart_461829 : Nat := 118140960795 + 461829 * 2 ^ 59
def prefixEnd_461829 : Nat := 4983230072969 + 3 ^ 40 * 461829 * 2
def baseEnd_461829 : Nat := 79046752395126275204531

theorem tailTrace_461829 : CollatzResearch.WordTrace tailWord_461829 prefixEnd_461829 79046752395126275204531 := by
  unfold tailWord_461829
  simp only [CollatzResearch.WordTrace]
  refine ⟨16844287443879881958820541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11229524962586587972547027 16844287443879881958820541)
  ·
    refine ⟨6316607791454955734557703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16844287443879881958820541 6316607791454955734557703)
    ·
      refine ⟨9474911687182433601836555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6316607791454955734557703 9474911687182433601836555)
      ·
        refine ⟨14212367530773650402754833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9474911687182433601836555 14212367530773650402754833)
        ·
          refine ⟨10659275648080237802066125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14212367530773650402754833 10659275648080237802066125)
          ·
            refine ⟨3997228368030089175774797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10659275648080237802066125 3997228368030089175774797)
            ·
              refine ⟨1498960638011283440915549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3997228368030089175774797 1498960638011283440915549)
              ·
                refine ⟨562110239254231290343331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1498960638011283440915549 562110239254231290343331)
                ·
                  refine ⟨843165358881346935514997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 562110239254231290343331 843165358881346935514997)
                  ·
                    refine ⟨79046752395126275204531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 843165358881346935514997 79046752395126275204531)
                    ·
                      rfl

theorem cell23_461829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 5].length) (baseStart_461829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461829 prefixEnd_461829 := by exact prefixLift 461829
  have htrace : WordTrace (prefixWord ++ tailWord_461829) baseStart_461829 baseEnd_461829 := by
    simpa [prefixWord, tailWord_461829, baseEnd_461829] using wordTrace_append hprefix tailTrace_461829
  have hstable : (prefixWord ++ tailWord_461829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461829).length < 2 ^ (prefixWord ++ tailWord_461829).sum := by decide
  have hdescent : baseEnd_461829 < baseStart_461829 := by decide
  rcases family_descends (prefixWord ++ tailWord_461829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461859 : List Nat := [1, 1, 1, 4, 3, 2, 3, 1, 1, 6]
def baseStart_461859 : Nat := 118140960795 + 461859 * 2 ^ 59
def prefixEnd_461859 : Nat := 4983230072969 + 3 ^ 40 * 461859 * 2
def baseEnd_461859 : Nat := 79051887201671236079485

theorem tailTrace_461859 : CollatzResearch.WordTrace tailWord_461859 prefixEnd_461859 79051887201671236079485 := by
  unfold tailWord_461859
  simp only [CollatzResearch.WordTrace]
  refine ⟨16845381633771197082412631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11230254422514131388275087 16845381633771197082412631)
  ·
    refine ⟨25268072450656795623618947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16845381633771197082412631 25268072450656795623618947)
    ·
      refine ⟨37902108675985193435428421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25268072450656795623618947 37902108675985193435428421)
      ·
        refine ⟨7106645376747223769142829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37902108675985193435428421 7106645376747223769142829)
        ·
          refine ⟨2664992016280208913428561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7106645376747223769142829 2664992016280208913428561)
          ·
            refine ⟨1998744012210156685071421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2664992016280208913428561 1998744012210156685071421)
            ·
              refine ⟨749529004578808756901783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1998744012210156685071421 749529004578808756901783)
              ·
                refine ⟨1124293506868213135352675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 749529004578808756901783 1124293506868213135352675)
                ·
                  refine ⟨1686440260302319703029013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1124293506868213135352675 1686440260302319703029013)
                  ·
                    refine ⟨79051887201671236079485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1686440260302319703029013 79051887201671236079485)
                    ·
                      rfl

theorem cell23_461859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 6].length) (baseStart_461859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461859 prefixEnd_461859 := by exact prefixLift 461859
  have htrace : WordTrace (prefixWord ++ tailWord_461859) baseStart_461859 baseEnd_461859 := by
    simpa [prefixWord, tailWord_461859, baseEnd_461859] using wordTrace_append hprefix tailTrace_461859
  have hstable : (prefixWord ++ tailWord_461859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461859).length < 2 ^ (prefixWord ++ tailWord_461859).sum := by decide
  have hdescent : baseEnd_461859 < baseStart_461859 := by decide
  rcases family_descends (prefixWord ++ tailWord_461859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461863 : List Nat := [1, 1, 7, 1, 1, 2, 2, 2, 1, 5]
def baseStart_461863 : Nat := 118140960795 + 461863 * 2 ^ 59
def prefixEnd_461863 : Nat := 4983230072969 + 3 ^ 40 * 461863 * 2
def baseEnd_461863 : Nat := 79052571842543897529479

theorem tailTrace_461863 : CollatzResearch.WordTrace tailWord_461863 prefixEnd_461863 79052571842543897529479 := by
  unfold tailWord_461863
  simp only [CollatzResearch.WordTrace]
  refine ⟨16845527525756705765558243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11230351683837803843705495 16845527525756705765558243)
  ·
    refine ⟨25268291288635058648337365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16845527525756705765558243 25268291288635058648337365)
    ·
      refine ⟨592225577077384187070407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 25268291288635058648337365 592225577077384187070407)
      ·
        refine ⟨888338365616076280605611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592225577077384187070407 888338365616076280605611)
        ·
          refine ⟨1332507548424114420908417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888338365616076280605611 1332507548424114420908417)
          ·
            refine ⟨999380661318085815681313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1332507548424114420908417 999380661318085815681313)
            ·
              refine ⟨749535495988564361760985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 999380661318085815681313 749535495988564361760985)
              ·
                refine ⟨562151621991423271320739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 749535495988564361760985 562151621991423271320739)
                ·
                  refine ⟨843227432987134906981109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 562151621991423271320739 843227432987134906981109)
                  ·
                    refine ⟨79052571842543897529479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 843227432987134906981109 79052571842543897529479)
                    ·
                      rfl

theorem cell23_461863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_461863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461863 prefixEnd_461863 := by exact prefixLift 461863
  have htrace : WordTrace (prefixWord ++ tailWord_461863) baseStart_461863 baseEnd_461863 := by
    simpa [prefixWord, tailWord_461863, baseEnd_461863] using wordTrace_append hprefix tailTrace_461863
  have hstable : (prefixWord ++ tailWord_461863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461863).length < 2 ^ (prefixWord ++ tailWord_461863).sum := by decide
  have hdescent : baseEnd_461863 < baseStart_461863 := by decide
  rcases family_descends (prefixWord ++ tailWord_461863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461872 : List Nat := [2, 1, 1, 1, 2, 4, 3, 9]
def baseStart_461872 : Nat := 118140960795 + 461872 * 2 ^ 59
def prefixEnd_461872 : Nat := 4983230072969 + 3 ^ 40 * 461872 * 2
def baseEnd_461872 : Nat := 8783790253834153976885

theorem tailTrace_461872 : CollatzResearch.WordTrace tailWord_461872 prefixEnd_461872 8783790253834153976885 := by
  unfold tailWord_461872
  simp only [CollatzResearch.WordTrace]
  refine ⟨8422927891362050151317935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11230570521816066868423913 8422927891362050151317935)
  ·
    refine ⟨12634391837043075226976903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8422927891362050151317935 12634391837043075226976903)
    ·
      refine ⟨18951587755564612840465355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12634391837043075226976903 18951587755564612840465355)
      ·
        refine ⟨28427381633346919260698033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18951587755564612840465355 28427381633346919260698033)
        ·
          refine ⟨21320536225010189445523525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28427381633346919260698033 21320536225010189445523525)
          ·
            refine ⟨3997600542189410521035661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21320536225010189445523525 3997600542189410521035661)
            ·
              refine ⟨1499100203321028945388373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3997600542189410521035661 1499100203321028945388373)
              ·
                refine ⟨8783790253834153976885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1499100203321028945388373 8783790253834153976885)
                ·
                  rfl

theorem cell23_461872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 9].length) (baseStart_461872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461872 prefixEnd_461872 := by exact prefixLift 461872
  have htrace : WordTrace (prefixWord ++ tailWord_461872) baseStart_461872 baseEnd_461872 := by
    simpa [prefixWord, tailWord_461872, baseEnd_461872] using wordTrace_append hprefix tailTrace_461872
  have hstable : (prefixWord ++ tailWord_461872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461872).length < 2 ^ (prefixWord ++ tailWord_461872).sum := by decide
  have hdescent : baseEnd_461872 < baseStart_461872 := by decide
  rcases family_descends (prefixWord ++ tailWord_461872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461886 : List Nat := [4, 2, 1, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_461886 : Nat := 118140960795 + 461886 * 2 ^ 59
def prefixEnd_461886 : Nat := 4983230072969 + 3 ^ 40 * 461886 * 2
def baseEnd_461886 : Nat := 237169525582685102600831

theorem tailTrace_461886 : CollatzResearch.WordTrace tailWord_461886 prefixEnd_461886 237169525582685102600831 := by
  unfold tailWord_461886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2105795800584172586705689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11230910936448920462430341 2105795800584172586705689)
  ·
    refine ⟨1579346850438129440029267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2105795800584172586705689 1579346850438129440029267)
    ·
      refine ⟨2369020275657194160043901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1579346850438129440029267 2369020275657194160043901)
      ·
        refine ⟨888382603371447810016463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2369020275657194160043901 888382603371447810016463)
        ·
          refine ⟨1332573905057171715024695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888382603371447810016463 1332573905057171715024695)
          ·
            refine ⟨1998860857585757572537043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1332573905057171715024695 1998860857585757572537043)
            ·
              refine ⟨2998291286378636358805565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1998860857585757572537043 2998291286378636358805565)
              ·
                refine ⟨1124359232391988634552087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2998291286378636358805565 1124359232391988634552087)
                ·
                  refine ⟨1686538848587982951828131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1124359232391988634552087 1686538848587982951828131)
                  ·
                    refine ⟨2529808272881974427742197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1686538848587982951828131 2529808272881974427742197)
                    ·
                      refine ⟨237169525582685102600831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2529808272881974427742197 237169525582685102600831)
                      ·
                        rfl

theorem cell23_461886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_461886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461886 prefixEnd_461886 := by exact prefixLift 461886
  have htrace : WordTrace (prefixWord ++ tailWord_461886) baseStart_461886 baseEnd_461886 := by
    simpa [prefixWord, tailWord_461886, baseEnd_461886] using wordTrace_append hprefix tailTrace_461886
  have hstable : (prefixWord ++ tailWord_461886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461886).length < 2 ^ (prefixWord ++ tailWord_461886).sum := by decide
  have hdescent : baseEnd_461886 < baseStart_461886 := by decide
  rcases family_descends (prefixWord ++ tailWord_461886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461894 : List Nat := [6, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3]
def baseStart_461894 : Nat := 118140960795 + 461894 * 2 ^ 59
def prefixEnd_461894 : Nat := 4983230072969 + 3 ^ 40 * 461894 * 2
def baseEnd_461894 : Nat := 237173633427921071300795

theorem tailTrace_461894 : CollatzResearch.WordTrace tailWord_461894 prefixEnd_461894 237173633427921071300795 := by
  unfold tailWord_461894
  simp only [CollatzResearch.WordTrace]
  refine ⟨526458068395137439373023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11231105459096265373291157 526458068395137439373023)
  ·
    refine ⟨789687102592706159059535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 526458068395137439373023 789687102592706159059535)
    ·
      refine ⟨1184530653889059238589303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 789687102592706159059535 1184530653889059238589303)
      ·
        refine ⟨1776795980833588857883955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1184530653889059238589303 1776795980833588857883955)
        ·
          refine ⟨2665193971250383286825933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1776795980833588857883955 2665193971250383286825933)
          ·
            refine ⟨999447739218893732559725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2665193971250383286825933 999447739218893732559725)
            ·
              refine ⟨374792902207085149709897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 999447739218893732559725 374792902207085149709897)
              ·
                refine ⟨281094676655313862282423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 374792902207085149709897 281094676655313862282423)
                ·
                  refine ⟨421642014982970793423635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 281094676655313862282423 421642014982970793423635)
                  ·
                    refine ⟨632463022474456190135453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 421642014982970793423635 632463022474456190135453)
                    ·
                      refine ⟨237173633427921071300795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 632463022474456190135453 237173633427921071300795)
                      ·
                        rfl

theorem cell23_461894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_461894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461894 prefixEnd_461894 := by exact prefixLift 461894
  have htrace : WordTrace (prefixWord ++ tailWord_461894) baseStart_461894 baseEnd_461894 := by
    simpa [prefixWord, tailWord_461894, baseEnd_461894] using wordTrace_append hprefix tailTrace_461894
  have hstable : (prefixWord ++ tailWord_461894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461894).length < 2 ^ (prefixWord ++ tailWord_461894).sum := by decide
  have hdescent : baseEnd_461894 < baseStart_461894 := by decide
  rcases family_descends (prefixWord ++ tailWord_461894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461916 : List Nat := [2, 2, 4, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_461916 : Nat := 118140960795 + 461916 * 2 ^ 59
def prefixEnd_461916 : Nat := 4983230072969 + 3 ^ 40 * 461916 * 2
def baseEnd_461916 : Nat := 237184930002319985225693

theorem tailTrace_461916 : CollatzResearch.WordTrace tailWord_461916 prefixEnd_461916 237184930002319985225693 := by
  unfold tailWord_461916
  simp only [CollatzResearch.WordTrace]
  refine ⟨8423730297282347908618801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11231640396376463878158401 8423730297282347908618801)
  ·
    refine ⟨6317797722961760931464101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8423730297282347908618801 6317797722961760931464101)
    ·
      refine ⟨1184587073055330174649519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6317797722961760931464101 1184587073055330174649519)
      ·
        refine ⟨1776880609582995261974279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1184587073055330174649519 1776880609582995261974279)
        ·
          refine ⟨2665320914374492892961419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1776880609582995261974279 2665320914374492892961419)
          ·
            refine ⟨3997981371561739339442129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2665320914374492892961419 3997981371561739339442129)
            ·
              refine ⟨2998486028671304504581597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3997981371561739339442129 2998486028671304504581597)
              ·
                refine ⟨1124432260751739189218099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2998486028671304504581597 1124432260751739189218099)
                ·
                  refine ⟨1686648391127608783827149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1124432260751739189218099 1686648391127608783827149)
                  ·
                    refine ⟨632493146672853293935181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1686648391127608783827149 632493146672853293935181)
                    ·
                      refine ⟨237184930002319985225693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 632493146672853293935181 237184930002319985225693)
                      ·
                        rfl

theorem cell23_461916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_461916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461916 prefixEnd_461916 := by exact prefixLift 461916
  have htrace : WordTrace (prefixWord ++ tailWord_461916) baseStart_461916 baseEnd_461916 := by
    simpa [prefixWord, tailWord_461916, baseEnd_461916] using wordTrace_append hprefix tailTrace_461916
  have hstable : (prefixWord ++ tailWord_461916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461916).length < 2 ^ (prefixWord ++ tailWord_461916).sum := by decide
  have hdescent : baseEnd_461916 < baseStart_461916 := by decide
  rcases family_descends (prefixWord ++ tailWord_461916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461917 : List Nat := [1, 4, 4, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_461917 : Nat := 118140960795 + 461917 * 2 ^ 59
def prefixEnd_461917 : Nat := 4983230072969 + 3 ^ 40 * 461917 * 2
def baseEnd_461917 : Nat := 237185443482974481313189

theorem tailTrace_461917 : CollatzResearch.WordTrace tailWord_461917 prefixEnd_461917 237185443482974481313189 := by
  unfold tailWord_461917
  simp only [CollatzResearch.WordTrace]
  refine ⟨16847497067561072988024005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11231664711707381992016003 16847497067561072988024005)
  ·
    refine ⟨3158905700167701185254501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16847497067561072988024005 3158905700167701185254501)
    ·
      refine ⟨592294818781443972235219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3158905700167701185254501 592294818781443972235219)
      ·
        refine ⟨888442228172165958352829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592294818781443972235219 888442228172165958352829)
        ·
          refine ⟨333165835564562234382311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 888442228172165958352829 333165835564562234382311)
          ·
            refine ⟨499748753346843351573467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333165835564562234382311 499748753346843351573467)
            ·
              refine ⟨749623130020265027360201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499748753346843351573467 749623130020265027360201)
              ·
                refine ⟨562217347515198770520151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 749623130020265027360201 562217347515198770520151)
                ·
                  refine ⟨843326021272798155780227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 562217347515198770520151 843326021272798155780227)
                  ·
                    refine ⟨1264989031909197233670341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 843326021272798155780227 1264989031909197233670341)
                    ·
                      refine ⟨237185443482974481313189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1264989031909197233670341 237185443482974481313189)
                      ·
                        rfl

theorem cell23_461917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_461917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461917 prefixEnd_461917 := by exact prefixLift 461917
  have htrace : WordTrace (prefixWord ++ tailWord_461917) baseStart_461917 baseEnd_461917 := by
    simpa [prefixWord, tailWord_461917, baseEnd_461917] using wordTrace_append hprefix tailTrace_461917
  have hstable : (prefixWord ++ tailWord_461917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461917).length < 2 ^ (prefixWord ++ tailWord_461917).sum := by decide
  have hdescent : baseEnd_461917 < baseStart_461917 := by decide
  rcases family_descends (prefixWord ++ tailWord_461917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461949 : List Nat := [1, 4, 1, 1, 3, 1, 2, 2, 2, 6]
def baseStart_461949 : Nat := 118140960795 + 461949 * 2 ^ 59
def prefixEnd_461949 : Nat := 4983230072969 + 3 ^ 40 * 461949 * 2
def baseEnd_461949 : Nat := 79067291621306118704347

theorem tailTrace_461949 : CollatzResearch.WordTrace tailWord_461949 prefixEnd_461949 79067291621306118704347 := by
  unfold tailWord_461949
  simp only [CollatzResearch.WordTrace]
  refine ⟨16848664203445142453188901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11232442802296761635459267 16848664203445142453188901)
  ·
    refine ⟨3159124538145964209972919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16848664203445142453188901 3159124538145964209972919)
    ·
      refine ⟨4738686807218946314959379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3159124538145964209972919 4738686807218946314959379)
      ·
        refine ⟨7108030210828419472439069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4738686807218946314959379 7108030210828419472439069)
        ·
          refine ⟨2665511329060657302164651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7108030210828419472439069 2665511329060657302164651)
          ·
            refine ⟨3998266993590985953246977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2665511329060657302164651 3998266993590985953246977)
            ·
              refine ⟨2998700245193239464935233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3998266993590985953246977 2998700245193239464935233)
              ·
                refine ⟨2249025183894929598701425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2998700245193239464935233 2249025183894929598701425)
                ·
                  refine ⟨1686768887921197199026069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2249025183894929598701425 1686768887921197199026069)
                  ·
                    refine ⟨79067291621306118704347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1686768887921197199026069 79067291621306118704347)
                    ·
                      rfl

theorem cell23_461949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_461949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461949 prefixEnd_461949 := by exact prefixLift 461949
  have htrace : WordTrace (prefixWord ++ tailWord_461949) baseStart_461949 baseEnd_461949 := by
    simpa [prefixWord, tailWord_461949, baseEnd_461949] using wordTrace_append hprefix tailTrace_461949
  have hstable : (prefixWord ++ tailWord_461949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461949).length < 2 ^ (prefixWord ++ tailWord_461949).sum := by decide
  have hdescent : baseEnd_461949 < baseStart_461949 := by decide
  rcases family_descends (prefixWord ++ tailWord_461949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461966 : List Nat := [4, 1, 1, 3, 2, 2, 1, 1, 2, 6]
def baseStart_461966 : Nat := 118140960795 + 461966 * 2 ^ 59
def prefixEnd_461966 : Nat := 4983230072969 + 3 ^ 40 * 461966 * 2
def baseEnd_461966 : Nat := 79070201345014929866821

theorem tailTrace_461966 : CollatzResearch.WordTrace tailWord_461966 prefixEnd_461966 79070201345014929866821 := by
  unfold tailWord_461966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2106160530547944294569719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11232856162922369571038501 2106160530547944294569719)
  ·
    refine ⟨3159240795821916441854579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2106160530547944294569719 3159240795821916441854579)
    ·
      refine ⟨4738861193732874662781869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3159240795821916441854579 4738861193732874662781869)
      ·
        refine ⟨1777072947649827998543201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4738861193732874662781869 1777072947649827998543201)
        ·
          refine ⟨1332804710737370998907401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1777072947649827998543201 1332804710737370998907401)
          ·
            refine ⟨999603533053028249180551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1332804710737370998907401 999603533053028249180551)
            ·
              refine ⟨1499405299579542373770827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999603533053028249180551 1499405299579542373770827)
              ·
                refine ⟨2249107949369313560656241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1499405299579542373770827 2249107949369313560656241)
                ·
                  refine ⟨1686830962026985170492181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2249107949369313560656241 1686830962026985170492181)
                  ·
                    refine ⟨79070201345014929866821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1686830962026985170492181 79070201345014929866821)
                    ·
                      rfl

theorem cell23_461966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_461966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461966 prefixEnd_461966 := by exact prefixLift 461966
  have htrace : WordTrace (prefixWord ++ tailWord_461966) baseStart_461966 baseEnd_461966 := by
    simpa [prefixWord, tailWord_461966, baseEnd_461966] using wordTrace_append hprefix tailTrace_461966
  have hstable : (prefixWord ++ tailWord_461966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461966).length < 2 ^ (prefixWord ++ tailWord_461966).sum := by decide
  have hdescent : baseEnd_461966 < baseStart_461966 := by decide
  rcases family_descends (prefixWord ++ tailWord_461966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461994 : List Nat := [3, 1, 5, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_461994 : Nat := 118140960795 + 461994 * 2 ^ 59
def prefixEnd_461994 : Nat := 4983230072969 + 3 ^ 40 * 461994 * 2
def baseEnd_461994 : Nat := 237224981493370680050335

theorem tailTrace_461994 : CollatzResearch.WordTrace tailWord_461994 prefixEnd_461994 237224981493370680050335 := by
  unfold tailWord_461994
  simp only [CollatzResearch.WordTrace]
  refine ⟨4212576372070528784644259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11233536992188076759051357 4212576372070528784644259)
  ·
    refine ⟨6318864558105793176966389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4212576372070528784644259 6318864558105793176966389)
    ·
      refine ⟨592393552322418110340599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6318864558105793176966389 592393552322418110340599)
      ·
        refine ⟨888590328483627165510899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592393552322418110340599 888590328483627165510899)
        ·
          refine ⟨1332885492725440748266349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888590328483627165510899 1332885492725440748266349)
          ·
            refine ⟨499832059772040280599881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1332885492725440748266349 499832059772040280599881)
            ·
              refine ⟨374874044829030210449911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 499832059772040280599881 374874044829030210449911)
              ·
                refine ⟨562311067243545315674867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374874044829030210449911 562311067243545315674867)
                ·
                  refine ⟨843466600865317973512301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 562311067243545315674867 843466600865317973512301)
                  ·
                    refine ⟨316299975324494240067113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 843466600865317973512301 316299975324494240067113)
                    ·
                      refine ⟨237224981493370680050335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 316299975324494240067113 237224981493370680050335)
                      ·
                        rfl

theorem cell23_461994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_461994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_461994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_461994 prefixEnd_461994 := by exact prefixLift 461994
  have htrace : WordTrace (prefixWord ++ tailWord_461994) baseStart_461994 baseEnd_461994 := by
    simpa [prefixWord, tailWord_461994, baseEnd_461994] using wordTrace_append hprefix tailTrace_461994
  have hstable : (prefixWord ++ tailWord_461994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461994).length < 2 ^ (prefixWord ++ tailWord_461994).sum := by decide
  have hdescent : baseEnd_461994 < baseStart_461994 := by decide
  rcases family_descends (prefixWord ++ tailWord_461994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462063 : List Nat := [1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 4]
def baseStart_462063 : Nat := 118140960795 + 462063 * 2 ^ 59
def prefixEnd_462063 : Nat := 4983230072969 + 3 ^ 40 * 462063 * 2
def baseEnd_462063 : Nat := 237260411658530910087517

theorem tailTrace_462063 : CollatzResearch.WordTrace tailWord_462063 prefixEnd_462063 237260411658530910087517 := by
  unfold tailWord_462063
  simp only [CollatzResearch.WordTrace]
  refine ⟨16852822125032139922838843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11235214750021426615225895 16852822125032139922838843)
  ·
    refine ⟨25279233187548209884258265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16852822125032139922838843 25279233187548209884258265)
    ·
      refine ⟨18959424890661157413193699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25279233187548209884258265 18959424890661157413193699)
      ·
        refine ⟨28439137335991736119790549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18959424890661157413193699 28439137335991736119790549)
        ·
          refine ⟨666542281312306315307591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 28439137335991736119790549 666542281312306315307591)
          ·
            refine ⟨999813421968459472961387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666542281312306315307591 999813421968459472961387)
            ·
              refine ⟨1499720132952689209442081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999813421968459472961387 1499720132952689209442081)
              ·
                refine ⟨1124790099714516907081561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1499720132952689209442081 1124790099714516907081561)
                ·
                  refine ⟨843592574785887680311171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1124790099714516907081561 843592574785887680311171)
                  ·
                    refine ⟨1265388862178831520466757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 843592574785887680311171 1265388862178831520466757)
                    ·
                      refine ⟨237260411658530910087517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1265388862178831520466757 237260411658530910087517)
                      ·
                        rfl

theorem cell23_462063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 4].length) (baseStart_462063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462063 prefixEnd_462063 := by exact prefixLift 462063
  have htrace : WordTrace (prefixWord ++ tailWord_462063) baseStart_462063 baseEnd_462063 := by
    simpa [prefixWord, tailWord_462063, baseEnd_462063] using wordTrace_append hprefix tailTrace_462063
  have hstable : (prefixWord ++ tailWord_462063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462063).length < 2 ^ (prefixWord ++ tailWord_462063).sum := by decide
  have hdescent : baseEnd_462063 < baseStart_462063 := by decide
  rcases family_descends (prefixWord ++ tailWord_462063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462170 : List Nat := [3, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4]
def baseStart_462170 : Nat := 118140960795 + 462170 * 2 ^ 59
def prefixEnd_462170 : Nat := 4983230072969 + 3 ^ 40 * 462170 * 2
def baseEnd_462170 : Nat := 237315354088561991449525

theorem tailTrace_462170 : CollatzResearch.WordTrace tailWord_462170 prefixEnd_462170 237315354088561991449525 := by
  unfold tailWord_462170
  simp only [CollatzResearch.WordTrace]
  refine ⟨4214181183911124299245991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11237816490429664797989309 4214181183911124299245991)
  ·
    refine ⟨6321271775866686448868987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4214181183911124299245991 6321271775866686448868987)
    ·
      refine ⟨9481907663800029673303481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6321271775866686448868987 9481907663800029673303481)
      ·
        refine ⟨7111430747850022254977611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9481907663800029673303481 7111430747850022254977611)
        ·
          refine ⟨10667146121775033382466417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7111430747850022254977611 10667146121775033382466417)
          ·
            refine ⟨8000359591331275036849813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10667146121775033382466417 8000359591331275036849813)
            ·
              refine ⟨375016855843653517352335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8000359591331275036849813 375016855843653517352335)
              ·
                refine ⟨562525283765480276028503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375016855843653517352335 562525283765480276028503)
                ·
                  refine ⟨843787925648220414042755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 562525283765480276028503 843787925648220414042755)
                  ·
                    refine ⟨1265681888472330621064133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 843787925648220414042755 1265681888472330621064133)
                    ·
                      refine ⟨237315354088561991449525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1265681888472330621064133 237315354088561991449525)
                      ·
                        rfl

theorem cell23_462170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4].length) (baseStart_462170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462170 prefixEnd_462170 := by exact prefixLift 462170
  have htrace : WordTrace (prefixWord ++ tailWord_462170) baseStart_462170 baseEnd_462170 := by
    simpa [prefixWord, tailWord_462170, baseEnd_462170] using wordTrace_append hprefix tailTrace_462170
  have hstable : (prefixWord ++ tailWord_462170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462170).length < 2 ^ (prefixWord ++ tailWord_462170).sum := by decide
  have hdescent : baseEnd_462170 < baseStart_462170 := by decide
  rcases family_descends (prefixWord ++ tailWord_462170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462176 : List Nat := [2, 1, 1, 3, 4, 2, 10]
def baseStart_462176 : Nat := 118140960795 + 462176 * 2 ^ 59
def prefixEnd_462176 : Nat := 4983230072969 + 3 ^ 40 * 462176 * 2
def baseEnd_462176 : Nat := 2929857221882579851537

theorem tailTrace_462176 : CollatzResearch.WordTrace tailWord_462176 prefixEnd_462176 2929857221882579851537 := by
  unfold tailWord_462176
  simp only [CollatzResearch.WordTrace]
  refine ⟨8428471786811380110851191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11237962382415173481134921 8428471786811380110851191)
  ·
    refine ⟨12642707680217070166276787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8428471786811380110851191 12642707680217070166276787)
    ·
      refine ⟨18964061520325605249415181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12642707680217070166276787 18964061520325605249415181)
      ·
        refine ⟨7111523070122101968530693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18964061520325605249415181 7111523070122101968530693)
        ·
          refine ⟨1333410575647894119099505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7111523070122101968530693 1333410575647894119099505)
          ·
            refine ⟨1000057931735920589324629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1333410575647894119099505 1000057931735920589324629)
            ·
              refine ⟨2929857221882579851537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1000057931735920589324629 2929857221882579851537)
              ·
                rfl

theorem cell23_462176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 10].length) (baseStart_462176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462176 prefixEnd_462176 := by exact prefixLift 462176
  have htrace : WordTrace (prefixWord ++ tailWord_462176) baseStart_462176 baseEnd_462176 := by
    simpa [prefixWord, tailWord_462176, baseEnd_462176] using wordTrace_append hprefix tailTrace_462176
  have hstable : (prefixWord ++ tailWord_462176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462176).length < 2 ^ (prefixWord ++ tailWord_462176).sum := by decide
  have hdescent : baseEnd_462176 < baseStart_462176 := by decide
  rcases family_descends (prefixWord ++ tailWord_462176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462180 : List Nat := [2, 3, 1, 1, 3, 2, 3, 2, 2, 4]
def baseStart_462180 : Nat := 118140960795 + 462180 * 2 ^ 59
def prefixEnd_462180 : Nat := 4983230072969 + 3 ^ 40 * 462180 * 2
def baseEnd_462180 : Nat := 79106829631702317441493

theorem tailTrace_462180 : CollatzResearch.WordTrace tailWord_462180 prefixEnd_462180 79106829631702317441493 := by
  unfold tailWord_462180
  simp only [CollatzResearch.WordTrace]
  refine ⟨8428544732804134452423997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11238059643738845936565329 8428544732804134452423997)
  ·
    refine ⟨3160704274801550419658999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8428544732804134452423997 3160704274801550419658999)
    ·
      refine ⟨4741056412202325629488499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3160704274801550419658999 4741056412202325629488499)
      ·
        refine ⟨7111584618303488444232749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4741056412202325629488499 7111584618303488444232749)
        ·
          refine ⟨2666844231863808166587281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7111584618303488444232749 2666844231863808166587281)
          ·
            refine ⟨2000133173897856124940461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2666844231863808166587281 2000133173897856124940461)
            ·
              refine ⟨750049940211696046852673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2000133173897856124940461 750049940211696046852673)
              ·
                refine ⟨562537455158772035139505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 750049940211696046852673 562537455158772035139505)
                ·
                  refine ⟨421903091369079026354629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 562537455158772035139505 421903091369079026354629)
                  ·
                    refine ⟨79106829631702317441493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 421903091369079026354629 79106829631702317441493)
                    ·
                      rfl

theorem cell23_462180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_462180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462180 prefixEnd_462180 := by exact prefixLift 462180
  have htrace : WordTrace (prefixWord ++ tailWord_462180) baseStart_462180 baseEnd_462180 := by
    simpa [prefixWord, tailWord_462180, baseEnd_462180] using wordTrace_append hprefix tailTrace_462180
  have hstable : (prefixWord ++ tailWord_462180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462180).length < 2 ^ (prefixWord ++ tailWord_462180).sum := by decide
  have hdescent : baseEnd_462180 < baseStart_462180 := by decide
  rcases family_descends (prefixWord ++ tailWord_462180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462197 : List Nat := [1, 3, 4, 1, 4, 1, 1, 1, 1, 6]
def baseStart_462197 : Nat := 118140960795 + 462197 * 2 ^ 59
def prefixEnd_462197 : Nat := 4983230072969 + 3 ^ 40 * 462197 * 2
def baseEnd_462197 : Nat := 79109739355411128603967

theorem tailTrace_462197 : CollatzResearch.WordTrace tailWord_462197 prefixEnd_462197 79109739355411128603967 := by
  unfold tailWord_462197
  simp only [CollatzResearch.WordTrace]
  refine ⟨16857709506546680808216845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11238473004364453872144563 16857709506546680808216845)
  ·
    refine ⟨6321641064955005303081317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16857709506546680808216845 6321641064955005303081317)
    ·
      refine ⟨1185307699679063494327747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6321641064955005303081317 1185307699679063494327747)
      ·
        refine ⟨1777961549518595241491621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1185307699679063494327747 1777961549518595241491621)
        ·
          refine ⟨333367790534736607779679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1777961549518595241491621 333367790534736607779679)
          ·
            refine ⟨500051685802104911669519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333367790534736607779679 500051685802104911669519)
            ·
              refine ⟨750077528703157367504279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500051685802104911669519 750077528703157367504279)
              ·
                refine ⟨1125116293054736051256419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 750077528703157367504279 1125116293054736051256419)
                ·
                  refine ⟨1687674439582104076884629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1125116293054736051256419 1687674439582104076884629)
                  ·
                    refine ⟨79109739355411128603967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1687674439582104076884629 79109739355411128603967)
                    ·
                      rfl

theorem cell23_462197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_462197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462197 prefixEnd_462197 := by exact prefixLift 462197
  have htrace : WordTrace (prefixWord ++ tailWord_462197) baseStart_462197 baseEnd_462197 := by
    simpa [prefixWord, tailWord_462197, baseEnd_462197] using wordTrace_append hprefix tailTrace_462197
  have hstable : (prefixWord ++ tailWord_462197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462197).length < 2 ^ (prefixWord ++ tailWord_462197).sum := by decide
  have hdescent : baseEnd_462197 < baseStart_462197 := by decide
  rcases family_descends (prefixWord ++ tailWord_462197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462210 : List Nat := [3, 4, 2, 1, 1, 2, 1, 9]
def baseStart_462210 : Nat := 118140960795 + 462210 * 2 ^ 59
def prefixEnd_462210 : Nat := 4983230072969 + 3 ^ 40 * 462210 * 2
def baseEnd_462210 : Nat := 8790218270916364257383

theorem tailTrace_462210 : CollatzResearch.WordTrace tailWord_462210 prefixEnd_462210 8790218270916364257383 := by
  unfold tailWord_462210
  simp only [CollatzResearch.WordTrace]
  refine ⟨4214545913874896007110021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11238789103666389352293389 4214545913874896007110021)
  ·
    refine ⟨790227358851543001333129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4214545913874896007110021 790227358851543001333129)
    ·
      refine ⟨592670519138657250999847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 790227358851543001333129 592670519138657250999847)
      ·
        refine ⟨889005778707985876499771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592670519138657250999847 889005778707985876499771)
        ·
          refine ⟨1333508668061978814749657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 889005778707985876499771 1333508668061978814749657)
          ·
            refine ⟨1000131501046484111062243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1333508668061978814749657 1000131501046484111062243)
            ·
              refine ⟨1500197251569726166593365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000131501046484111062243 1500197251569726166593365)
              ·
                refine ⟨8790218270916364257383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1500197251569726166593365 8790218270916364257383)
                ·
                  rfl

theorem cell23_462210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 9].length) (baseStart_462210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462210 prefixEnd_462210 := by exact prefixLift 462210
  have htrace : WordTrace (prefixWord ++ tailWord_462210) baseStart_462210 baseEnd_462210 := by
    simpa [prefixWord, tailWord_462210, baseEnd_462210] using wordTrace_append hprefix tailTrace_462210
  have hstable : (prefixWord ++ tailWord_462210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462210).length < 2 ^ (prefixWord ++ tailWord_462210).sum := by decide
  have hdescent : baseEnd_462210 < baseStart_462210 := by decide
  rcases family_descends (prefixWord ++ tailWord_462210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462238 : List Nat := [4, 3, 1, 2, 3, 1, 1, 1, 3, 2, 2]
def baseStart_462238 : Nat := 118140960795 + 462238 * 2 ^ 59
def prefixEnd_462238 : Nat := 4983230072969 + 3 ^ 40 * 462238 * 2
def baseEnd_462238 : Nat := 237350270773067725399213

theorem tailTrace_462238 : CollatzResearch.WordTrace tailWord_462238 prefixEnd_462238 237350270773067725399213 := by
  unfold tailWord_462238
  simp only [CollatzResearch.WordTrace]
  refine ⟨2107400612424768101307421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11239469932932096540306245 2107400612424768101307421)
  ·
    refine ⟨790275229659288037990283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2107400612424768101307421 790275229659288037990283)
    ·
      refine ⟨1185412844488932056985425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 790275229659288037990283 1185412844488932056985425)
      ·
        refine ⟨889059633366699042739069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1185412844488932056985425 889059633366699042739069)
        ·
          refine ⟨333397362512512141027151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 889059633366699042739069 333397362512512141027151)
          ·
            refine ⟨500096043768768211540727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333397362512512141027151 500096043768768211540727)
            ·
              refine ⟨750144065653152317311091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500096043768768211540727 750144065653152317311091)
              ·
                refine ⟨1125216098479728475966637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 750144065653152317311091 1125216098479728475966637)
                ·
                  refine ⟨421956036929898178487489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1125216098479728475966637 421956036929898178487489)
                  ·
                    refine ⟨316467027697423633865617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 421956036929898178487489 316467027697423633865617)
                    ·
                      refine ⟨237350270773067725399213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 316467027697423633865617 237350270773067725399213)
                      ·
                        rfl

theorem cell23_462238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_462238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462238 prefixEnd_462238 := by exact prefixLift 462238
  have htrace : WordTrace (prefixWord ++ tailWord_462238) baseStart_462238 baseEnd_462238 := by
    simpa [prefixWord, tailWord_462238, baseEnd_462238] using wordTrace_append hprefix tailTrace_462238
  have hstable : (prefixWord ++ tailWord_462238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462238).length < 2 ^ (prefixWord ++ tailWord_462238).sum := by decide
  have hdescent : baseEnd_462238 < baseStart_462238 := by decide
  rcases family_descends (prefixWord ++ tailWord_462238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462370 : List Nat := [3, 3, 1, 1, 1, 1, 3, 2, 1, 4, 3]
def baseStart_462370 : Nat := 118140960795 + 462370 * 2 ^ 59
def prefixEnd_462370 : Nat := 4983230072969 + 3 ^ 40 * 462370 * 2
def baseEnd_462370 : Nat := 237418050219461208948605

theorem tailTrace_462370 : CollatzResearch.WordTrace tailWord_462370 prefixEnd_462370 237418050219461208948605 := by
  unfold tailWord_462370
  simp only [CollatzResearch.WordTrace]
  refine ⟨4216004833729982838566141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11242679556613287569509709 4216004833729982838566141)
  ·
    refine ⟨1581001812648743564462303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4216004833729982838566141 1581001812648743564462303)
    ·
      refine ⟨2371502718973115346693455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1581001812648743564462303 2371502718973115346693455)
      ·
        refine ⟨3557254078459673020040183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2371502718973115346693455 3557254078459673020040183)
        ·
          refine ⟨5335881117689509530060275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3557254078459673020040183 5335881117689509530060275)
          ·
            refine ⟨8003821676534264295090413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5335881117689509530060275 8003821676534264295090413)
            ·
              refine ⟨3001433128700349110658905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8003821676534264295090413 3001433128700349110658905)
              ·
                refine ⟨2251074846525261832994179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3001433128700349110658905 2251074846525261832994179)
                ·
                  refine ⟨3376612269787892749491269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2251074846525261832994179 3376612269787892749491269)
                  ·
                    refine ⟨633114800585229890529613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3376612269787892749491269 633114800585229890529613)
                    ·
                      refine ⟨237418050219461208948605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 633114800585229890529613 237418050219461208948605)
                      ·
                        rfl

theorem cell23_462370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_462370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462370 prefixEnd_462370 := by exact prefixLift 462370
  have htrace : WordTrace (prefixWord ++ tailWord_462370) baseStart_462370 baseEnd_462370 := by
    simpa [prefixWord, tailWord_462370, baseEnd_462370] using wordTrace_append hprefix tailTrace_462370
  have hstable : (prefixWord ++ tailWord_462370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462370).length < 2 ^ (prefixWord ++ tailWord_462370).sum := by decide
  have hdescent : baseEnd_462370 < baseStart_462370 := by decide
  rcases family_descends (prefixWord ++ tailWord_462370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462403 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 7, 5]
def baseStart_462403 : Nat := 118140960795 + 462403 * 2 ^ 59
def prefixEnd_462403 : Nat := 4983230072969 + 3 ^ 40 * 462403 * 2
def baseEnd_462403 : Nat := 79144998360353193278651

theorem tailTrace_462403 : CollatzResearch.WordTrace tailWord_462403 prefixEnd_462403 79144998360353193278651 := by
  unfold tailWord_462403
  simp only [CollatzResearch.WordTrace]
  refine ⟨16865222943800377990215863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11243481962533585326810575 16865222943800377990215863)
  ·
    refine ⟨25297834415700566985323795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16865222943800377990215863 25297834415700566985323795)
    ·
      refine ⟨37946751623550850477985693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25297834415700566985323795 37946751623550850477985693)
      ·
        refine ⟨14230031858831568929244635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37946751623550850477985693 14230031858831568929244635)
        ·
          refine ⟨21345047788247353393866953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14230031858831568929244635 21345047788247353393866953)
          ·
            refine ⟨16008785841185515045400215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21345047788247353393866953 16008785841185515045400215)
            ·
              refine ⟨24013178761778272568100323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16008785841185515045400215 24013178761778272568100323)
              ·
                refine ⟨36019768142667408852150485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24013178761778272568100323 36019768142667408852150485)
                ·
                  refine ⟨844213315843767394972277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 36019768142667408852150485 844213315843767394972277)
                  ·
                    refine ⟨79144998360353193278651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 844213315843767394972277 79144998360353193278651)
                    ·
                      rfl

theorem cell23_462403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 5].length) (baseStart_462403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462403 prefixEnd_462403 := by exact prefixLift 462403
  have htrace : WordTrace (prefixWord ++ tailWord_462403) baseStart_462403 baseEnd_462403 := by
    simpa [prefixWord, tailWord_462403, baseEnd_462403] using wordTrace_append hprefix tailTrace_462403
  have hstable : (prefixWord ++ tailWord_462403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462403).length < 2 ^ (prefixWord ++ tailWord_462403).sum := by decide
  have hdescent : baseEnd_462403 < baseStart_462403 := by decide
  rcases family_descends (prefixWord ++ tailWord_462403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462420 : List Nat := [2, 4, 1, 1, 1, 2, 2, 2, 3, 5]
def baseStart_462420 : Nat := 118140960795 + 462420 * 2 ^ 59
def prefixEnd_462420 : Nat := 4983230072969 + 3 ^ 40 * 462420 * 2
def baseEnd_462420 : Nat := 79147908084062004441125

theorem tailTrace_462420 : CollatzResearch.WordTrace tailWord_462420 prefixEnd_462420 79147908084062004441125 := by
  unfold tailWord_462420
  simp only [CollatzResearch.WordTrace]
  refine ⟨8432921492369394946792357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11243895323159193262389809 8432921492369394946792357)
  ·
    refine ⟨1581172779819261552523567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8432921492369394946792357 1581172779819261552523567)
    ·
      refine ⟨2371759169728892328785351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1581172779819261552523567 2371759169728892328785351)
      ·
        refine ⟨3557638754593338493178027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2371759169728892328785351 3557638754593338493178027)
        ·
          refine ⟨5336458131890007739767041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3557638754593338493178027 5336458131890007739767041)
          ·
            refine ⟨4002343598917505804825281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5336458131890007739767041 4002343598917505804825281)
            ·
              refine ⟨3001757699188129353618961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4002343598917505804825281 3001757699188129353618961)
              ·
                refine ⟨2251318274391097015214221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3001757699188129353618961 2251318274391097015214221)
                ·
                  refine ⟨844244352896661380705333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2251318274391097015214221 844244352896661380705333)
                  ·
                    refine ⟨79147908084062004441125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 844244352896661380705333 79147908084062004441125)
                    ·
                      rfl

theorem cell23_462420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_462420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462420 prefixEnd_462420 := by exact prefixLift 462420
  have htrace : WordTrace (prefixWord ++ tailWord_462420) baseStart_462420 baseEnd_462420 := by
    simpa [prefixWord, tailWord_462420, baseEnd_462420] using wordTrace_append hprefix tailTrace_462420
  have hstable : (prefixWord ++ tailWord_462420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462420).length < 2 ^ (prefixWord ++ tailWord_462420).sum := by decide
  have hdescent : baseEnd_462420 < baseStart_462420 := by decide
  rcases family_descends (prefixWord ++ tailWord_462420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462437 : List Nat := [1, 3, 1, 3, 3, 1, 3, 2, 1, 5]
def baseStart_462437 : Nat := 118140960795 + 462437 * 2 ^ 59
def prefixEnd_462437 : Nat := 4983230072969 + 3 ^ 40 * 462437 * 2
def baseEnd_462437 : Nat := 79150817807770815603599

theorem tailTrace_462437 : CollatzResearch.WordTrace tailWord_462437 prefixEnd_462437 79150817807770815603599 := by
  unfold tailWord_462437
  simp only [CollatzResearch.WordTrace]
  refine ⟨16866463025677201796953565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11244308683784801197969043 16866463025677201796953565)
  ·
    refine ⟨6324923634628950673857587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16866463025677201796953565 6324923634628950673857587)
    ·
      refine ⟨9487385451943426010786381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6324923634628950673857587 9487385451943426010786381)
      ·
        refine ⟨3557769544478784754044893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9487385451943426010786381 3557769544478784754044893)
        ·
          refine ⟨1334163579179544282766835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3557769544478784754044893 1334163579179544282766835)
          ·
            refine ⟨2001245368769316424150253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1334163579179544282766835 2001245368769316424150253)
            ·
              refine ⟨750467013288493659056345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2001245368769316424150253 750467013288493659056345)
              ·
                refine ⟨562850259966370244292259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 750467013288493659056345 562850259966370244292259)
                ·
                  refine ⟨844275389949555366438389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 562850259966370244292259 844275389949555366438389)
                  ·
                    refine ⟨79150817807770815603599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 844275389949555366438389 79150817807770815603599)
                    ·
                      rfl

theorem cell23_462437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 5].length) (baseStart_462437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462437 prefixEnd_462437 := by exact prefixLift 462437
  have htrace : WordTrace (prefixWord ++ tailWord_462437) baseStart_462437 baseEnd_462437 := by
    simpa [prefixWord, tailWord_462437, baseEnd_462437] using wordTrace_append hprefix tailTrace_462437
  have hstable : (prefixWord ++ tailWord_462437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462437).length < 2 ^ (prefixWord ++ tailWord_462437).sum := by decide
  have hdescent : baseEnd_462437 < baseStart_462437 := by decide
  rcases family_descends (prefixWord ++ tailWord_462437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462450 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 3, 6]
def baseStart_462450 : Nat := 118140960795 + 462450 * 2 ^ 59
def prefixEnd_462450 : Nat := 4983230072969 + 3 ^ 40 * 462450 * 2
def baseEnd_462450 : Nat := 79153042890606965316079

theorem tailTrace_462450 : CollatzResearch.WordTrace tailWord_462450 prefixEnd_462450 79153042890606965316079 := by
  unfold tailWord_462450
  simp only [CollatzResearch.WordTrace]
  refine ⟨4216734293657526254294201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11244624783086736678117869 4216734293657526254294201)
  ·
    refine ⟨3162550720243144690720651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4216734293657526254294201 3162550720243144690720651)
    ·
      refine ⟨4743826080364717036080977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3162550720243144690720651 4743826080364717036080977)
      ·
        refine ⟨3557869560273537777060733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4743826080364717036080977 3557869560273537777060733)
        ·
          refine ⟨1334201085102576666397775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3557869560273537777060733 1334201085102576666397775)
          ·
            refine ⟨2001301627653864999596663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1334201085102576666397775 2001301627653864999596663)
            ·
              refine ⟨3001952441480797499394995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2001301627653864999596663 3001952441480797499394995)
              ·
                refine ⟨4502928662221196249092493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3001952441480797499394995 4502928662221196249092493)
                ·
                  refine ⟨1688598248332948593409685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4502928662221196249092493 1688598248332948593409685)
                  ·
                    refine ⟨79153042890606965316079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1688598248332948593409685 79153042890606965316079)
                    ·
                      rfl

theorem cell23_462450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_462450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462450 prefixEnd_462450 := by exact prefixLift 462450
  have htrace : WordTrace (prefixWord ++ tailWord_462450) baseStart_462450 baseEnd_462450 := by
    simpa [prefixWord, tailWord_462450, baseEnd_462450] using wordTrace_append hprefix tailTrace_462450
  have hstable : (prefixWord ++ tailWord_462450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462450).length < 2 ^ (prefixWord ++ tailWord_462450).sum := by decide
  have hdescent : baseEnd_462450 < baseStart_462450 := by decide
  rcases family_descends (prefixWord ++ tailWord_462450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462484 : List Nat := [2, 4, 2, 2, 2, 1, 2, 1, 1, 6]
def baseStart_462484 : Nat := 118140960795 + 462484 * 2 ^ 59
def prefixEnd_462484 : Nat := 4983230072969 + 3 ^ 40 * 462484 * 2
def baseEnd_462484 : Nat := 79158862338024587641027

theorem tailTrace_462484 : CollatzResearch.WordTrace tailWord_462484 prefixEnd_462484 79158862338024587641027 := by
  unfold tailWord_462484
  simp only [CollatzResearch.WordTrace]
  refine ⟨8434088628253464411957253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11245451504337952549276337 8434088628253464411957253)
  ·
    refine ⟨1581391617797524577241985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8434088628253464411957253 1581391617797524577241985)
    ·
      refine ⟨1186043713348143432931489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1581391617797524577241985 1186043713348143432931489)
      ·
        refine ⟨889532785011107574698617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1186043713348143432931489 889532785011107574698617)
        ·
          refine ⟨667149588758330681023963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 889532785011107574698617 667149588758330681023963)
          ·
            refine ⟨1000724383137496021535945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667149588758330681023963 1000724383137496021535945)
            ·
              refine ⟨750543287353122016151959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1000724383137496021535945 750543287353122016151959)
              ·
                refine ⟨1125814931029683024227939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 750543287353122016151959 1125814931029683024227939)
                ·
                  refine ⟨1688722396544524536341909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1125814931029683024227939 1688722396544524536341909)
                  ·
                    refine ⟨79158862338024587641027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1688722396544524536341909 79158862338024587641027)
                    ·
                      rfl

theorem cell23_462484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_462484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462484 prefixEnd_462484 := by exact prefixLift 462484
  have htrace : WordTrace (prefixWord ++ tailWord_462484) baseStart_462484 baseEnd_462484 := by
    simpa [prefixWord, tailWord_462484, baseEnd_462484] using wordTrace_append hprefix tailTrace_462484
  have hstable : (prefixWord ++ tailWord_462484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462484).length < 2 ^ (prefixWord ++ tailWord_462484).sum := by decide
  have hdescent : baseEnd_462484 < baseStart_462484 := by decide
  rcases family_descends (prefixWord ++ tailWord_462484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462487 : List Nat := [1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 4]
def baseStart_462487 : Nat := 118140960795 + 462487 * 2 ^ 59
def prefixEnd_462487 : Nat := 4983230072969 + 3 ^ 40 * 462487 * 2
def baseEnd_462487 : Nat := 237478127456037251185567

theorem tailTrace_462487 : CollatzResearch.WordTrace tailWord_462487 prefixEnd_462487 237478127456037251185567 := by
  unfold tailWord_462487
  simp only [CollatzResearch.WordTrace]
  refine ⟨16868286675496060336273715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11245524450330706890849143 16868286675496060336273715)
  ·
    refine ⟨25302430013244090504410573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16868286675496060336273715 25302430013244090504410573)
    ·
      refine ⟨9488411254966533939153965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25302430013244090504410573 9488411254966533939153965)
      ·
        refine ⟨3558154220612450227182737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9488411254966533939153965 3558154220612450227182737)
        ·
          refine ⟨2668615665459337670387053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3558154220612450227182737 2668615665459337670387053)
          ·
            refine ⟨1000730874547251626395145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2668615665459337670387053 1000730874547251626395145)
            ·
              refine ⟨750548155910438719796359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1000730874547251626395145 750548155910438719796359)
              ·
                refine ⟨1125822233865658079694539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 750548155910438719796359 1125822233865658079694539)
                ·
                  refine ⟨1688733350798487119541809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1125822233865658079694539 1688733350798487119541809)
                  ·
                    refine ⟨1266550013098865339656357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1688733350798487119541809 1266550013098865339656357)
                    ·
                      refine ⟨237478127456037251185567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1266550013098865339656357 237478127456037251185567)
                      ·
                        rfl

theorem cell23_462487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_462487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462487 prefixEnd_462487 := by exact prefixLift 462487
  have htrace : WordTrace (prefixWord ++ tailWord_462487) baseStart_462487 baseEnd_462487 := by
    simpa [prefixWord, tailWord_462487, baseEnd_462487] using wordTrace_append hprefix tailTrace_462487
  have hstable : (prefixWord ++ tailWord_462487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462487).length < 2 ^ (prefixWord ++ tailWord_462487).sum := by decide
  have hdescent : baseEnd_462487 < baseStart_462487 := by decide
  rcases family_descends (prefixWord ++ tailWord_462487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462494 : List Nat := [4, 3, 1, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_462494 : Nat := 118140960795 + 462494 * 2 ^ 59
def prefixEnd_462494 : Nat := 4983230072969 + 3 ^ 40 * 462494 * 2
def baseEnd_462494 : Nat := 237481721820618723798035

theorem tailTrace_462494 : CollatzResearch.WordTrace tailWord_462494 prefixEnd_462494 237481721820618723798035 := by
  unfold tailWord_462494
  simp only [CollatzResearch.WordTrace]
  refine ⟨2108567748308837566472317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11245694657647133687852357 2108567748308837566472317)
  ·
    refine ⟨790712905615814087427119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2108567748308837566472317 790712905615814087427119)
    ·
      refine ⟨1186069358423721131140679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 790712905615814087427119 1186069358423721131140679)
      ·
        refine ⟨1779104037635581696711019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1186069358423721131140679 1779104037635581696711019)
        ·
          refine ⟨2668656056453372545066529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1779104037635581696711019 2668656056453372545066529)
          ·
            refine ⟨2001492042340029408799897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2668656056453372545066529 2001492042340029408799897)
            ·
              refine ⟨1501119031755022056599923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2001492042340029408799897 1501119031755022056599923)
              ·
                refine ⟨2251678547632533084899885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1501119031755022056599923 2251678547632533084899885)
                ·
                  refine ⟨844379455362199906837457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2251678547632533084899885 844379455362199906837457)
                  ·
                    refine ⟨633284591521649930128093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 844379455362199906837457 633284591521649930128093)
                    ·
                      refine ⟨237481721820618723798035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 633284591521649930128093 237481721820618723798035)
                      ·
                        rfl

theorem cell23_462494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_462494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462494 prefixEnd_462494 := by exact prefixLift 462494
  have htrace : WordTrace (prefixWord ++ tailWord_462494) baseStart_462494 baseEnd_462494 := by
    simpa [prefixWord, tailWord_462494, baseEnd_462494] using wordTrace_append hprefix tailTrace_462494
  have hstable : (prefixWord ++ tailWord_462494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462494).length < 2 ^ (prefixWord ++ tailWord_462494).sum := by decide
  have hdescent : baseEnd_462494 < baseStart_462494 := by decide
  rcases family_descends (prefixWord ++ tailWord_462494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462497 : List Nat := [1, 2, 3, 3, 2, 2, 3, 7]
def baseStart_462497 : Nat := 118140960795 + 462497 * 2 ^ 59
def prefixEnd_462497 : Nat := 4983230072969 + 3 ^ 40 * 462497 * 2
def baseEnd_462497 : Nat := 8795676380095637483723

theorem tailTrace_462497 : CollatzResearch.WordTrace tailWord_462497 prefixEnd_462497 8795676380095637483723 := by
  unfold tailWord_462497
  simp only [CollatzResearch.WordTrace]
  refine ⟨16868651405459832044137745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11245767603639888029425163 16868651405459832044137745)
  ·
    refine ⟨12651488554094874033103309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16868651405459832044137745 12651488554094874033103309)
    ·
      refine ⟨4744308207785577762413741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12651488554094874033103309 4744308207785577762413741)
      ·
        refine ⟨1779115577919591660905153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4744308207785577762413741 1779115577919591660905153)
        ·
          refine ⟨1334336683439693745678865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1779115577919591660905153 1334336683439693745678865)
          ·
            refine ⟨1000752512579770309259149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1334336683439693745678865 1000752512579770309259149)
            ·
              refine ⟨375282192217413865972181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1000752512579770309259149 375282192217413865972181)
              ·
                refine ⟨8795676380095637483723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 375282192217413865972181 8795676380095637483723)
                ·
                  rfl

theorem cell23_462497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 7].length) (baseStart_462497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462497 prefixEnd_462497 := by exact prefixLift 462497
  have htrace : WordTrace (prefixWord ++ tailWord_462497) baseStart_462497 baseEnd_462497 := by
    simpa [prefixWord, tailWord_462497, baseEnd_462497] using wordTrace_append hprefix tailTrace_462497
  have hstable : (prefixWord ++ tailWord_462497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462497).length < 2 ^ (prefixWord ++ tailWord_462497).sum := by decide
  have hdescent : baseEnd_462497 < baseStart_462497 := by decide
  rcases family_descends (prefixWord ++ tailWord_462497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462518 : List Nat := [5, 1, 3, 1, 1, 3, 1, 2, 2, 4]
def baseStart_462518 : Nat := 118140960795 + 462518 * 2 ^ 59
def prefixEnd_462518 : Nat := 4983230072969 + 3 ^ 40 * 462518 * 2
def baseEnd_462518 : Nat := 79164681785442209965975

theorem tailTrace_462518 : CollatzResearch.WordTrace tailWord_462518 prefixEnd_462518 79164681785442209965975 := by
  unfold tailWord_462518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1054338583648984539415763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11246278225589168420434805 1054338583648984539415763)
  ·
    refine ⟨1581507875473476809123645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1054338583648984539415763 1581507875473476809123645)
    ·
      refine ⟨593065453302553803421367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1581507875473476809123645 593065453302553803421367)
      ·
        refine ⟨889598179953830705132051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593065453302553803421367 889598179953830705132051)
        ·
          refine ⟨1334397269930746057698077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 889598179953830705132051 1334397269930746057698077)
          ·
            refine ⟨500398976224029771636779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1334397269930746057698077 500398976224029771636779)
            ·
              refine ⟨750598464336044657455169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500398976224029771636779 750598464336044657455169)
              ·
                refine ⟨562948848252033493091377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 750598464336044657455169 562948848252033493091377)
                ·
                  refine ⟨422211636189025119818533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 562948848252033493091377 422211636189025119818533)
                  ·
                    refine ⟨79164681785442209965975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 422211636189025119818533 79164681785442209965975)
                    ·
                      rfl

theorem cell23_462518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_462518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462518 prefixEnd_462518 := by exact prefixLift 462518
  have htrace : WordTrace (prefixWord ++ tailWord_462518) baseStart_462518 baseEnd_462518 := by
    simpa [prefixWord, tailWord_462518, baseEnd_462518] using wordTrace_append hprefix tailTrace_462518
  have hstable : (prefixWord ++ tailWord_462518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462518).length < 2 ^ (prefixWord ++ tailWord_462518).sum := by decide
  have hdescent : baseEnd_462518 < baseStart_462518 := by decide
  rcases family_descends (prefixWord ++ tailWord_462518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462524 : List Nat := [2, 2, 2, 3, 1, 3, 1, 1, 4, 1, 3]
def baseStart_462524 : Nat := 118140960795 + 462524 * 2 ^ 59
def prefixEnd_462524 : Nat := 4983230072969 + 3 ^ 40 * 462524 * 2
def baseEnd_462524 : Nat := 237497126240253606422897

theorem tailTrace_462524 : CollatzResearch.WordTrace tailWord_462524 prefixEnd_462524 237497126240253606422897 := by
  unfold tailWord_462524
  simp only [CollatzResearch.WordTrace]
  refine ⟨8434818088181007827685313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11246424117574677103580417 8434818088181007827685313)
  ·
    refine ⟨6326113566135755870763985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8434818088181007827685313 6326113566135755870763985)
    ·
      refine ⟨4744585174601816903072989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6326113566135755870763985 4744585174601816903072989)
      ·
        refine ⟨1779219440475681338652371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4744585174601816903072989 1779219440475681338652371)
        ·
          refine ⟨2668829160713522007978557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1779219440475681338652371 2668829160713522007978557)
          ·
            refine ⟨1000810935267570752991959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2668829160713522007978557 1000810935267570752991959)
            ·
              refine ⟨1501216402901356129487939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000810935267570752991959 1501216402901356129487939)
              ·
                refine ⟨2251824604352034194231909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1501216402901356129487939 2251824604352034194231909)
                ·
                  refine ⟨422217113316006411418483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2251824604352034194231909 422217113316006411418483)
                  ·
                    refine ⟨633325669974009617127725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 422217113316006411418483 633325669974009617127725)
                    ·
                      refine ⟨237497126240253606422897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 633325669974009617127725 237497126240253606422897)
                      ·
                        rfl

theorem cell23_462524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_462524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462524 prefixEnd_462524 := by exact prefixLift 462524
  have htrace : WordTrace (prefixWord ++ tailWord_462524) baseStart_462524 baseEnd_462524 := by
    simpa [prefixWord, tailWord_462524, baseEnd_462524] using wordTrace_append hprefix tailTrace_462524
  have hstable : (prefixWord ++ tailWord_462524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462524).length < 2 ^ (prefixWord ++ tailWord_462524).sum := by decide
  have hdescent : baseEnd_462524 < baseStart_462524 := by decide
  rcases family_descends (prefixWord ++ tailWord_462524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462541 : List Nat := [1, 6, 2, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_462541 : Nat := 118140960795 + 462541 * 2 ^ 59
def prefixEnd_462541 : Nat := 4983230072969 + 3 ^ 40 * 462541 * 2
def baseEnd_462541 : Nat := 237505855411380039910319

theorem tailTrace_462541 : CollatzResearch.WordTrace tailWord_462541 prefixEnd_462541 237505855411380039910319 := by
  unfold tailWord_462541
  simp only [CollatzResearch.WordTrace]
  refine ⟨16870256217300427558739477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11246837478200285039159651 16870256217300427558739477)
  ·
    refine ⟨790793260185957541815913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16870256217300427558739477 790793260185957541815913)
    ·
      refine ⟨593094945139468156361935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 790793260185957541815913 593094945139468156361935)
      ·
        refine ⟨889642417709202234542903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593094945139468156361935 889642417709202234542903)
        ·
          refine ⟨1334463626563803351814355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 889642417709202234542903 1334463626563803351814355)
          ·
            refine ⟨2001695439845705027721533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1334463626563803351814355 2001695439845705027721533)
            ·
              refine ⟨750635789942139385395575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2001695439845705027721533 750635789942139385395575)
              ·
                refine ⟨1125953684913209078093363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 750635789942139385395575 1125953684913209078093363)
                ·
                  refine ⟨1688930527369813617140045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1125953684913209078093363 1688930527369813617140045)
                  ·
                    refine ⟨633348947763680106427517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1688930527369813617140045 633348947763680106427517)
                    ·
                      refine ⟨237505855411380039910319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 633348947763680106427517 237505855411380039910319)
                      ·
                        rfl

theorem cell23_462541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_462541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462541 prefixEnd_462541 := by exact prefixLift 462541
  have htrace : WordTrace (prefixWord ++ tailWord_462541) baseStart_462541 baseEnd_462541 := by
    simpa [prefixWord, tailWord_462541, baseEnd_462541] using wordTrace_append hprefix tailTrace_462541
  have hstable : (prefixWord ++ tailWord_462541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462541).length < 2 ^ (prefixWord ++ tailWord_462541).sum := by decide
  have hdescent : baseEnd_462541 < baseStart_462541 := by decide
  rcases family_descends (prefixWord ++ tailWord_462541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462560 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 4]
def baseStart_462560 : Nat := 118140960795 + 462560 * 2 ^ 59
def prefixEnd_462560 : Nat := 4983230072969 + 3 ^ 40 * 462560 * 2
def baseEnd_462560 : Nat := 237515611543815465572731

theorem tailTrace_462560 : CollatzResearch.WordTrace tailWord_462560 prefixEnd_462560 237515611543815465572731 := by
  unfold tailWord_462560
  simp only [CollatzResearch.WordTrace]
  refine ⟨8435474602115796901840567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11247299469487729202454089 8435474602115796901840567)
  ·
    refine ⟨12653211903173695352760851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8435474602115796901840567 12653211903173695352760851)
    ·
      refine ⟨18979817854760543029141277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12653211903173695352760851 18979817854760543029141277)
      ·
        refine ⟨7117431695535203635927979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18979817854760543029141277 7117431695535203635927979)
        ·
          refine ⟨10676147543302805453891969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7117431695535203635927979 10676147543302805453891969)
          ·
            refine ⟨8007110657477104090418977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10676147543302805453891969 8007110657477104090418977)
            ·
              refine ⟨6005332993107828067814233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8007110657477104090418977 6005332993107828067814233)
              ·
                refine ⟨4503999744830871050860675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6005332993107828067814233 4503999744830871050860675)
                ·
                  refine ⟨6755999617246306576291013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4503999744830871050860675 6755999617246306576291013)
                  ·
                    refine ⟨1266749928233682483054565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6755999617246306576291013 1266749928233682483054565)
                    ·
                      refine ⟨237515611543815465572731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1266749928233682483054565 237515611543815465572731)
                      ·
                        rfl

theorem cell23_462560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_462560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462560 prefixEnd_462560 := by exact prefixLift 462560
  have htrace : WordTrace (prefixWord ++ tailWord_462560) baseStart_462560 baseEnd_462560 := by
    simpa [prefixWord, tailWord_462560, baseEnd_462560] using wordTrace_append hprefix tailTrace_462560
  have hstable : (prefixWord ++ tailWord_462560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462560).length < 2 ^ (prefixWord ++ tailWord_462560).sum := by decide
  have hdescent : baseEnd_462560 < baseStart_462560 := by decide
  rcases family_descends (prefixWord ++ tailWord_462560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462564 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 6, 2, 2]
def baseStart_462564 : Nat := 118140960795 + 462564 * 2 ^ 59
def prefixEnd_462564 : Nat := 4983230072969 + 3 ^ 40 * 462564 * 2
def baseEnd_462564 : Nat := 237517665466433449922713

theorem tailTrace_462564 : CollatzResearch.WordTrace tailWord_462564 prefixEnd_462564 237517665466433449922713 := by
  unfold tailWord_462564
  simp only [CollatzResearch.WordTrace]
  refine ⟨8435547548108551243413373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11247396730811401657884497 8435547548108551243413373)
  ·
    refine ⟨3163330330540706716280015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8435547548108551243413373 3163330330540706716280015)
    ·
      refine ⟨4744995495811060074420023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3163330330540706716280015 4744995495811060074420023)
      ·
        refine ⟨7117493243716590111630035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4744995495811060074420023 7117493243716590111630035)
        ·
          refine ⟨10676239865574885167445053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7117493243716590111630035 10676239865574885167445053)
          ·
            refine ⟨4003589949590581937791895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10676239865574885167445053 4003589949590581937791895)
            ·
              refine ⟨6005384924385872906687843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4003589949590581937791895 6005384924385872906687843)
              ·
                refine ⟨9008077386578809360031765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6005384924385872906687843 9008077386578809360031765)
                ·
                  refine ⟨422253627495881688751489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9008077386578809360031765 422253627495881688751489)
                  ·
                    refine ⟨316690220621911266563617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 422253627495881688751489 316690220621911266563617)
                    ·
                      refine ⟨237517665466433449922713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 316690220621911266563617 237517665466433449922713)
                      ·
                        rfl

theorem cell23_462564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 6, 2, 2].length) (baseStart_462564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462564 prefixEnd_462564 := by exact prefixLift 462564
  have htrace : WordTrace (prefixWord ++ tailWord_462564) baseStart_462564 baseEnd_462564 := by
    simpa [prefixWord, tailWord_462564, baseEnd_462564] using wordTrace_append hprefix tailTrace_462564
  have hstable : (prefixWord ++ tailWord_462564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462564).length < 2 ^ (prefixWord ++ tailWord_462564).sum := by decide
  have hdescent : baseEnd_462564 < baseStart_462564 := by decide
  rcases family_descends (prefixWord ++ tailWord_462564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462570 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 9]
def baseStart_462570 : Nat := 118140960795 + 462570 * 2 ^ 59
def prefixEnd_462570 : Nat := 4983230072969 + 3 ^ 40 * 462570 * 2
def baseEnd_462570 : Nat := 26391194038928936271965

theorem tailTrace_462570 : CollatzResearch.WordTrace tailWord_462570 prefixEnd_462570 26391194038928936271965 := by
  unfold tailWord_462570
  simp only [CollatzResearch.WordTrace]
  refine ⟨4217828483548841377886291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11247542622796910341030109 4217828483548841377886291)
  ·
    refine ⟨6326742725323262066829437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4217828483548841377886291 6326742725323262066829437)
    ·
      refine ⟨2372528521996223275061039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6326742725323262066829437 2372528521996223275061039)
      ·
        refine ⟨3558792782994334912591559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2372528521996223275061039 3558792782994334912591559)
        ·
          refine ⟨5338189174491502368887339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3558792782994334912591559 5338189174491502368887339)
          ·
            refine ⟨8007283761737253553331009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5338189174491502368887339 8007283761737253553331009)
            ·
              refine ⟨6005462821302940164998257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8007283761737253553331009 6005462821302940164998257)
              ·
                refine ⟨4504097115977205123748693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6005462821302940164998257 4504097115977205123748693)
                ·
                  refine ⟨26391194038928936271965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4504097115977205123748693 26391194038928936271965)
                  ·
                    rfl

theorem cell23_462570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 9].length) (baseStart_462570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462570 prefixEnd_462570 := by exact prefixLift 462570
  have htrace : WordTrace (prefixWord ++ tailWord_462570) baseStart_462570 baseEnd_462570 := by
    simpa [prefixWord, tailWord_462570, baseEnd_462570] using wordTrace_append hprefix tailTrace_462570
  have hstable : (prefixWord ++ tailWord_462570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462570).length < 2 ^ (prefixWord ++ tailWord_462570).sum := by decide
  have hdescent : baseEnd_462570 < baseStart_462570 := by decide
  rcases family_descends (prefixWord ++ tailWord_462570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462607 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 4, 5, 2]
def baseStart_462607 : Nat := 118140960795 + 462607 * 2 ^ 59
def prefixEnd_462607 : Nat := 4983230072969 + 3 ^ 40 * 462607 * 2
def baseEnd_462607 : Nat := 237539745134576781685015

theorem tailTrace_462607 : CollatzResearch.WordTrace tailWord_462607 prefixEnd_462607 237539745134576781685015 := by
  unfold tailWord_462607
  simp only [CollatzResearch.WordTrace]
  refine ⟨16872663435061320830642075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11248442290040880553761383 16872663435061320830642075)
  ·
    refine ⟨25308995152591981245963113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16872663435061320830642075 25308995152591981245963113)
    ·
      refine ⟨18981746364443985934472335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25308995152591981245963113 18981746364443985934472335)
      ·
        refine ⟨28472619546665978901708503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18981746364443985934472335 28472619546665978901708503)
        ·
          refine ⟨42708929319998968352562755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28472619546665978901708503 42708929319998968352562755)
          ·
            refine ⟨64063393979998452528844133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42708929319998968352562755 64063393979998452528844133)
            ·
              refine ⟨12011886371249709849158275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64063393979998452528844133 12011886371249709849158275)
              ·
                refine ⟨18017829556874564773737413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12011886371249709849158275 18017829556874564773737413)
                ·
                  refine ⟨3378343041913980895075765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18017829556874564773737413 3378343041913980895075765)
                  ·
                    refine ⟨316719660179435708913353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3378343041913980895075765 316719660179435708913353)
                    ·
                      refine ⟨237539745134576781685015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 316719660179435708913353 237539745134576781685015)
                      ·
                        rfl

theorem cell23_462607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 5, 2].length) (baseStart_462607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462607 prefixEnd_462607 := by exact prefixLift 462607
  have htrace : WordTrace (prefixWord ++ tailWord_462607) baseStart_462607 baseEnd_462607 := by
    simpa [prefixWord, tailWord_462607, baseEnd_462607] using wordTrace_append hprefix tailTrace_462607
  have hstable : (prefixWord ++ tailWord_462607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462607).length < 2 ^ (prefixWord ++ tailWord_462607).sum := by decide
  have hdescent : baseEnd_462607 < baseStart_462607 := by decide
  rcases family_descends (prefixWord ++ tailWord_462607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462644 : List Nat := [2, 5, 1, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_462644 : Nat := 118140960795 + 462644 * 2 ^ 59
def prefixEnd_462644 : Nat := 4983230072969 + 3 ^ 40 * 462644 * 2
def baseEnd_462644 : Nat := 237558743918793136922345

theorem tailTrace_462644 : CollatzResearch.WordTrace tailWord_462644 prefixEnd_462644 237558743918793136922345 := by
  unfold tailWord_462644
  simp only [CollatzResearch.WordTrace]
  refine ⟨8437006467963638074869493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11249341957284850766492657 8437006467963638074869493)
  ·
    refine ⟨790969356371591069519015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8437006467963638074869493 790969356371591069519015)
    ·
      refine ⟨1186454034557386604278523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 790969356371591069519015 1186454034557386604278523)
      ·
        refine ⟨1779681051836079906417785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1186454034557386604278523 1779681051836079906417785)
        ·
          refine ⟨1334760788877059929813339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1779681051836079906417785 1334760788877059929813339)
          ·
            refine ⟨2002141183315589894720009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1334760788877059929813339 2002141183315589894720009)
            ·
              refine ⟨1501605887486692421040007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2002141183315589894720009 1501605887486692421040007)
              ·
                refine ⟨2252408831230038631560011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1501605887486692421040007 2252408831230038631560011)
                ·
                  refine ⟨3378613246845057947340017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2252408831230038631560011 3378613246845057947340017)
                  ·
                    refine ⟨2533959935133793460505013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3378613246845057947340017 2533959935133793460505013)
                    ·
                      refine ⟨237558743918793136922345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2533959935133793460505013 237558743918793136922345)
                      ·
                        rfl

theorem cell23_462644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_462644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462644 prefixEnd_462644 := by exact prefixLift 462644
  have htrace : WordTrace (prefixWord ++ tailWord_462644) baseStart_462644 baseEnd_462644 := by
    simpa [prefixWord, tailWord_462644, baseEnd_462644] using wordTrace_append hprefix tailTrace_462644
  have hstable : (prefixWord ++ tailWord_462644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462644).length < 2 ^ (prefixWord ++ tailWord_462644).sum := by decide
  have hdescent : baseEnd_462644 < baseStart_462644 := by decide
  rcases family_descends (prefixWord ++ tailWord_462644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462664 : List Nat := [2, 1, 3, 1, 1, 5, 1, 2, 3, 4]
def baseStart_462664 : Nat := 118140960795 + 462664 * 2 ^ 59
def prefixEnd_462664 : Nat := 4983230072969 + 3 ^ 40 * 462664 * 2
def baseEnd_462664 : Nat := 79189671177294352890751

theorem tailTrace_462664 : CollatzResearch.WordTrace tailWord_462664 prefixEnd_462664 79189671177294352890751 := by
  unfold tailWord_462664
  simp only [CollatzResearch.WordTrace]
  refine ⟨8437371197927409782733523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11249828263903213043644697 8437371197927409782733523)
  ·
    refine ⟨12656056796891114674100285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8437371197927409782733523 12656056796891114674100285)
    ·
      refine ⟨4746021298834168002787607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12656056796891114674100285 4746021298834168002787607)
      ·
        refine ⟨7119031948251252004181411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4746021298834168002787607 7119031948251252004181411)
        ·
          refine ⟨10678547922376878006272117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7119031948251252004181411 10678547922376878006272117)
          ·
            refine ⟨1001113867722832313088011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10678547922376878006272117 1001113867722832313088011)
            ·
              refine ⟨1501670801584248469632017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001113867722832313088011 1501670801584248469632017)
              ·
                refine ⟨1126253101188186352224013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1501670801584248469632017 1126253101188186352224013)
                ·
                  refine ⟨422344912945569882084005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1126253101188186352224013 422344912945569882084005)
                  ·
                    refine ⟨79189671177294352890751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 422344912945569882084005 79189671177294352890751)
                    ·
                      rfl

theorem cell23_462664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_462664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462664 prefixEnd_462664 := by exact prefixLift 462664
  have htrace : WordTrace (prefixWord ++ tailWord_462664) baseStart_462664 baseEnd_462664 := by
    simpa [prefixWord, tailWord_462664, baseEnd_462664] using wordTrace_append hprefix tailTrace_462664
  have hstable : (prefixWord ++ tailWord_462664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462664).length < 2 ^ (prefixWord ++ tailWord_462664).sum := by decide
  have hdescent : baseEnd_462664 < baseStart_462664 := by decide
  rcases family_descends (prefixWord ++ tailWord_462664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462674 : List Nat := [3, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3]
def baseStart_462674 : Nat := 118140960795 + 462674 * 2 ^ 59
def prefixEnd_462674 : Nat := 4983230072969 + 3 ^ 40 * 462674 * 2
def baseEnd_462674 : Nat := 237574148338428019547207

theorem tailTrace_462674 : CollatzResearch.WordTrace tailWord_462674 prefixEnd_462674 237574148338428019547207 := by
  unfold tailWord_462674
  simp only [CollatzResearch.WordTrace]
  refine ⟨4218776781454647818332769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11250071417212394182220717 4218776781454647818332769)
  ·
    refine ⟨3164082586090985863749577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4218776781454647818332769 3164082586090985863749577)
    ·
      refine ⟨2373061939568239397812183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3164082586090985863749577 2373061939568239397812183)
      ·
        refine ⟨3559592909352359096718275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2373061939568239397812183 3559592909352359096718275)
        ·
          refine ⟨5339389364028538645077413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3559592909352359096718275 5339389364028538645077413)
          ·
            refine ⟨1001135505755350995952015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5339389364028538645077413 1001135505755350995952015)
            ·
              refine ⟨1501703258633026493928023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001135505755350995952015 1501703258633026493928023)
              ·
                refine ⟨2252554887949539740892035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1501703258633026493928023 2252554887949539740892035)
                ·
                  refine ⟨3378832331924309611338053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2252554887949539740892035 3378832331924309611338053)
                  ·
                    refine ⟨633531062235808052125885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3378832331924309611338053 633531062235808052125885)
                    ·
                      refine ⟨237574148338428019547207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 633531062235808052125885 237574148338428019547207)
                      ·
                        rfl

theorem cell23_462674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_462674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462674 prefixEnd_462674 := by exact prefixLift 462674
  have htrace : WordTrace (prefixWord ++ tailWord_462674) baseStart_462674 baseEnd_462674 := by
    simpa [prefixWord, tailWord_462674, baseEnd_462674] using wordTrace_append hprefix tailTrace_462674
  have hstable : (prefixWord ++ tailWord_462674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462674).length < 2 ^ (prefixWord ++ tailWord_462674).sum := by decide
  have hdescent : baseEnd_462674 < baseStart_462674 := by decide
  rcases family_descends (prefixWord ++ tailWord_462674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462681 : List Nat := [1, 2, 1, 2, 2, 3, 4, 3, 1, 4]
def baseStart_462681 : Nat := 118140960795 + 462681 * 2 ^ 59
def prefixEnd_462681 : Nat := 4983230072969 + 3 ^ 40 * 462681 * 2
def baseEnd_462681 : Nat := 79192580901003164053225

theorem tailTrace_462681 : CollatzResearch.WordTrace tailWord_462681 prefixEnd_462681 79192580901003164053225 := by
  unfold tailWord_462681
  simp only [CollatzResearch.WordTrace]
  refine ⟨16875362436793231468835897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11250241624528820979223931 16875362436793231468835897)
  ·
    refine ⟨12656521827594923601626923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16875362436793231468835897 12656521827594923601626923)
    ·
      refine ⟨18984782741392385402440385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12656521827594923601626923 18984782741392385402440385)
      ·
        refine ⟨14238587056044289051830289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18984782741392385402440385 14238587056044289051830289)
        ·
          refine ⟨10678940292033216788872717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14238587056044289051830289 10678940292033216788872717)
          ·
            refine ⟨4004602609512456295827269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10678940292033216788872717 4004602609512456295827269)
            ·
              refine ⟨750862989283585555467613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4004602609512456295827269 750862989283585555467613)
              ·
                refine ⟨281573620981344583300355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 750862989283585555467613 281573620981344583300355)
                ·
                  refine ⟨422360431472016874950533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 281573620981344583300355 422360431472016874950533)
                  ·
                    refine ⟨79192580901003164053225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 422360431472016874950533 79192580901003164053225)
                    ·
                      rfl

theorem cell23_462681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3, 1, 4].length) (baseStart_462681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462681 prefixEnd_462681 := by exact prefixLift 462681
  have htrace : WordTrace (prefixWord ++ tailWord_462681) baseStart_462681 baseEnd_462681 := by
    simpa [prefixWord, tailWord_462681, baseEnd_462681] using wordTrace_append hprefix tailTrace_462681
  have hstable : (prefixWord ++ tailWord_462681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462681).length < 2 ^ (prefixWord ++ tailWord_462681).sum := by decide
  have hdescent : baseEnd_462681 < baseStart_462681 := by decide
  rcases family_descends (prefixWord ++ tailWord_462681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462698 : List Nat := [3, 1, 3, 4, 1, 1, 2, 1, 3, 4]
def baseStart_462698 : Nat := 118140960795 + 462698 * 2 ^ 59
def prefixEnd_462698 : Nat := 4983230072969 + 3 ^ 40 * 462698 * 2
def baseEnd_462698 : Nat := 79195490624711975215699

theorem tailTrace_462698 : CollatzResearch.WordTrace tailWord_462698 prefixEnd_462698 79195490624711975215699 := by
  unfold tailWord_462698
  simp only [CollatzResearch.WordTrace]
  refine ⟨4218995619432910843051187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11250654985154428914803165 4218995619432910843051187)
  ·
    refine ⟨6328493429149366264576781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4218995619432910843051187 6328493429149366264576781)
    ·
      refine ⟨2373185035931012349216293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6328493429149366264576781 2373185035931012349216293)
      ·
        refine ⟨444972194237064815478055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2373185035931012349216293 444972194237064815478055)
        ·
          refine ⟨667458291355597223217083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444972194237064815478055 667458291355597223217083)
          ·
            refine ⟨1001187437033395834825625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667458291355597223217083 1001187437033395834825625)
            ·
              refine ⟨750890577775046876119219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1001187437033395834825625 750890577775046876119219)
              ·
                refine ⟨1126335866662570314178829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 750890577775046876119219 1126335866662570314178829)
                ·
                  refine ⟨422375949998463867817061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1126335866662570314178829 422375949998463867817061)
                  ·
                    refine ⟨79195490624711975215699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 422375949998463867817061 79195490624711975215699)
                    ·
                      rfl

theorem cell23_462698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_462698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462698 prefixEnd_462698 := by exact prefixLift 462698
  have htrace : WordTrace (prefixWord ++ tailWord_462698) baseStart_462698 baseEnd_462698 := by
    simpa [prefixWord, tailWord_462698, baseEnd_462698] using wordTrace_append hprefix tailTrace_462698
  have hstable : (prefixWord ++ tailWord_462698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462698).length < 2 ^ (prefixWord ++ tailWord_462698).sum := by decide
  have hdescent : baseEnd_462698 < baseStart_462698 := by decide
  rcases family_descends (prefixWord ++ tailWord_462698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462714 : List Nat := [3, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2]
def baseStart_462714 : Nat := 118140960795 + 462714 * 2 ^ 59
def prefixEnd_462714 : Nat := 4983230072969 + 3 ^ 40 * 462714 * 2
def baseEnd_462714 : Nat := 237594687564607863047023

theorem tailTrace_462714 : CollatzResearch.WordTrace tailWord_462714 prefixEnd_462714 237594687564607863047023 := by
  unfold tailWord_462714
  simp only [CollatzResearch.WordTrace]
  refine ⟨4219141511418419526196799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11251044030449118736524797 4219141511418419526196799)
  ·
    refine ⟨6328712267127629289295199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4219141511418419526196799 6328712267127629289295199)
    ·
      refine ⟨9493068400691443933942799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6328712267127629289295199 9493068400691443933942799)
      ·
        refine ⟨14239602601037165900914199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9493068400691443933942799 14239602601037165900914199)
        ·
          refine ⟨21359403901555748851371299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14239602601037165900914199 21359403901555748851371299)
          ·
            refine ⟨32039105852333623277056949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21359403901555748851371299 32039105852333623277056949)
            ·
              refine ⟨3003666173656277182224089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32039105852333623277056949 3003666173656277182224089)
              ·
                refine ⟨2252749630242207886668067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3003666173656277182224089 2252749630242207886668067)
                ·
                  refine ⟨3379124445363311830002101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2252749630242207886668067 3379124445363311830002101)
                  ·
                    refine ⟨316792916752810484062697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3379124445363311830002101 316792916752810484062697)
                    ·
                      refine ⟨237594687564607863047023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 316792916752810484062697 237594687564607863047023)
                      ·
                        rfl

theorem cell23_462714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2].length) (baseStart_462714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462714 prefixEnd_462714 := by exact prefixLift 462714
  have htrace : WordTrace (prefixWord ++ tailWord_462714) baseStart_462714 baseEnd_462714 := by
    simpa [prefixWord, tailWord_462714, baseEnd_462714] using wordTrace_append hprefix tailTrace_462714
  have hstable : (prefixWord ++ tailWord_462714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462714).length < 2 ^ (prefixWord ++ tailWord_462714).sum := by decide
  have hdescent : baseEnd_462714 < baseStart_462714 := by decide
  rcases family_descends (prefixWord ++ tailWord_462714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462724 : List Nat := [2, 3, 2, 1, 1, 1, 3, 4, 1, 5]
def baseStart_462724 : Nat := 118140960795 + 462724 * 2 ^ 59
def prefixEnd_462724 : Nat := 4983230072969 + 3 ^ 40 * 462724 * 2
def baseEnd_462724 : Nat := 79199940790384274640659

theorem tailTrace_462724 : CollatzResearch.WordTrace tailWord_462724 prefixEnd_462724 79199940790384274640659 := by
  unfold tailWord_462724
  simp only [CollatzResearch.WordTrace]
  refine ⟨8438465387818724906325613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11251287183758299875100817 8438465387818724906325613)
  ·
    refine ⟨3164424520432021839872105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8438465387818724906325613 3164424520432021839872105)
    ·
      refine ⟨2373318390324016379904079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3164424520432021839872105 2373318390324016379904079)
      ·
        refine ⟨3559977585486024569856119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2373318390324016379904079 3559977585486024569856119)
        ·
          refine ⟨5339966378229036854784179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3559977585486024569856119 5339966378229036854784179)
          ·
            refine ⟨8009949567343555282176269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5339966378229036854784179 8009949567343555282176269)
            ·
              refine ⟨3003731087753833230816101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8009949567343555282176269 3003731087753833230816101)
              ·
                refine ⟨563199578953843730778019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3003731087753833230816101 563199578953843730778019)
                ·
                  refine ⟨844799368430765596167029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 563199578953843730778019 844799368430765596167029)
                  ·
                    refine ⟨79199940790384274640659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 844799368430765596167029 79199940790384274640659)
                    ·
                      rfl

theorem cell23_462724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_462724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462724 prefixEnd_462724 := by exact prefixLift 462724
  have htrace : WordTrace (prefixWord ++ tailWord_462724) baseStart_462724 baseEnd_462724 := by
    simpa [prefixWord, tailWord_462724, baseEnd_462724] using wordTrace_append hprefix tailTrace_462724
  have hstable : (prefixWord ++ tailWord_462724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462724).length < 2 ^ (prefixWord ++ tailWord_462724).sum := by decide
  have hdescent : baseEnd_462724 < baseStart_462724 := by decide
  rcases family_descends (prefixWord ++ tailWord_462724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
