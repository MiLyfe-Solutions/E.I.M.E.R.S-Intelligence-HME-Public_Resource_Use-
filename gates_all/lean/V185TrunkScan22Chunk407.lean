import V185TrunkScan22Chunk406

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3629855 : List Nat := [1, 1, 2, 4, 2, 3, 1, 1, 7]
def baseStart_3629855 : Nat := 118140960795 + 3629855 * 2 ^ 59
def prefixEnd_3629855 : Nat := 4983230072969 + 3 ^ 40 * 3629855 * 2
def baseEnd_3629855 : Nat := 414191182472444646515357

theorem tailTrace_3629855 : CollatzResearch.WordTrace tailWord_3629855 prefixEnd_3629855 414191182472444646515357 := by
  unfold tailWord_3629855
  simp only [CollatzResearch.WordTrace]
  refine ⟨132391688264662739723971019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88261125509775159815980679 132391688264662739723971019)
  ·
    refine ⟨198587532396994109585956529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132391688264662739723971019 198587532396994109585956529)
    ·
      refine ⟨148940649297745582189467397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198587532396994109585956529 148940649297745582189467397)
      ·
        refine ⟨27926371743327296660525137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148940649297745582189467397 27926371743327296660525137)
        ·
          refine ⟨20944778807495472495393853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27926371743327296660525137 20944778807495472495393853)
          ·
            refine ⟨7854292052810802185772695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20944778807495472495393853 7854292052810802185772695)
            ·
              refine ⟨11781438079216203278659043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7854292052810802185772695 11781438079216203278659043)
              ·
                refine ⟨17672157118824304917988565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11781438079216203278659043 17672157118824304917988565)
                ·
                  refine ⟨414191182472444646515357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17672157118824304917988565 414191182472444646515357)
                  ·
                    rfl

theorem cell22_3629855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 7].length) (baseStart_3629855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629855 prefixEnd_3629855 := by exact prefixLift 3629855
  have htrace : WordTrace (prefixWord ++ tailWord_3629855) baseStart_3629855 baseEnd_3629855 := by
    simpa [prefixWord, tailWord_3629855, baseEnd_3629855] using wordTrace_append hprefix tailTrace_3629855
  have hstable : (prefixWord ++ tailWord_3629855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629855).length < 2 ^ (prefixWord ++ tailWord_3629855).sum := by decide
  have hdescent : baseEnd_3629855 < baseStart_3629855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629945 : List Nat := [1, 2, 1, 3, 2, 3, 2, 8]
def baseStart_3629945 : Nat := 118140960795 + 3629945 * 2 ^ 59
def prefixEnd_3629945 : Nat := 4983230072969 + 3 ^ 40 * 3629945 * 2
def baseEnd_3629945 : Nat := 138067150695178189421755

theorem tailTrace_3629945 : CollatzResearch.WordTrace tailWord_3629945 prefixEnd_3629945 138067150695178189421755 := by
  unfold tailWord_3629945
  simp only [CollatzResearch.WordTrace]
  refine ⟨132394970834336685094747289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88263313889557790063164859 132394970834336685094747289)
  ·
    refine ⟨99296228125752513821060467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132394970834336685094747289 99296228125752513821060467)
    ·
      refine ⟨148944342188628770731590701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99296228125752513821060467 148944342188628770731590701)
      ·
        refine ⟨55854128320735789024346513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148944342188628770731590701 55854128320735789024346513)
        ·
          refine ⟨41890596240551841768259885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55854128320735789024346513 41890596240551841768259885)
          ·
            refine ⟨15708973590206940663097457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41890596240551841768259885 15708973590206940663097457)
            ·
              refine ⟨11781730192655205497323093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15708973590206940663097457 11781730192655205497323093)
              ·
                refine ⟨138067150695178189421755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11781730192655205497323093 138067150695178189421755)
                ·
                  rfl

theorem cell22_3629945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 8].length) (baseStart_3629945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629945 prefixEnd_3629945 := by exact prefixLift 3629945
  have htrace : WordTrace (prefixWord ++ tailWord_3629945) baseStart_3629945 baseEnd_3629945 := by
    simpa [prefixWord, tailWord_3629945, baseEnd_3629945] using wordTrace_append hprefix tailTrace_3629945
  have hstable : (prefixWord ++ tailWord_3629945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629945).length < 2 ^ (prefixWord ++ tailWord_3629945).sum := by decide
  have hdescent : baseEnd_3629945 < baseStart_3629945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629975 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 1, 8]
def baseStart_3629975 : Nat := 118140960795 + 3629975 * 2 ^ 59
def prefixEnd_3629975 : Nat := 4983230072969 + 3 ^ 40 * 3629975 * 2
def baseEnd_3629975 : Nat := 1242614625869693626545703

theorem tailTrace_3629975 : CollatzResearch.WordTrace tailWord_3629975 prefixEnd_3629975 1242614625869693626545703 := by
  unfold tailWord_3629975
  simp only [CollatzResearch.WordTrace]
  refine ⟨132396065024228000218339379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88264043349485333478892919 132396065024228000218339379)
  ·
    refine ⟨198594097536342000327509069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132396065024228000218339379 198594097536342000327509069)
    ·
      refine ⟨74472786576128250122815901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198594097536342000327509069 74472786576128250122815901)
      ·
        refine ⟨27927294966048093796055963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74472786576128250122815901 27927294966048093796055963)
        ·
          refine ⟨41890942449072140694083945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27927294966048093796055963 41890942449072140694083945)
          ·
            refine ⟨31418206836804105520562959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41890942449072140694083945 31418206836804105520562959)
            ·
              refine ⟨47127310255206158280844439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31418206836804105520562959 47127310255206158280844439)
              ·
                refine ⟨70690965382809237421266659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47127310255206158280844439 70690965382809237421266659)
                ·
                  refine ⟨106036448074213856131899989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70690965382809237421266659 106036448074213856131899989)
                  ·
                    refine ⟨1242614625869693626545703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106036448074213856131899989 1242614625869693626545703)
                    ·
                      rfl

theorem cell22_3629975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_3629975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629975 prefixEnd_3629975 := by exact prefixLift 3629975
  have htrace : WordTrace (prefixWord ++ tailWord_3629975) baseStart_3629975 baseEnd_3629975 := by
    simpa [prefixWord, tailWord_3629975, baseEnd_3629975] using wordTrace_append hprefix tailTrace_3629975
  have hstable : (prefixWord ++ tailWord_3629975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629975).length < 2 ^ (prefixWord ++ tailWord_3629975).sum := by decide
  have hdescent : baseEnd_3629975 < baseStart_3629975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629977 : List Nat := [1, 2, 1, 2, 1, 3, 1, 5, 3, 3]
def baseStart_3629977 : Nat := 118140960795 + 3629977 * 2 ^ 59
def prefixEnd_3629977 : Nat := 4983230072969 + 3 ^ 40 * 3629977 * 2
def baseEnd_3629977 : Nat := 1242615310510566287995697

theorem tailTrace_3629977 : CollatzResearch.WordTrace tailWord_3629977 prefixEnd_3629977 1242615310510566287995697 := by
  unfold tailWord_3629977
  simp only [CollatzResearch.WordTrace]
  refine ⟨132396137970220754559912185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88264091980147169706608123 132396137970220754559912185)
  ·
    refine ⟨99297103477665565919934139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132396137970220754559912185 99297103477665565919934139)
    ·
      refine ⟨148945655216498348879901209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99297103477665565919934139 148945655216498348879901209)
      ·
        refine ⟨111709241412373761659925907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148945655216498348879901209 111709241412373761659925907)
        ·
          refine ⟨167563862118560642489888861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111709241412373761659925907 167563862118560642489888861)
          ·
            refine ⟨62836448294460240933708323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167563862118560642489888861 62836448294460240933708323)
            ·
              refine ⟨94254672441690361400562485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62836448294460240933708323 94254672441690361400562485)
              ·
                refine ⟨8836375541408471381302733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94254672441690361400562485 8836375541408471381302733)
                ·
                  refine ⟨3313640828028176767988525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8836375541408471381302733 3313640828028176767988525)
                  ·
                    refine ⟨1242615310510566287995697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3313640828028176767988525 1242615310510566287995697)
                    ·
                      rfl

theorem cell22_3629977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3, 3].length) (baseStart_3629977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3629977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3629977 prefixEnd_3629977 := by exact prefixLift 3629977
  have htrace : WordTrace (prefixWord ++ tailWord_3629977) baseStart_3629977 baseEnd_3629977 := by
    simpa [prefixWord, tailWord_3629977, baseEnd_3629977] using wordTrace_append hprefix tailTrace_3629977
  have hstable : (prefixWord ++ tailWord_3629977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629977).length < 2 ^ (prefixWord ++ tailWord_3629977).sum := by decide
  have hdescent : baseEnd_3629977 < baseStart_3629977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630101 : List Nat := [1, 3, 2, 1, 4, 2, 1, 3, 2, 3]
def baseStart_3630101 : Nat := 118140960795 + 3630101 * 2 ^ 59
def prefixEnd_3630101 : Nat := 4983230072969 + 3 ^ 40 * 3630101 * 2
def baseEnd_3630101 : Nat := 1242657758244671297895317

theorem tailTrace_3630101 : CollatzResearch.WordTrace tailWord_3630101 prefixEnd_3630101 1242657758244671297895317 := by
  unfold tailWord_3630101
  simp only [CollatzResearch.WordTrace]
  refine ⟨132400660621771523737426157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88267107081181015824950771 132400660621771523737426157)
  ·
    refine ⟨49650247733164321401534809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132400660621771523737426157 49650247733164321401534809)
    ·
      refine ⟨37237685799873241051151107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49650247733164321401534809 37237685799873241051151107)
      ·
        refine ⟨55856528699809861576726661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37237685799873241051151107 55856528699809861576726661)
        ·
          refine ⟨10473099131214349045636249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55856528699809861576726661 10473099131214349045636249)
          ·
            refine ⟨7854824348410761784227187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10473099131214349045636249 7854824348410761784227187)
            ·
              refine ⟨11782236522616142676340781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7854824348410761784227187 11782236522616142676340781)
              ·
                refine ⟨4418338695981053503627793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11782236522616142676340781 4418338695981053503627793)
                ·
                  refine ⟨3313754021985790127720845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4418338695981053503627793 3313754021985790127720845)
                  ·
                    refine ⟨1242657758244671297895317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3313754021985790127720845 1242657758244671297895317)
                    ·
                      rfl

theorem cell22_3630101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_3630101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630101 prefixEnd_3630101 := by exact prefixLift 3630101
  have htrace : WordTrace (prefixWord ++ tailWord_3630101) baseStart_3630101 baseEnd_3630101 := by
    simpa [prefixWord, tailWord_3630101, baseEnd_3630101] using wordTrace_append hprefix tailTrace_3630101
  have hstable : (prefixWord ++ tailWord_3630101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630101).length < 2 ^ (prefixWord ++ tailWord_3630101).sum := by decide
  have hdescent : baseEnd_3630101 < baseStart_3630101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630116 : List Nat := [2, 3, 1, 4, 1, 2, 2, 1, 2, 4]
def baseStart_3630116 : Nat := 118140960795 + 3630116 * 2 ^ 59
def prefixEnd_3630116 : Nat := 4983230072969 + 3 ^ 40 * 3630116 * 2
def baseEnd_3630116 : Nat := 1242662893051216258770271

theorem tailTrace_3630116 : CollatzResearch.WordTrace tailWord_3630116 prefixEnd_3630116 1242662893051216258770271 := by
  unfold tailWord_3630116
  simp only [CollatzResearch.WordTrace]
  refine ⟨66200603858358590649611101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88267471811144787532814801 66200603858358590649611101)
  ·
    refine ⟨24825226446884471493604163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66200603858358590649611101 24825226446884471493604163)
    ·
      refine ⟨37237839670326707240406245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24825226446884471493604163 37237839670326707240406245)
      ·
        refine ⟨6982094938186257607576171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37237839670326707240406245 6982094938186257607576171)
        ·
          refine ⟨10473142407279386411364257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6982094938186257607576171 10473142407279386411364257)
          ·
            refine ⟨7854856805459539808523193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10473142407279386411364257 7854856805459539808523193)
            ·
              refine ⟨5891142604094654856392395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7854856805459539808523193 5891142604094654856392395)
              ·
                refine ⟨8836713906141982284588593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5891142604094654856392395 8836713906141982284588593)
                ·
                  refine ⟨6627535429606486713441445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8836713906141982284588593 6627535429606486713441445)
                  ·
                    refine ⟨1242662893051216258770271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6627535429606486713441445 1242662893051216258770271)
                    ·
                      rfl

theorem cell22_3630116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_3630116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630116 prefixEnd_3630116 := by exact prefixLift 3630116
  have htrace : WordTrace (prefixWord ++ tailWord_3630116) baseStart_3630116 baseEnd_3630116 := by
    simpa [prefixWord, tailWord_3630116, baseEnd_3630116] using wordTrace_append hprefix tailTrace_3630116
  have hstable : (prefixWord ++ tailWord_3630116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630116).length < 2 ^ (prefixWord ++ tailWord_3630116).sum := by decide
  have hdescent : baseEnd_3630116 < baseStart_3630116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630202 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 1, 11]
def baseStart_3630202 : Nat := 118140960795 + 3630202 * 2 ^ 59
def prefixEnd_3630202 : Nat := 4983230072969 + 3 ^ 40 * 3630202 * 2
def baseEnd_3630202 : Nat := 1242692332608740701120007

theorem tailTrace_3630202 : CollatzResearch.WordTrace tailWord_3630202 prefixEnd_3630202 1242692332608740701120007 := by
  unfold tailWord_3630202
  simp only [CollatzResearch.WordTrace]
  refine ⟨33101086098601404496713215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88269562929603745324568573 33101086098601404496713215)
  ·
    refine ⟨49651629147902106745069823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33101086098601404496713215 49651629147902106745069823)
    ·
      refine ⟨74477443721853160117604735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49651629147902106745069823 74477443721853160117604735)
      ·
        refine ⟨111716165582779740176407103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74477443721853160117604735 111716165582779740176407103)
        ·
          refine ⟨167574248374169610264610655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111716165582779740176407103 167574248374169610264610655)
          ·
            refine ⟨251361372561254415396915983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167574248374169610264610655 251361372561254415396915983)
            ·
              refine ⟨377042058841881623095373975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251361372561254415396915983 377042058841881623095373975)
              ·
                refine ⟨565563088262822434643060963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377042058841881623095373975 565563088262822434643060963)
                ·
                  refine ⟨848344632394233651964591445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 565563088262822434643060963 848344632394233651964591445)
                  ·
                    refine ⟨1242692332608740701120007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 848344632394233651964591445 1242692332608740701120007)
                    ·
                      rfl

theorem cell22_3630202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_3630202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630202 prefixEnd_3630202 := by exact prefixLift 3630202
  have htrace : WordTrace (prefixWord ++ tailWord_3630202) baseStart_3630202 baseEnd_3630202 := by
    simpa [prefixWord, tailWord_3630202, baseEnd_3630202] using wordTrace_append hprefix tailTrace_3630202
  have hstable : (prefixWord ++ tailWord_3630202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630202).length < 2 ^ (prefixWord ++ tailWord_3630202).sum := by decide
  have hdescent : baseEnd_3630202 < baseStart_3630202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630204 : List Nat := [2, 2, 2, 1, 1, 3, 4, 1, 6]
def baseStart_3630204 : Nat := 118140960795 + 3630204 * 2 ^ 59
def prefixEnd_3630204 : Nat := 4983230072969 + 3 ^ 40 * 3630204 * 2
def baseEnd_3630204 : Nat := 414231005749871120856667

theorem tailTrace_3630204 : CollatzResearch.WordTrace tailWord_3630204 prefixEnd_3630204 414231005749871120856667 := by
  unfold tailWord_3630204
  simp only [CollatzResearch.WordTrace]
  refine ⟨66202208670199186164212833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88269611560265581552283777 66202208670199186164212833)
  ·
    refine ⟨49651656502649389623159625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66202208670199186164212833 49651656502649389623159625)
    ·
      refine ⟨37238742376987042217369719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49651656502649389623159625 37238742376987042217369719)
      ·
        refine ⟨55858113565480563326054579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37238742376987042217369719 55858113565480563326054579)
        ·
          refine ⟨83787170348220844989081869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55858113565480563326054579 83787170348220844989081869)
          ·
            refine ⟨31420188880582816870905701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83787170348220844989081869 31420188880582816870905701)
            ·
              refine ⟨5891285415109278163294819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31420188880582816870905701 5891285415109278163294819)
              ·
                refine ⟨8836928122663917244942229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5891285415109278163294819 8836928122663917244942229)
                ·
                  refine ⟨414231005749871120856667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8836928122663917244942229 414231005749871120856667)
                  ·
                    rfl

theorem cell22_3630204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 6].length) (baseStart_3630204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630204 prefixEnd_3630204 := by exact prefixLift 3630204
  have htrace : WordTrace (prefixWord ++ tailWord_3630204) baseStart_3630204 baseEnd_3630204 := by
    simpa [prefixWord, tailWord_3630204, baseEnd_3630204] using wordTrace_append hprefix tailTrace_3630204
  have hstable : (prefixWord ++ tailWord_3630204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630204).length < 2 ^ (prefixWord ++ tailWord_3630204).sum := by decide
  have hdescent : baseEnd_3630204 < baseStart_3630204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630236 : List Nat := [2, 2, 3, 2, 1, 2, 1, 2, 4, 3]
def baseStart_3630236 : Nat := 118140960795 + 3630236 * 2 ^ 59
def prefixEnd_3630236 : Nat := 4983230072969 + 3 ^ 40 * 3630236 * 2
def baseEnd_3630236 : Nat := 1242703971503575945769903

theorem tailTrace_3630236 : CollatzResearch.WordTrace tailWord_3630236 prefixEnd_3630236 1242703971503575945769903 := by
  unfold tailWord_3630236
  simp only [CollatzResearch.WordTrace]
  refine ⟨66202792238141220896795281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88270389650854961195727041 66202792238141220896795281)
  ·
    refine ⟨49652094178605915672596461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66202792238141220896795281 49652094178605915672596461)
    ·
      refine ⟨18619535316977218377223673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49652094178605915672596461 18619535316977218377223673)
      ·
        refine ⟨13964651487732913782917755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18619535316977218377223673 13964651487732913782917755)
        ·
          refine ⟨20946977231599370674376633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13964651487732913782917755 20946977231599370674376633)
          ·
            refine ⟨15710232923699528005782475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20946977231599370674376633 15710232923699528005782475)
            ·
              refine ⟨23565349385549292008673713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15710232923699528005782475 23565349385549292008673713)
              ·
                refine ⟨17674012039161969006505285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23565349385549292008673713 17674012039161969006505285)
                ·
                  refine ⟨3313877257342869188719741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17674012039161969006505285 3313877257342869188719741)
                  ·
                    refine ⟨1242703971503575945769903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3313877257342869188719741 1242703971503575945769903)
                    ·
                      rfl

theorem cell22_3630236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_3630236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630236 prefixEnd_3630236 := by exact prefixLift 3630236
  have htrace : WordTrace (prefixWord ++ tailWord_3630236) baseStart_3630236 baseEnd_3630236 := by
    simpa [prefixWord, tailWord_3630236, baseEnd_3630236] using wordTrace_append hprefix tailTrace_3630236
  have hstable : (prefixWord ++ tailWord_3630236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630236).length < 2 ^ (prefixWord ++ tailWord_3630236).sum := by decide
  have hdescent : baseEnd_3630236 < baseStart_3630236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630270 : List Nat := [4, 2, 1, 1, 3, 1, 4, 1, 2, 3]
def baseStart_3630270 : Nat := 118140960795 + 3630270 * 2 ^ 59
def prefixEnd_3630270 : Nat := 4983230072969 + 3 ^ 40 * 3630270 * 2
def baseEnd_3630270 : Nat := 1242715610398411190419799

theorem tailTrace_3630270 : CollatzResearch.WordTrace tailWord_3630270 prefixEnd_3630270 1242715610398411190419799 := by
  unfold tailWord_3630270
  simp only [CollatzResearch.WordTrace]
  refine ⟨16550853069769908200041033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88271216372106177066885509 16550853069769908200041033)
  ·
    refine ⟨12413139802327431150030775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16550853069769908200041033 12413139802327431150030775)
    ·
      refine ⟨18619709703491146725046163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12413139802327431150030775 18619709703491146725046163)
      ·
        refine ⟨27929564555236720087569245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18619709703491146725046163 27929564555236720087569245)
        ·
          refine ⟨10473586708213770032838467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27929564555236720087569245 10473586708213770032838467)
          ·
            refine ⟨15710380062320655049257701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10473586708213770032838467 15710380062320655049257701)
            ·
              refine ⟨2945696261685122821735819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15710380062320655049257701 2945696261685122821735819)
              ·
                refine ⟨4418544392527684232603729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2945696261685122821735819 4418544392527684232603729)
                ·
                  refine ⟨3313908294395763174452797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4418544392527684232603729 3313908294395763174452797)
                  ·
                    refine ⟨1242715610398411190419799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3313908294395763174452797 1242715610398411190419799)
                    ·
                      rfl

theorem cell22_3630270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_3630270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630270 prefixEnd_3630270 := by exact prefixLift 3630270
  have htrace : WordTrace (prefixWord ++ tailWord_3630270) baseStart_3630270 baseEnd_3630270 := by
    simpa [prefixWord, tailWord_3630270, baseEnd_3630270] using wordTrace_append hprefix tailTrace_3630270
  have hstable : (prefixWord ++ tailWord_3630270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630270).length < 2 ^ (prefixWord ++ tailWord_3630270).sum := by decide
  have hdescent : baseEnd_3630270 < baseStart_3630270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630274 : List Nat := [3, 5, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_3630274 : Nat := 118140960795 + 3630274 * 2 ^ 59
def prefixEnd_3630274 : Nat := 4983230072969 + 3 ^ 40 * 3630274 * 2
def baseEnd_3630274 : Nat := 1242716979680156513319787

theorem tailTrace_3630274 : CollatzResearch.WordTrace tailWord_3630274 prefixEnd_3630274 1242716979680156513319787 := by
  unfold tailWord_3630274
  simp only [CollatzResearch.WordTrace]
  refine ⟨33101742612536193570868469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88271313633429849522315917 33101742612536193570868469)
  ·
    refine ⟨3103288369925268147268919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33101742612536193570868469 3103288369925268147268919)
    ·
      refine ⟨4654932554887902220903379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3103288369925268147268919 4654932554887902220903379)
      ·
        refine ⟨6982398832331853331355069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4654932554887902220903379 6982398832331853331355069)
        ·
          refine ⟨2618399562124444999258151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6982398832331853331355069 2618399562124444999258151)
          ·
            refine ⟨3927599343186667498887227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2618399562124444999258151 3927599343186667498887227)
            ·
              refine ⟨5891399014780001248330841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3927599343186667498887227 5891399014780001248330841)
              ·
                refine ⟨4418549261085000936248131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5891399014780001248330841 4418549261085000936248131)
                ·
                  refine ⟨6627823891627501404372197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4418549261085000936248131 6627823891627501404372197)
                  ·
                    refine ⟨1242716979680156513319787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6627823891627501404372197 1242716979680156513319787)
                    ·
                      rfl

theorem cell22_3630274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_3630274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630274 prefixEnd_3630274 := by exact prefixLift 3630274
  have htrace : WordTrace (prefixWord ++ tailWord_3630274) baseStart_3630274 baseEnd_3630274 := by
    simpa [prefixWord, tailWord_3630274, baseEnd_3630274] using wordTrace_append hprefix tailTrace_3630274
  have hstable : (prefixWord ++ tailWord_3630274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630274).length < 2 ^ (prefixWord ++ tailWord_3630274).sum := by decide
  have hdescent : baseEnd_3630274 < baseStart_3630274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630298 : List Nat := [3, 1, 1, 2, 2, 1, 1, 7, 1, 3]
def baseStart_3630298 : Nat := 118140960795 + 3630298 * 2 ^ 59
def prefixEnd_3630298 : Nat := 4983230072969 + 3 ^ 40 * 3630298 * 2
def baseEnd_3630298 : Nat := 1242725195370628450719713

theorem tailTrace_3630298 : CollatzResearch.WordTrace tailWord_3630298 prefixEnd_3630298 1242725195370628450719713 := by
  unfold tailWord_3630298
  simp only [CollatzResearch.WordTrace]
  refine ⟨33101961450514456595586887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88271897201371884254898365 33101961450514456595586887)
  ·
    refine ⟨49652942175771684893380331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33101961450514456595586887 49652942175771684893380331)
    ·
      refine ⟨74479413263657527340070497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49652942175771684893380331 74479413263657527340070497)
      ·
        refine ⟨55859559947743145505052873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74479413263657527340070497 55859559947743145505052873)
        ·
          refine ⟨41894669960807359128789655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55859559947743145505052873 41894669960807359128789655)
          ·
            refine ⟨62842004941211038693184483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41894669960807359128789655 62842004941211038693184483)
            ·
              refine ⟨94263007411816558039776725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62842004941211038693184483 94263007411816558039776725)
              ·
                refine ⟨2209289236214450579057267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 94263007411816558039776725 2209289236214450579057267)
                ·
                  refine ⟨3313933854321675868585901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2209289236214450579057267 3313933854321675868585901)
                  ·
                    refine ⟨1242725195370628450719713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3313933854321675868585901 1242725195370628450719713)
                    ·
                      rfl

theorem cell22_3630298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7, 1, 3].length) (baseStart_3630298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630298 prefixEnd_3630298 := by exact prefixLift 3630298
  have htrace : WordTrace (prefixWord ++ tailWord_3630298) baseStart_3630298 baseEnd_3630298 := by
    simpa [prefixWord, tailWord_3630298, baseEnd_3630298] using wordTrace_append hprefix tailTrace_3630298
  have hstable : (prefixWord ++ tailWord_3630298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630298).length < 2 ^ (prefixWord ++ tailWord_3630298).sum := by decide
  have hdescent : baseEnd_3630298 < baseStart_3630298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630315 : List Nat := [1, 1, 1, 1, 2, 6, 4, 2, 1, 3]
def baseStart_3630315 : Nat := 118140960795 + 3630315 * 2 ^ 59
def prefixEnd_3630315 : Nat := 4983230072969 + 3 ^ 40 * 3630315 * 2
def baseEnd_3630315 : Nat := 1242731014818046073044661

theorem tailTrace_3630315 : CollatzResearch.WordTrace tailWord_3630315 prefixEnd_3630315 1242731014818046073044661 := by
  unfold tailWord_3630315
  simp only [CollatzResearch.WordTrace]
  refine ⟨132408465842996238285716399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88272310561997492190477599 132408465842996238285716399)
  ·
    refine ⟨198612698764494357428574599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132408465842996238285716399 198612698764494357428574599)
    ·
      refine ⟨297919048146741536142861899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198612698764494357428574599 297919048146741536142861899)
      ·
        refine ⟨446878572220112304214292849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297919048146741536142861899 446878572220112304214292849)
        ·
          refine ⟨335158929165084228160719637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446878572220112304214292849 335158929165084228160719637)
          ·
            refine ⟨15710574804613323195033733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 335158929165084228160719637 15710574804613323195033733)
            ·
              refine ⟨2945732775864998099068825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15710574804613323195033733 2945732775864998099068825)
              ·
                refine ⟨2209299581898748574301619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2945732775864998099068825 2209299581898748574301619)
                ·
                  refine ⟨3313949372848122861452429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2209299581898748574301619 3313949372848122861452429)
                  ·
                    refine ⟨1242731014818046073044661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3313949372848122861452429 1242731014818046073044661)
                    ·
                      rfl

theorem cell22_3630315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2, 1, 3].length) (baseStart_3630315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630315 prefixEnd_3630315 := by exact prefixLift 3630315
  have htrace : WordTrace (prefixWord ++ tailWord_3630315) baseStart_3630315 baseEnd_3630315 := by
    simpa [prefixWord, tailWord_3630315, baseEnd_3630315] using wordTrace_append hprefix tailTrace_3630315
  have hstable : (prefixWord ++ tailWord_3630315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630315).length < 2 ^ (prefixWord ++ tailWord_3630315).sum := by decide
  have hdescent : baseEnd_3630315 < baseStart_3630315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630339 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 8]
def baseStart_3630339 : Nat := 118140960795 + 3630339 * 2 ^ 59
def prefixEnd_3630339 : Nat := 4983230072969 + 3 ^ 40 * 3630339 * 2
def baseEnd_3630339 : Nat := 414246410169506003481529

theorem tailTrace_3630339 : CollatzResearch.WordTrace tailWord_3630339 prefixEnd_3630339 414246410169506003481529 := by
  unfold tailWord_3630339
  simp only [CollatzResearch.WordTrace]
  refine ⟨132409341194909290384590071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88272894129939526923060047 132409341194909290384590071)
  ·
    refine ⟨198614011792363935576885107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132409341194909290384590071 198614011792363935576885107)
    ·
      refine ⟨297921017688545903365327661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198614011792363935576885107 297921017688545903365327661)
      ·
        refine ⟨111720381633204713761997873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297921017688545903365327661 111720381633204713761997873)
        ·
          refine ⟨83790286224903535321498405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111720381633204713761997873 83790286224903535321498405)
          ·
            refine ⟨15710678667169412872780951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83790286224903535321498405 15710678667169412872780951)
            ·
              refine ⟨23566018000754119309171427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15710678667169412872780951 23566018000754119309171427)
              ·
                refine ⟨35349027001131178963757141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23566018000754119309171427 35349027001131178963757141)
                ·
                  refine ⟨414246410169506003481529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35349027001131178963757141 414246410169506003481529)
                  ·
                    rfl

theorem cell22_3630339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 8].length) (baseStart_3630339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630339 prefixEnd_3630339 := by exact prefixLift 3630339
  have htrace : WordTrace (prefixWord ++ tailWord_3630339) baseStart_3630339 baseEnd_3630339 := by
    simpa [prefixWord, tailWord_3630339, baseEnd_3630339] using wordTrace_append hprefix tailTrace_3630339
  have hstable : (prefixWord ++ tailWord_3630339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630339).length < 2 ^ (prefixWord ++ tailWord_3630339).sum := by decide
  have hdescent : baseEnd_3630339 < baseStart_3630339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630341 : List Nat := [1, 3, 1, 1, 2, 1, 4, 4, 1, 4]
def baseStart_3630341 : Nat := 118140960795 + 3630341 * 2 ^ 59
def prefixEnd_3630341 : Nat := 4983230072969 + 3 ^ 40 * 3630341 * 2
def baseEnd_3630341 : Nat := 1242739915149390671894581

theorem tailTrace_3630341 : CollatzResearch.WordTrace tailWord_3630341 prefixEnd_3630341 1242739915149390671894581 := by
  unfold tailWord_3630341
  simp only [CollatzResearch.WordTrace]
  refine ⟨132409414140902044726162877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88272942760601363150775251 132409414140902044726162877)
  ·
    refine ⟨49653530302838266772311079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132409414140902044726162877 49653530302838266772311079)
    ·
      refine ⟨74480295454257400158466619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49653530302838266772311079 74480295454257400158466619)
      ·
        refine ⟨111720443181386100237699929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74480295454257400158466619 111720443181386100237699929)
        ·
          refine ⟨83790332386039575178274947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111720443181386100237699929 83790332386039575178274947)
          ·
            refine ⟨125685498579059362767412421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83790332386039575178274947 125685498579059362767412421)
            ·
              refine ⟨23566030983573630518889829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125685498579059362767412421 23566030983573630518889829)
              ·
                refine ⟨4418630809420055722291843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23566030983573630518889829 4418630809420055722291843)
                ·
                  refine ⟨6627946214130083583437765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4418630809420055722291843 6627946214130083583437765)
                  ·
                    refine ⟨1242739915149390671894581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6627946214130083583437765 1242739915149390671894581)
                    ·
                      rfl

theorem cell22_3630341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_3630341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630341 prefixEnd_3630341 := by exact prefixLift 3630341
  have htrace : WordTrace (prefixWord ++ tailWord_3630341) baseStart_3630341 baseEnd_3630341 := by
    simpa [prefixWord, tailWord_3630341, baseEnd_3630341] using wordTrace_append hprefix tailTrace_3630341
  have hstable : (prefixWord ++ tailWord_3630341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630341).length < 2 ^ (prefixWord ++ tailWord_3630341).sum := by decide
  have hdescent : baseEnd_3630341 < baseStart_3630341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630373 : List Nat := [1, 3, 1, 2, 4, 1, 2, 4, 4]
def baseStart_3630373 : Nat := 118140960795 + 3630373 * 2 ^ 59
def prefixEnd_3630373 : Nat := 4983230072969 + 3 ^ 40 * 3630373 * 2
def baseEnd_3630373 : Nat := 414250289801117751698161

theorem tailTrace_3630373 : CollatzResearch.WordTrace tailWord_3630373 prefixEnd_3630373 414250289801117751698161 := by
  unfold tailWord_3630373
  simp only [CollatzResearch.WordTrace]
  refine ⟨132410581276786114191327773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88273720851190742794218515 132410581276786114191327773)
  ·
    refine ⟨49653967978794792821747915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132410581276786114191327773 49653967978794792821747915)
    ·
      refine ⟨74480951968192189232621873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49653967978794792821747915 74480951968192189232621873)
      ·
        refine ⟨55860713976144141924466405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74480951968192189232621873 55860713976144141924466405)
        ·
          refine ⟨10473883870527026610837451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55860713976144141924466405 10473883870527026610837451)
          ·
            refine ⟨15710825805790539916256177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10473883870527026610837451 15710825805790539916256177)
            ·
              refine ⟨11783119354342904937192133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15710825805790539916256177 11783119354342904937192133)
              ·
                refine ⟨2209334878939294675723525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11783119354342904937192133 2209334878939294675723525)
                ·
                  refine ⟨414250289801117751698161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2209334878939294675723525 414250289801117751698161)
                  ·
                    rfl

theorem cell22_3630373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4, 4].length) (baseStart_3630373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630373 prefixEnd_3630373 := by exact prefixLift 3630373
  have htrace : WordTrace (prefixWord ++ tailWord_3630373) baseStart_3630373 baseEnd_3630373 := by
    simpa [prefixWord, tailWord_3630373, baseEnd_3630373] using wordTrace_append hprefix tailTrace_3630373
  have hstable : (prefixWord ++ tailWord_3630373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630373).length < 2 ^ (prefixWord ++ tailWord_3630373).sum := by decide
  have hdescent : baseEnd_3630373 < baseStart_3630373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630384 : List Nat := [2, 1, 1, 1, 2, 2, 4, 9]
def baseStart_3630384 : Nat := 118140960795 + 3630384 * 2 ^ 59
def prefixEnd_3630384 : Nat := 4983230072969 + 3 ^ 40 * 3630384 * 2
def baseEnd_3630384 : Nat := 138083848325350321452161

theorem tailTrace_3630384 : CollatzResearch.WordTrace tailWord_3630384 prefixEnd_3630384 138083848325350321452161 := by
  unfold tailWord_3630384
  simp only [CollatzResearch.WordTrace]
  refine ⟨66205491239873131534989103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88273988319830842046652137 66205491239873131534989103)
  ·
    refine ⟨99308236859809697302483655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66205491239873131534989103 99308236859809697302483655)
    ·
      refine ⟨148962355289714545953725483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99308236859809697302483655 148962355289714545953725483)
      ·
        refine ⟨223443532934571818930588225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148962355289714545953725483 223443532934571818930588225)
        ·
          refine ⟨167582649700928864197941169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223443532934571818930588225 167582649700928864197941169)
          ·
            refine ⟨125686987275696648148455877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167582649700928864197941169 125686987275696648148455877)
            ·
              refine ⟨23566310114193121527835477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125686987275696648148455877 23566310114193121527835477)
              ·
                refine ⟨138083848325350321452161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23566310114193121527835477 138083848325350321452161)
                ·
                  rfl

theorem cell22_3630384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 9].length) (baseStart_3630384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630384 prefixEnd_3630384 := by exact prefixLift 3630384
  have htrace : WordTrace (prefixWord ++ tailWord_3630384) baseStart_3630384 baseEnd_3630384 := by
    simpa [prefixWord, tailWord_3630384, baseEnd_3630384] using wordTrace_append hprefix tailTrace_3630384
  have hstable : (prefixWord ++ tailWord_3630384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630384).length < 2 ^ (prefixWord ++ tailWord_3630384).sum := by decide
  have hdescent : baseEnd_3630384 < baseStart_3630384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630386 : List Nat := [3, 2, 1, 1, 4, 1, 1, 2, 1, 6]
def baseStart_3630386 : Nat := 118140960795 + 3630386 * 2 ^ 59
def prefixEnd_3630386 : Nat := 4983230072969 + 3 ^ 40 * 3630386 * 2
def baseEnd_3630386 : Nat := 1242755319569025554519443

theorem tailTrace_3630386 : CollatzResearch.WordTrace tailWord_3630386 prefixEnd_3630386 1242755319569025554519443 := by
  unfold tailWord_3630386
  simp only [CollatzResearch.WordTrace]
  refine ⟨33102763856434754352887753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88274036950492678274367341 33102763856434754352887753)
  ·
    refine ⟨24827072892326065764665815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33102763856434754352887753 24827072892326065764665815)
    ·
      refine ⟨37240609338489098646998723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24827072892326065764665815 37240609338489098646998723)
      ·
        refine ⟨55860914007733647970498085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37240609338489098646998723 55860914007733647970498085)
        ·
          refine ⟨10473921376450058994468391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55860914007733647970498085 10473921376450058994468391)
          ·
            refine ⟨15710882064675088491702587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10473921376450058994468391 15710882064675088491702587)
            ·
              refine ⟨23566323097012632737553881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15710882064675088491702587 23566323097012632737553881)
              ·
                refine ⟨17674742322759474553165411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23566323097012632737553881 17674742322759474553165411)
                ·
                  refine ⟨26512113484139211829748117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17674742322759474553165411 26512113484139211829748117)
                  ·
                    refine ⟨1242755319569025554519443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26512113484139211829748117 1242755319569025554519443)
                    ·
                      rfl

theorem cell22_3630386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_3630386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630386 prefixEnd_3630386 := by exact prefixLift 3630386
  have htrace : WordTrace (prefixWord ++ tailWord_3630386) baseStart_3630386 baseEnd_3630386 := by
    simpa [prefixWord, tailWord_3630386, baseEnd_3630386] using wordTrace_append hprefix tailTrace_3630386
  have hstable : (prefixWord ++ tailWord_3630386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630386).length < 2 ^ (prefixWord ++ tailWord_3630386).sum := by decide
  have hdescent : baseEnd_3630386 < baseStart_3630386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630439 : List Nat := [1, 1, 5, 1, 5, 1, 2, 1, 2, 3]
def baseStart_3630439 : Nat := 118140960795 + 3630439 * 2 ^ 59
def prefixEnd_3630439 : Nat := 4983230072969 + 3 ^ 40 * 3630439 * 2
def baseEnd_3630439 : Nat := 1242773462552151082944281

theorem tailTrace_3630439 : CollatzResearch.WordTrace tailWord_3630439 prefixEnd_3630439 1242773462552151082944281 := by
  unfold tailWord_3630439
  simp only [CollatzResearch.WordTrace]
  refine ⟨132412988494547007463230371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88275325663031338308820247 132412988494547007463230371)
  ·
    refine ⟨198619482741820511194845557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132412988494547007463230371 198619482741820511194845557)
    ·
      refine ⟨18620576507045672924516771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198619482741820511194845557 18620576507045672924516771)
      ·
        refine ⟨27930864760568509386775157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18620576507045672924516771 27930864760568509386775157)
        ·
          refine ⟨2618518571303297755010171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27930864760568509386775157 2618518571303297755010171)
          ·
            refine ⟨3927777856954946632515257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2618518571303297755010171 3927777856954946632515257)
            ·
              refine ⟨2945833392716209974386443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3927777856954946632515257 2945833392716209974386443)
              ·
                refine ⟨4418750089074314961579665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2945833392716209974386443 4418750089074314961579665)
                ·
                  refine ⟨3314062566805736221184749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4418750089074314961579665 3314062566805736221184749)
                  ·
                    refine ⟨1242773462552151082944281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3314062566805736221184749 1242773462552151082944281)
                    ·
                      rfl

theorem cell22_3630439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_3630439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630439 prefixEnd_3630439 := by exact prefixLift 3630439
  have htrace : WordTrace (prefixWord ++ tailWord_3630439) baseStart_3630439 baseEnd_3630439 := by
    simpa [prefixWord, tailWord_3630439, baseEnd_3630439] using wordTrace_append hprefix tailTrace_3630439
  have hstable : (prefixWord ++ tailWord_3630439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630439).length < 2 ^ (prefixWord ++ tailWord_3630439).sum := by decide
  have hdescent : baseEnd_3630439 < baseStart_3630439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630484 : List Nat := [2, 4, 2, 1, 2, 1, 4, 2, 1, 3]
def baseStart_3630484 : Nat := 118140960795 + 3630484 * 2 ^ 59
def prefixEnd_3630484 : Nat := 4983230072969 + 3 ^ 40 * 3630484 * 2
def baseEnd_3630484 : Nat := 1242788866971785965569143

theorem tailTrace_3630484 : CollatzResearch.WordTrace tailWord_3630484 prefixEnd_3630484 1242788866971785965569143 := by
  unfold tailWord_3630484
  simp only [CollatzResearch.WordTrace]
  refine ⟨66207314889691990074309253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88276419852922653432412337 66207314889691990074309253)
  ·
    refine ⟨12413871541817248138932985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66207314889691990074309253 12413871541817248138932985)
    ·
      refine ⟨9310403656362936104199739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12413871541817248138932985 9310403656362936104199739)
      ·
        refine ⟨13965605484544404156299609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9310403656362936104199739 13965605484544404156299609)
        ·
          refine ⟨10474204113408303117224707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13965605484544404156299609 10474204113408303117224707)
          ·
            refine ⟨15711306170112454675837061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10474204113408303117224707 15711306170112454675837061)
            ·
              refine ⟨2945869906896085251719449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15711306170112454675837061 2945869906896085251719449)
              ·
                refine ⟨2209402430172063938789587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2945869906896085251719449 2209402430172063938789587)
                ·
                  refine ⟨3314103645258095908184381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2209402430172063938789587 3314103645258095908184381)
                  ·
                    refine ⟨1242788866971785965569143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3314103645258095908184381 1242788866971785965569143)
                    ·
                      rfl

theorem cell22_3630484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_3630484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630484 prefixEnd_3630484 := by exact prefixLift 3630484
  have htrace : WordTrace (prefixWord ++ tailWord_3630484) baseStart_3630484 baseEnd_3630484 := by
    simpa [prefixWord, tailWord_3630484, baseEnd_3630484] using wordTrace_append hprefix tailTrace_3630484
  have hstable : (prefixWord ++ tailWord_3630484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630484).length < 2 ^ (prefixWord ++ tailWord_3630484).sum := by decide
  have hdescent : baseEnd_3630484 < baseStart_3630484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630493 : List Nat := [1, 4, 2, 1, 3, 1, 1, 2, 3, 4]
def baseStart_3630493 : Nat := 118140960795 + 3630493 * 2 ^ 59
def prefixEnd_3630493 : Nat := 4983230072969 + 3 ^ 40 * 3630493 * 2
def baseEnd_3630493 : Nat := 1242791947855712942094115

theorem tailTrace_3630493 : CollatzResearch.WordTrace tailWord_3630493 prefixEnd_3630493 1242791947855712942094115 := by
  unfold tailWord_3630493
  simp only [CollatzResearch.WordTrace]
  refine ⟨132414958036351374685696133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88276638690900916457130755 132414958036351374685696133)
  ·
    refine ⟨24827804631815882753568025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132414958036351374685696133 24827804631815882753568025)
    ·
      refine ⟨18620853473861912065176019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24827804631815882753568025 18620853473861912065176019)
      ·
        refine ⟨27931280210792868097764029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18620853473861912065176019 27931280210792868097764029)
        ·
          refine ⟨10474230079047325536661511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27931280210792868097764029 10474230079047325536661511)
          ·
            refine ⟨15711345118570988304992267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10474230079047325536661511 15711345118570988304992267)
            ·
              refine ⟨23567017677856482457488401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15711345118570988304992267 23567017677856482457488401)
              ·
                refine ⟨17675263258392361843116301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23567017677856482457488401 17675263258392361843116301)
                ·
                  refine ⟨6628223721897135691168613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17675263258392361843116301 6628223721897135691168613)
                  ·
                    refine ⟨1242791947855712942094115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6628223721897135691168613 1242791947855712942094115)
                    ·
                      rfl

theorem cell22_3630493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_3630493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630493 prefixEnd_3630493 := by exact prefixLift 3630493
  have htrace : WordTrace (prefixWord ++ tailWord_3630493) baseStart_3630493 baseEnd_3630493 := by
    simpa [prefixWord, tailWord_3630493, baseEnd_3630493] using wordTrace_append hprefix tailTrace_3630493
  have hstable : (prefixWord ++ tailWord_3630493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630493).length < 2 ^ (prefixWord ++ tailWord_3630493).sum := by decide
  have hdescent : baseEnd_3630493 < baseStart_3630493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630525 : List Nat := [1, 4, 1, 2, 2, 1, 4, 3, 4]
def baseStart_3630525 : Nat := 118140960795 + 3630525 * 2 ^ 59
def prefixEnd_3630525 : Nat := 4983230072969 + 3 ^ 40 * 3630525 * 2
def baseEnd_3630525 : Nat := 414267634036558508431339

theorem tailTrace_3630525 : CollatzResearch.WordTrace tailWord_3630525 prefixEnd_3630525 414267634036558508431339 := by
  unfold tailWord_3630525
  simp only [CollatzResearch.WordTrace]
  refine ⟨132416125172235444150861029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88277416781490296100574019 132416125172235444150861029)
  ·
    refine ⟨24828023469794145778286443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132416125172235444150861029 24828023469794145778286443)
    ·
      refine ⟨37242035204691218667429665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24828023469794145778286443 37242035204691218667429665)
      ·
        refine ⟨27931526403518414000572249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37242035204691218667429665 27931526403518414000572249)
        ·
          refine ⟨20948644802638810500429187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27931526403518414000572249 20948644802638810500429187)
          ·
            refine ⟨31422967203958215750643781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20948644802638810500429187 31422967203958215750643781)
            ·
              refine ⟨5891806350742165453245709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31422967203958215750643781 5891806350742165453245709)
              ·
                refine ⟨2209427381528312044967141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5891806350742165453245709 2209427381528312044967141)
                ·
                  refine ⟨414267634036558508431339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2209427381528312044967141 414267634036558508431339)
                  ·
                    rfl

theorem cell22_3630525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_3630525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630525 prefixEnd_3630525 := by exact prefixLift 3630525
  have htrace : WordTrace (prefixWord ++ tailWord_3630525) baseStart_3630525 baseEnd_3630525 := by
    simpa [prefixWord, tailWord_3630525, baseEnd_3630525] using wordTrace_append hprefix tailTrace_3630525
  have hstable : (prefixWord ++ tailWord_3630525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630525).length < 2 ^ (prefixWord ++ tailWord_3630525).sum := by decide
  have hdescent : baseEnd_3630525 < baseStart_3630525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630536 : List Nat := [2, 1, 3, 1, 3, 1, 11]
def baseStart_3630536 : Nat := 118140960795 + 3630536 * 2 ^ 59
def prefixEnd_3630536 : Nat := 4983230072969 + 3 ^ 40 * 3630536 * 2
def baseEnd_3630536 : Nat := 46029876579054635676629

theorem tailTrace_3630536 : CollatzResearch.WordTrace tailWord_3630536 prefixEnd_3630536 46029876579054635676629 := by
  unfold tailWord_3630536
  simp only [CollatzResearch.WordTrace]
  refine ⟨66208263187597796514755731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88277684250130395353007641 66208263187597796514755731)
  ·
    refine ⟨99312394781396694772133597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66208263187597796514755731 99312394781396694772133597)
    ·
      refine ⟨37242148043023760539550099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99312394781396694772133597 37242148043023760539550099)
      ·
        refine ⟨55863222064535640809325149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37242148043023760539550099 55863222064535640809325149)
        ·
          refine ⟨20948708274200865303496931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55863222064535640809325149 20948708274200865303496931)
          ·
            refine ⟨31423062411301297955245397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20948708274200865303496931 31423062411301297955245397)
            ·
              refine ⟨46029876579054635676629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 31423062411301297955245397 46029876579054635676629)
              ·
                rfl

theorem cell22_3630536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 11].length) (baseStart_3630536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630536 prefixEnd_3630536 := by exact prefixLift 3630536
  have htrace : WordTrace (prefixWord ++ tailWord_3630536) baseStart_3630536 baseEnd_3630536 := by
    simpa [prefixWord, tailWord_3630536, baseEnd_3630536] using wordTrace_append hprefix tailTrace_3630536
  have hstable : (prefixWord ++ tailWord_3630536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630536).length < 2 ^ (prefixWord ++ tailWord_3630536).sum := by decide
  have hdescent : baseEnd_3630536 < baseStart_3630536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630540 : List Nat := [2, 2, 1, 4, 2, 2, 1, 1, 4, 3]
def baseStart_3630540 : Nat := 118140960795 + 3630540 * 2 ^ 59
def prefixEnd_3630540 : Nat := 4983230072969 + 3 ^ 40 * 3630540 * 2
def baseEnd_3630540 : Nat := 1242808036916220486168971

theorem tailTrace_3630540 : CollatzResearch.WordTrace tailWord_3630540 prefixEnd_3630540 1242808036916220486168971 := by
  unfold tailWord_3630540
  simp only [CollatzResearch.WordTrace]
  refine ⟨66208336133590550856328537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88277781511454067808438049 66208336133590550856328537)
  ·
    refine ⟨49656252100192913142246403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66208336133590550856328537 49656252100192913142246403)
    ·
      refine ⟨74484378150289369713369605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49656252100192913142246403 74484378150289369713369605)
      ·
        refine ⟨13965820903179256821256801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74484378150289369713369605 13965820903179256821256801)
        ·
          refine ⟨10474365677384442615942601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13965820903179256821256801 10474365677384442615942601)
          ·
            refine ⟨7855774258038331961956951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10474365677384442615942601 7855774258038331961956951)
            ·
              refine ⟨11783661387057497942935427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7855774258038331961956951 11783661387057497942935427)
              ·
                refine ⟨17675492080586246914403141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11783661387057497942935427 17675492080586246914403141)
                ·
                  refine ⟨3314154765109921296450589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17675492080586246914403141 3314154765109921296450589)
                  ·
                    refine ⟨1242808036916220486168971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3314154765109921296450589 1242808036916220486168971)
                    ·
                      rfl

theorem cell22_3630540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 4, 3].length) (baseStart_3630540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630540 prefixEnd_3630540 := by exact prefixLift 3630540
  have htrace : WordTrace (prefixWord ++ tailWord_3630540) baseStart_3630540 baseEnd_3630540 := by
    simpa [prefixWord, tailWord_3630540, baseEnd_3630540] using wordTrace_append hprefix tailTrace_3630540
  have hstable : (prefixWord ++ tailWord_3630540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630540).length < 2 ^ (prefixWord ++ tailWord_3630540).sum := by decide
  have hdescent : baseEnd_3630540 < baseStart_3630540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630602 : List Nat := [3, 1, 2, 2, 2, 4, 1, 1, 3, 3]
def baseStart_3630602 : Nat := 118140960795 + 3630602 * 2 ^ 59
def prefixEnd_3630602 : Nat := 4983230072969 + 3 ^ 40 * 3630602 * 2
def baseEnd_3630602 : Nat := 1242829260783272991118781

theorem tailTrace_3630602 : CollatzResearch.WordTrace tailWord_3630602 prefixEnd_3630602 1242829260783272991118781 := by
  unfold tailWord_3630602
  simp only [CollatzResearch.WordTrace]
  refine ⟨33104733398239121575353515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88279289061970990867609373 33104733398239121575353515)
  ·
    refine ⟨49657100097358682363030273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33104733398239121575353515 49657100097358682363030273)
    ·
      refine ⟨37242825073019011772272705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49657100097358682363030273 37242825073019011772272705)
      ·
        refine ⟨27932118804764258829204529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37242825073019011772272705 27932118804764258829204529)
        ·
          refine ⟨20949089103573194121903397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27932118804764258829204529 20949089103573194121903397)
          ·
            refine ⟨3927954206919973897856887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20949089103573194121903397 3927954206919973897856887)
            ·
              refine ⟨5891931310379960846785331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3927954206919973897856887 5891931310379960846785331)
              ·
                refine ⟨8837896965569941270177997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5891931310379960846785331 8837896965569941270177997)
                ·
                  refine ⟨3314211362088727976316749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8837896965569941270177997 3314211362088727976316749)
                  ·
                    refine ⟨1242829260783272991118781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3314211362088727976316749 1242829260783272991118781)
                    ·
                      rfl

theorem cell22_3630602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_3630602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630602 prefixEnd_3630602 := by exact prefixLift 3630602
  have htrace : WordTrace (prefixWord ++ tailWord_3630602) baseStart_3630602 baseEnd_3630602 := by
    simpa [prefixWord, tailWord_3630602, baseEnd_3630602] using wordTrace_append hprefix tailTrace_3630602
  have hstable : (prefixWord ++ tailWord_3630602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630602).length < 2 ^ (prefixWord ++ tailWord_3630602).sum := by decide
  have hdescent : baseEnd_3630602 < baseStart_3630602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630653 : List Nat := [1, 4, 1, 3, 4, 1, 2, 2, 1, 3]
def baseStart_3630653 : Nat := 118140960795 + 3630653 * 2 ^ 59
def prefixEnd_3630653 : Nat := 4983230072969 + 3 ^ 40 * 3630653 * 2
def baseEnd_3630653 : Nat := 1242846719125525858093625

theorem tailTrace_3630653 : CollatzResearch.WordTrace tailWord_3630653 prefixEnd_3630653 1242846719125525858093625 := by
  unfold tailWord_3630653
  simp only [CollatzResearch.WordTrace]
  refine ⟨132420793715771722011520613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88280529143847814674347075 132420793715771722011520613)
  ·
    refine ⟨24828898821707197877160115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132420793715771722011520613 24828898821707197877160115)
    ·
      refine ⟨37243348232560796815740173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24828898821707197877160115 37243348232560796815740173)
      ·
        refine ⟨13966255587210298805902565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37243348232560796815740173 13966255587210298805902565)
        ·
          refine ⟨2618672922601931026106731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13966255587210298805902565 2618672922601931026106731)
          ·
            refine ⟨3928009383902896539160097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2618672922601931026106731 3928009383902896539160097)
            ·
              refine ⟨2946007037927172404370073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3928009383902896539160097 2946007037927172404370073)
              ·
                refine ⟨2209505278445379303277555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2946007037927172404370073 2209505278445379303277555)
                ·
                  refine ⟨3314257917668068954916333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2209505278445379303277555 3314257917668068954916333)
                  ·
                    refine ⟨1242846719125525858093625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3314257917668068954916333 1242846719125525858093625)
                    ·
                      rfl

theorem cell22_3630653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_3630653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630653 prefixEnd_3630653 := by exact prefixLift 3630653
  have htrace : WordTrace (prefixWord ++ tailWord_3630653) baseStart_3630653 baseEnd_3630653 := by
    simpa [prefixWord, tailWord_3630653, baseEnd_3630653] using wordTrace_append hprefix tailTrace_3630653
  have hstable : (prefixWord ++ tailWord_3630653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630653).length < 2 ^ (prefixWord ++ tailWord_3630653).sum := by decide
  have hdescent : baseEnd_3630653 < baseStart_3630653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630673 : List Nat := [1, 2, 2, 1, 3, 2, 2, 2, 1, 6]
def baseStart_3630673 : Nat := 118140960795 + 3630673 * 2 ^ 59
def prefixEnd_3630673 : Nat := 4983230072969 + 3 ^ 40 * 3630673 * 2
def baseEnd_3630673 : Nat := 1242853565534252472593563

theorem tailTrace_3630673 : CollatzResearch.WordTrace tailWord_3630673 prefixEnd_3630673 1242853565534252472593563 := by
  unfold tailWord_3630673
  simp only [CollatzResearch.WordTrace]
  refine ⟨132421523175699265427248673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88281015450466176951499115 132421523175699265427248673)
  ·
    refine ⟨99316142381774449070436505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132421523175699265427248673 99316142381774449070436505)
    ·
      refine ⟨74487106786330836802827379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99316142381774449070436505 74487106786330836802827379)
      ·
        refine ⟨111730660179496255204241069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74487106786330836802827379 111730660179496255204241069)
        ·
          refine ⟨41898997567311095701590401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111730660179496255204241069 41898997567311095701590401)
          ·
            refine ⟨31424248175483321776192801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41898997567311095701590401 31424248175483321776192801)
            ·
              refine ⟨23568186131612491332144601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31424248175483321776192801 23568186131612491332144601)
              ·
                refine ⟨17676139598709368499108451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23568186131612491332144601 17676139598709368499108451)
                ·
                  refine ⟨26514209398064052748662677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17676139598709368499108451 26514209398064052748662677)
                  ·
                    refine ⟨1242853565534252472593563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26514209398064052748662677 1242853565534252472593563)
                    ·
                      rfl

theorem cell22_3630673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_3630673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630673 prefixEnd_3630673 := by exact prefixLift 3630673
  have htrace : WordTrace (prefixWord ++ tailWord_3630673) baseStart_3630673 baseEnd_3630673 := by
    simpa [prefixWord, tailWord_3630673, baseEnd_3630673] using wordTrace_append hprefix tailTrace_3630673
  have hstable : (prefixWord ++ tailWord_3630673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630673).length < 2 ^ (prefixWord ++ tailWord_3630673).sum := by decide
  have hdescent : baseEnd_3630673 < baseStart_3630673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630709 : List Nat := [1, 3, 4, 2, 1, 1, 3, 2, 2, 3]
def baseStart_3630709 : Nat := 118140960795 + 3630709 * 2 ^ 59
def prefixEnd_3630709 : Nat := 4983230072969 + 3 ^ 40 * 3630709 * 2
def baseEnd_3630709 : Nat := 1242865889069960378693453

theorem tailTrace_3630709 : CollatzResearch.WordTrace tailWord_3630709 prefixEnd_3630709 1242865889069960378693453 := by
  unfold tailWord_3630709
  simp only [CollatzResearch.WordTrace]
  refine ⟨132422836203568843575559181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88281890802379229050372787 132422836203568843575559181)
  ·
    refine ⟨49658563576338316340834693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132422836203568843575559181 49658563576338316340834693)
    ·
      refine ⟨9310980670563434313906505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49658563576338316340834693 9310980670563434313906505)
      ·
        refine ⟨6983235502922575735429879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9310980670563434313906505 6983235502922575735429879)
        ·
          refine ⟨10474853254383863603144819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6983235502922575735429879 10474853254383863603144819)
          ·
            refine ⟨15712279881575795404717229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10474853254383863603144819 15712279881575795404717229)
            ·
              refine ⟨5892104955590923276768961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15712279881575795404717229 5892104955590923276768961)
              ·
                refine ⟨4419078716693192457576721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5892104955590923276768961 4419078716693192457576721)
                ·
                  refine ⟨3314309037519894343182541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4419078716693192457576721 3314309037519894343182541)
                  ·
                    refine ⟨1242865889069960378693453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3314309037519894343182541 1242865889069960378693453)
                    ·
                      rfl

theorem cell22_3630709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_3630709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630709 prefixEnd_3630709 := by exact prefixLift 3630709
  have htrace : WordTrace (prefixWord ++ tailWord_3630709) baseStart_3630709 baseEnd_3630709 := by
    simpa [prefixWord, tailWord_3630709, baseEnd_3630709] using wordTrace_append hprefix tailTrace_3630709
  have hstable : (prefixWord ++ tailWord_3630709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630709).length < 2 ^ (prefixWord ++ tailWord_3630709).sum := by decide
  have hdescent : baseEnd_3630709 < baseStart_3630709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630810 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 3, 5]
def baseStart_3630810 : Nat := 118140960795 + 3630810 * 2 ^ 59
def prefixEnd_3630810 : Nat := 4983230072969 + 3 ^ 40 * 3630810 * 2
def baseEnd_3630810 : Nat := 1242900463434029781918143

theorem tailTrace_3630810 : CollatzResearch.WordTrace tailWord_3630810 prefixEnd_3630810 1242900463434029781918143 := by
  unfold tailWord_3630810
  simp only [CollatzResearch.WordTrace]
  refine ⟨33106629994050734456246471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88284346650801958549990589 33106629994050734456246471)
  ·
    refine ⟨49659944991076101684369707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33106629994050734456246471 49659944991076101684369707)
    ·
      refine ⟨74489917486614152526554561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49659944991076101684369707 74489917486614152526554561)
      ·
        refine ⟨55867438114960614394915921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74489917486614152526554561 55867438114960614394915921)
        ·
          refine ⟨41900578586220460796186941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55867438114960614394915921 41900578586220460796186941)
          ·
            refine ⟨15712716969832672798570103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41900578586220460796186941 15712716969832672798570103)
            ·
              refine ⟨23569075454749009197855155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15712716969832672798570103 23569075454749009197855155)
              ·
                refine ⟨35353613182123513796782733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23569075454749009197855155 35353613182123513796782733)
                ·
                  refine ⟨13257604943296317673793525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35353613182123513796782733 13257604943296317673793525)
                  ·
                    refine ⟨1242900463434029781918143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13257604943296317673793525 1242900463434029781918143)
                    ·
                      rfl

theorem cell22_3630810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_3630810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630810 prefixEnd_3630810 := by exact prefixLift 3630810
  have htrace : WordTrace (prefixWord ++ tailWord_3630810) baseStart_3630810 baseEnd_3630810 := by
    simpa [prefixWord, tailWord_3630810, baseEnd_3630810] using wordTrace_append hprefix tailTrace_3630810
  have hstable : (prefixWord ++ tailWord_3630810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630810).length < 2 ^ (prefixWord ++ tailWord_3630810).sum := by decide
  have hdescent : baseEnd_3630810 < baseStart_3630810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630827 : List Nat := [1, 1, 1, 1, 2, 4, 3, 4, 2, 3]
def baseStart_3630827 : Nat := 118140960795 + 3630827 * 2 ^ 59
def prefixEnd_3630827 : Nat := 4983230072969 + 3 ^ 40 * 3630827 * 2
def baseEnd_3630827 : Nat := 1242906282881447404243091

theorem tailTrace_3630827 : CollatzResearch.WordTrace tailWord_3630827 prefixEnd_3630827 1242906282881447404243091 := by
  unfold tailWord_3630827
  simp only [CollatzResearch.WordTrace]
  refine ⟨132427140017141349728354735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88284760011427566485569823 132427140017141349728354735)
  ·
    refine ⟨198640710025712024592532103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132427140017141349728354735 198640710025712024592532103)
    ·
      refine ⟨297961065038568036888798155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198640710025712024592532103 297961065038568036888798155)
      ·
        refine ⟨446941597557852055333197233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297961065038568036888798155 446941597557852055333197233)
        ·
          refine ⟨335206198168389041499897925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446941597557852055333197233 335206198168389041499897925)
          ·
            refine ⟨62851162156572945281230861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 335206198168389041499897925 62851162156572945281230861)
            ·
              refine ⟨23569185808714854480461573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62851162156572945281230861 23569185808714854480461573)
              ·
                refine ⟨4419222339134035215086545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23569185808714854480461573 4419222339134035215086545)
                ·
                  refine ⟨3314416754350526411314909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4419222339134035215086545 3314416754350526411314909)
                  ·
                    refine ⟨1242906282881447404243091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3314416754350526411314909 1242906282881447404243091)
                    ·
                      rfl

theorem cell22_3630827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2, 3].length) (baseStart_3630827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630827 prefixEnd_3630827 := by exact prefixLift 3630827
  have htrace : WordTrace (prefixWord ++ tailWord_3630827) baseStart_3630827 baseEnd_3630827 := by
    simpa [prefixWord, tailWord_3630827, baseEnd_3630827] using wordTrace_append hprefix tailTrace_3630827
  have hstable : (prefixWord ++ tailWord_3630827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630827).length < 2 ^ (prefixWord ++ tailWord_3630827).sum := by decide
  have hdescent : baseEnd_3630827 < baseStart_3630827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630829 : List Nat := [1, 5, 1, 2, 1, 3, 1, 4, 4]
def baseStart_3630829 : Nat := 118140960795 + 3630829 * 2 ^ 59
def prefixEnd_3630829 : Nat := 4983230072969 + 3 ^ 40 * 3630829 * 2
def baseEnd_3630829 : Nat := 414302322507440021897695

theorem tailTrace_3630829 : CollatzResearch.WordTrace tailWord_3630829 prefixEnd_3630829 414302322507440021897695 := by
  unfold tailWord_3630829
  simp only [CollatzResearch.WordTrace]
  refine ⟨132427212963134104069927541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88284808642089402713285027 132427212963134104069927541)
  ·
    refine ⟨12415051215293822256555707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132427212963134104069927541 12415051215293822256555707)
    ·
      refine ⟨18622576822940733384833561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12415051215293822256555707 18622576822940733384833561)
      ·
        refine ⟨13966932617205550038625171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18622576822940733384833561 13966932617205550038625171)
        ·
          refine ⟨20950398925808325057937757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13966932617205550038625171 20950398925808325057937757)
          ·
            refine ⟨7856399597178121896726659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20950398925808325057937757 7856399597178121896726659)
            ·
              refine ⟨11784599395767182845089989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7856399597178121896726659 11784599395767182845089989)
              ·
                refine ⟨2209612386706346783454373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11784599395767182845089989 2209612386706346783454373)
                ·
                  refine ⟨414302322507440021897695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2209612386706346783454373 414302322507440021897695)
                  ·
                    rfl

theorem cell22_3630829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_3630829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630829 prefixEnd_3630829 := by exact prefixLift 3630829
  have htrace : WordTrace (prefixWord ++ tailWord_3630829) baseStart_3630829 baseEnd_3630829 := by
    simpa [prefixWord, tailWord_3630829, baseEnd_3630829] using wordTrace_append hprefix tailTrace_3630829
  have hstable : (prefixWord ++ tailWord_3630829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630829).length < 2 ^ (prefixWord ++ tailWord_3630829).sum := by decide
  have hdescent : baseEnd_3630829 < baseStart_3630829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630878 : List Nat := [4, 3, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_3630878 : Nat := 118140960795 + 3630878 * 2 ^ 59
def prefixEnd_3630878 : Nat := 4983230072969 + 3 ^ 40 * 3630878 * 2
def baseEnd_3630878 : Nat := 1242923741223700271217935

theorem tailTrace_3630878 : CollatzResearch.WordTrace tailWord_3630878 prefixEnd_3630878 1242923741223700271217935 := by
  unfold tailWord_3630878
  simp only [CollatzResearch.WordTrace]
  refine ⟨16553625017494573179807661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88286000093304390292307525 16553625017494573179807661)
  ·
    refine ⟨6207609381560464942427873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16553625017494573179807661 6207609381560464942427873)
    ·
      refine ⟨4655707036170348706820905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6207609381560464942427873 4655707036170348706820905)
      ·
        refine ⟨3491780277127761530115679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4655707036170348706820905 3491780277127761530115679)
        ·
          refine ⟨5237670415691642295173519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3491780277127761530115679 5237670415691642295173519)
          ·
            refine ⟨7856505623537463442760279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5237670415691642295173519 7856505623537463442760279)
            ·
              refine ⟨11784758435306195164140419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7856505623537463442760279 11784758435306195164140419)
              ·
                refine ⟨17677137652959292746210629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11784758435306195164140419 17677137652959292746210629)
                ·
                  refine ⟨3314463309929867389914493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17677137652959292746210629 3314463309929867389914493)
                  ·
                    refine ⟨1242923741223700271217935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3314463309929867389914493 1242923741223700271217935)
                    ·
                      rfl

theorem cell22_3630878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_3630878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630878 prefixEnd_3630878 := by exact prefixLift 3630878
  have htrace : WordTrace (prefixWord ++ tailWord_3630878) baseStart_3630878 baseEnd_3630878 := by
    simpa [prefixWord, tailWord_3630878, baseEnd_3630878] using wordTrace_append hprefix tailTrace_3630878
  have hstable : (prefixWord ++ tailWord_3630878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630878).length < 2 ^ (prefixWord ++ tailWord_3630878).sum := by decide
  have hdescent : baseEnd_3630878 < baseStart_3630878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630940 : List Nat := [2, 2, 4, 2, 2, 1, 3, 2, 1, 3]
def baseStart_3630940 : Nat := 118140960795 + 3630940 * 2 ^ 59
def prefixEnd_3630940 : Nat := 4983230072969 + 3 ^ 40 * 3630940 * 2
def baseEnd_3630940 : Nat := 1242944965090752776167745

theorem tailTrace_3630940 : CollatzResearch.WordTrace tailWord_3630940 prefixEnd_3630940 1242944965090752776167745 := by
  unfold tailWord_3630940
  simp only [CollatzResearch.WordTrace]
  refine ⟨66215630732865985013609137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88287507643821313351478849 66215630732865985013609137)
  ·
    refine ⟨49661723049649488760206853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66215630732865985013609137 49661723049649488760206853)
    ·
      refine ⟨9311573071809279142538785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49661723049649488760206853 9311573071809279142538785)
      ·
        refine ⟨6983679803856959356904089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9311573071809279142538785 6983679803856959356904089)
        ·
          refine ⟨5237759852892719517678067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6983679803856959356904089 5237759852892719517678067)
          ·
            refine ⟨7856639779339079276517101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5237759852892719517678067 7856639779339079276517101)
            ·
              refine ⟨2946239917252154728693913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7856639779339079276517101 2946239917252154728693913)
              ·
                refine ⟨2209679937939116046520435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2946239917252154728693913 2209679937939116046520435)
                ·
                  refine ⟨3314519906908674069780653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2209679937939116046520435 3314519906908674069780653)
                  ·
                    refine ⟨1242944965090752776167745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3314519906908674069780653 1242944965090752776167745)
                    ·
                      rfl

theorem cell22_3630940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_3630940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630940 prefixEnd_3630940 := by exact prefixLift 3630940
  have htrace : WordTrace (prefixWord ++ tailWord_3630940) baseStart_3630940 baseEnd_3630940 := by
    simpa [prefixWord, tailWord_3630940, baseEnd_3630940] using wordTrace_append hprefix tailTrace_3630940
  have hstable : (prefixWord ++ tailWord_3630940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630940).length < 2 ^ (prefixWord ++ tailWord_3630940).sum := by decide
  have hdescent : baseEnd_3630940 < baseStart_3630940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630962 : List Nat := [3, 2, 1, 2, 1, 1, 1, 5, 1, 5]
def baseStart_3630962 : Nat := 118140960795 + 3630962 * 2 ^ 59
def prefixEnd_3630962 : Nat := 4983230072969 + 3 ^ 40 * 3630962 * 2
def baseEnd_3630962 : Nat := 1242952496140352052117677

theorem tailTrace_3630962 : CollatzResearch.WordTrace tailWord_3630962 prefixEnd_3630962 1242952496140352052117677 := by
  unfold tailWord_3630962
  simp only [CollatzResearch.WordTrace]
  refine ⟨33108015967913066946129785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88288042581101511856346093 33108015967913066946129785)
  ·
    refine ⟨24831011975934800209597339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33108015967913066946129785 24831011975934800209597339)
    ·
      refine ⟨37246517963902200314396009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24831011975934800209597339 37246517963902200314396009)
      ·
        refine ⟨27934888472926650235797007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37246517963902200314396009 27934888472926650235797007)
        ·
          refine ⟨41902332709389975353695511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27934888472926650235797007 41902332709389975353695511)
          ·
            refine ⟨62853499064084963030543267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41902332709389975353695511 62853499064084963030543267)
            ·
              refine ⟨94280248596127444545814901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62853499064084963030543267 94280248596127444545814901)
              ·
                refine ⟨8838773305886947926170147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94280248596127444545814901 8838773305886947926170147)
                ·
                  refine ⟨13258159958830421889255221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8838773305886947926170147 13258159958830421889255221)
                  ·
                    refine ⟨1242952496140352052117677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13258159958830421889255221 1242952496140352052117677)
                    ·
                      rfl

theorem cell22_3630962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_3630962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630962 prefixEnd_3630962 := by exact prefixLift 3630962
  have htrace : WordTrace (prefixWord ++ tailWord_3630962) baseStart_3630962 baseEnd_3630962 := by
    simpa [prefixWord, tailWord_3630962, baseEnd_3630962] using wordTrace_append hprefix tailTrace_3630962
  have hstable : (prefixWord ++ tailWord_3630962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630962).length < 2 ^ (prefixWord ++ tailWord_3630962).sum := by decide
  have hdescent : baseEnd_3630962 < baseStart_3630962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630966 : List Nat := [5, 1, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_3630966 : Nat := 118140960795 + 3630966 * 2 ^ 59
def prefixEnd_3630966 : Nat := 4983230072969 + 3 ^ 40 * 3630966 * 2
def baseEnd_3630966 : Nat := 1242953865422097375017665

theorem tailTrace_3630966 : CollatzResearch.WordTrace tailWord_3630966 prefixEnd_3630966 1242953865422097375017665 := by
  unfold tailWord_3630966
  simp only [CollatzResearch.WordTrace]
  refine ⟨8277013110227361029229047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88288139842425184311776501 8277013110227361029229047)
  ·
    refine ⟨12415519665341041543843571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8277013110227361029229047 12415519665341041543843571)
    ·
      refine ⟨18623279498011562315765357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12415519665341041543843571 18623279498011562315765357)
      ·
        refine ⟨6983729811754335868412009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18623279498011562315765357 6983729811754335868412009)
        ·
          refine ⟨5237797358815751901309007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6983729811754335868412009 5237797358815751901309007)
          ·
            refine ⟨7856696038223627851963511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5237797358815751901309007 7856696038223627851963511)
            ·
              refine ⟨11785044057335441777945267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7856696038223627851963511 11785044057335441777945267)
              ·
                refine ⟨17677566086003162666917901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11785044057335441777945267 17677566086003162666917901)
                ·
                  refine ⟨6629087282251186000094213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17677566086003162666917901 6629087282251186000094213)
                  ·
                    refine ⟨1242953865422097375017665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6629087282251186000094213 1242953865422097375017665)
                    ·
                      rfl

theorem cell22_3630966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_3630966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630966 prefixEnd_3630966 := by exact prefixLift 3630966
  have htrace : WordTrace (prefixWord ++ tailWord_3630966) baseStart_3630966 baseEnd_3630966 := by
    simpa [prefixWord, tailWord_3630966, baseEnd_3630966] using wordTrace_append hprefix tailTrace_3630966
  have hstable : (prefixWord ++ tailWord_3630966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630966).length < 2 ^ (prefixWord ++ tailWord_3630966).sum := by decide
  have hdescent : baseEnd_3630966 < baseStart_3630966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630996 : List Nat := [2, 4, 2, 1, 1, 2, 1, 4, 2, 3]
def baseStart_3630996 : Nat := 118140960795 + 3630996 * 2 ^ 59
def prefixEnd_3630996 : Nat := 4983230072969 + 3 ^ 40 * 3630996 * 2
def baseEnd_3630996 : Nat := 1242964135035187296767573

theorem tailTrace_3630996 : CollatzResearch.WordTrace tailWord_3630996 prefixEnd_3630996 1242964135035187296767573 := by
  unfold tailWord_3630996
  simp only [CollatzResearch.WordTrace]
  refine ⟨66216651976764545795628421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88288869302352727727504561 66216651976764545795628421)
  ·
    refine ⟨12415622245643352336680329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66216651976764545795628421 12415622245643352336680329)
    ·
      refine ⟨9311716684232514252510247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12415622245643352336680329 9311716684232514252510247)
      ·
        refine ⟨13967575026348771378765371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9311716684232514252510247 13967575026348771378765371)
        ·
          refine ⟨20951362539523157068148057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13967575026348771378765371 20951362539523157068148057)
          ·
            refine ⟨15713521904642367801111043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20951362539523157068148057 15713521904642367801111043)
            ·
              refine ⟨23570282856963551701666565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15713521904642367801111043 23570282856963551701666565)
              ·
                refine ⟨4419428035680665944062481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23570282856963551701666565 4419428035680665944062481)
                ·
                  refine ⟨3314571026760499458046861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4419428035680665944062481 3314571026760499458046861)
                  ·
                    refine ⟨1242964135035187296767573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3314571026760499458046861 1242964135035187296767573)
                    ·
                      rfl

theorem cell22_3630996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_3630996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3630996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3630996 prefixEnd_3630996 := by exact prefixLift 3630996
  have htrace : WordTrace (prefixWord ++ tailWord_3630996) baseStart_3630996 baseEnd_3630996 := by
    simpa [prefixWord, tailWord_3630996, baseEnd_3630996] using wordTrace_append hprefix tailTrace_3630996
  have hstable : (prefixWord ++ tailWord_3630996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630996).length < 2 ^ (prefixWord ++ tailWord_3630996).sum := by decide
  have hdescent : baseEnd_3630996 < baseStart_3630996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631058 : List Nat := [3, 2, 2, 3, 2, 1, 2, 1, 3, 3]
def baseStart_3631058 : Nat := 118140960795 + 3631058 * 2 ^ 59
def prefixEnd_3631058 : Nat := 4983230072969 + 3 ^ 40 * 3631058 * 2
def baseEnd_3631058 : Nat := 1242985358902239801717383

theorem tailTrace_3631058 : CollatzResearch.WordTrace tailWord_3631058 prefixEnd_3631058 1242985358902239801717383 := by
  unfold tailWord_3631058
  simp only [CollatzResearch.WordTrace]
  refine ⟨33108891319826119045003457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88290376852869650786675885 33108891319826119045003457)
  ·
    refine ⟨24831668489869589283752593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33108891319826119045003457 24831668489869589283752593)
    ·
      refine ⟨18623751367402191962814445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24831668489869589283752593 18623751367402191962814445)
      ·
        refine ⟨6983906762775821986055417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18623751367402191962814445 6983906762775821986055417)
        ·
          refine ⟨5237930072081866489541563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6983906762775821986055417 5237930072081866489541563)
          ·
            refine ⟨7856895108122799734312345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5237930072081866489541563 7856895108122799734312345)
            ·
              refine ⟨5892671331092099800734259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7856895108122799734312345 5892671331092099800734259)
              ·
                refine ⟨8839006996638149701101389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5892671331092099800734259 8839006996638149701101389)
                ·
                  refine ⟨3314627623739306137913021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8839006996638149701101389 3314627623739306137913021)
                  ·
                    refine ⟨1242985358902239801717383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3314627623739306137913021 1242985358902239801717383)
                    ·
                      rfl

theorem cell22_3631058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_3631058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631058 prefixEnd_3631058 := by exact prefixLift 3631058
  have htrace : WordTrace (prefixWord ++ tailWord_3631058) baseStart_3631058 baseEnd_3631058 := by
    simpa [prefixWord, tailWord_3631058, baseEnd_3631058] using wordTrace_append hprefix tailTrace_3631058
  have hstable : (prefixWord ++ tailWord_3631058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631058).length < 2 ^ (prefixWord ++ tailWord_3631058).sum := by decide
  have hdescent : baseEnd_3631058 < baseStart_3631058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631071 : List Nat := [1, 1, 2, 3, 4, 2, 3, 1, 5]
def baseStart_3631071 : Nat := 118140960795 + 3631071 * 2 ^ 59
def prefixEnd_3631071 : Nat := 4983230072969 + 3 ^ 40 * 3631071 * 2
def baseEnd_3631071 : Nat := 414329936355970700380781

theorem tailTrace_3631071 : CollatzResearch.WordTrace tailWord_3631071 prefixEnd_3631071 414329936355970700380781 := by
  unfold tailWord_3631071
  simp only [CollatzResearch.WordTrace]
  refine ⟨132436039428257379400237067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88290692952171586266824711 132436039428257379400237067)
  ·
    refine ⟨198654059142386069100355601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132436039428257379400237067 198654059142386069100355601)
    ·
      refine ⟨148990544356789551825266701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198654059142386069100355601 148990544356789551825266701)
      ·
        refine ⟨55871454133796081934475013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148990544356789551825266701 55871454133796081934475013)
        ·
          refine ⟨10475897650086765362714065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55871454133796081934475013 10475897650086765362714065)
          ·
            refine ⟨7856923237565074022035549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10475897650086765362714065 7856923237565074022035549)
            ·
              refine ⟨2946346214086902758263331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7856923237565074022035549 2946346214086902758263331)
              ·
                refine ⟨4419519321130354137394997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2946346214086902758263331 4419519321130354137394997)
                ·
                  refine ⟨414329936355970700380781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4419519321130354137394997 414329936355970700380781)
                  ·
                    rfl

theorem cell22_3631071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 5].length) (baseStart_3631071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631071 prefixEnd_3631071 := by exact prefixLift 3631071
  have htrace : WordTrace (prefixWord ++ tailWord_3631071) baseStart_3631071 baseEnd_3631071 := by
    simpa [prefixWord, tailWord_3631071, baseEnd_3631071] using wordTrace_append hprefix tailTrace_3631071
  have hstable : (prefixWord ++ tailWord_3631071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631071).length < 2 ^ (prefixWord ++ tailWord_3631071).sum := by decide
  have hdescent : baseEnd_3631071 < baseStart_3631071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631146 : List Nat := [3, 1, 4, 1, 2, 1, 1, 3, 2, 4]
def baseStart_3631146 : Nat := 118140960795 + 3631146 * 2 ^ 59
def prefixEnd_3631146 : Nat := 4983230072969 + 3 ^ 40 * 3631146 * 2
def baseEnd_3631146 : Nat := 1243015483100636905517113

theorem tailTrace_3631146 : CollatzResearch.WordTrace tailWord_3631146 prefixEnd_3631146 1243015483100636905517113 := by
  unfold tailWord_3631146
  simp only [CollatzResearch.WordTrace]
  refine ⟨33109693725746416802304323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88292516601990444806144861 33109693725746416802304323)
  ·
    refine ⟨49664540588619625203456485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33109693725746416802304323 49664540588619625203456485)
    ·
      refine ⟨9312101360366179725648091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49664540588619625203456485 9312101360366179725648091)
      ·
        refine ⟨13968152040549269588472137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9312101360366179725648091 13968152040549269588472137)
        ·
          refine ⟨10476114030411952191354103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13968152040549269588472137 10476114030411952191354103)
          ·
            refine ⟨15714171045617928287031155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10476114030411952191354103 15714171045617928287031155)
            ·
              refine ⟨23571256568426892430546733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15714171045617928287031155 23571256568426892430546733)
              ·
                refine ⟨8839221213160084661455025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23571256568426892430546733 8839221213160084661455025)
                ·
                  refine ⟨6629415909870063496091269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8839221213160084661455025 6629415909870063496091269)
                  ·
                    refine ⟨1243015483100636905517113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6629415909870063496091269 1243015483100636905517113)
                    ·
                      rfl

theorem cell22_3631146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_3631146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631146 prefixEnd_3631146 := by exact prefixLift 3631146
  have htrace : WordTrace (prefixWord ++ tailWord_3631146) baseStart_3631146 baseEnd_3631146 := by
    simpa [prefixWord, tailWord_3631146, baseEnd_3631146] using wordTrace_append hprefix tailTrace_3631146
  have hstable : (prefixWord ++ tailWord_3631146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631146).length < 2 ^ (prefixWord ++ tailWord_3631146).sum := by decide
  have hdescent : baseEnd_3631146 < baseStart_3631146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631285 : List Nat := [1, 3, 3, 4, 1, 2, 1, 1, 6]
def baseStart_3631285 : Nat := 118140960795 + 3631285 * 2 ^ 59
def prefixEnd_3631285 : Nat := 4983230072969 + 3 ^ 40 * 3631285 * 2
def baseEnd_3631285 : Nat := 414354355213762292097229

theorem tailTrace_3631285 : CollatzResearch.WordTrace tailWord_3631285 prefixEnd_3631285 414354355213762292097229 := by
  unfold tailWord_3631285
  simp only [CollatzResearch.WordTrace]
  refine ⟨132443844649482093948527309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88295896432988062632351539 132443844649482093948527309)
  ·
    refine ⟨49666441743555785230697741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132443844649482093948527309 49666441743555785230697741)
    ·
      refine ⟨18624915653833419461511653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49666441743555785230697741 18624915653833419461511653)
      ·
        refine ⟨3492171685093766149033435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18624915653833419461511653 3492171685093766149033435)
        ·
          refine ⟨5238257527640649223550153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3492171685093766149033435 5238257527640649223550153)
          ·
            refine ⟨3928693145730486917662615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5238257527640649223550153 3928693145730486917662615)
            ·
              refine ⟨5893039718595730376493923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3928693145730486917662615 5893039718595730376493923)
              ·
                refine ⟨8839559577893595564740885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5893039718595730376493923 8839559577893595564740885)
                ·
                  refine ⟨414354355213762292097229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8839559577893595564740885 414354355213762292097229)
                  ·
                    rfl

theorem cell22_3631285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 6].length) (baseStart_3631285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631285 prefixEnd_3631285 := by exact prefixLift 3631285
  have htrace : WordTrace (prefixWord ++ tailWord_3631285) baseStart_3631285 baseEnd_3631285 := by
    simpa [prefixWord, tailWord_3631285, baseEnd_3631285] using wordTrace_append hprefix tailTrace_3631285
  have hstable : (prefixWord ++ tailWord_3631285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631285).length < 2 ^ (prefixWord ++ tailWord_3631285).sum := by decide
  have hdescent : baseEnd_3631285 < baseStart_3631285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631296 : List Nat := [2, 1, 1, 2, 5, 2, 2, 7]
def baseStart_3631296 : Nat := 118140960795 + 3631296 * 2 ^ 59
def prefixEnd_3631296 : Nat := 4983230072969 + 3 ^ 40 * 3631296 * 2
def baseEnd_3631296 : Nat := 138118536796231834918517

theorem tailTrace_3631296 : CollatzResearch.WordTrace tailWord_3631296 prefixEnd_3631296 138118536796231834918517 := by
  unfold tailWord_3631296
  simp only [CollatzResearch.WordTrace]
  refine ⟨66222122926221121413588871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88296163901628161884785161 66222122926221121413588871)
  ·
    refine ⟨99333184389331682120383307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66222122926221121413588871 99333184389331682120383307)
    ·
      refine ⟨148999776583997523180574961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99333184389331682120383307 148999776583997523180574961)
      ·
        refine ⟨111749832437998142385431221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148999776583997523180574961 111749832437998142385431221)
        ·
          refine ⟨10476546791062325848634177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111749832437998142385431221 10476546791062325848634177)
          ·
            refine ⟨7857410093296744386475633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10476546791062325848634177 7857410093296744386475633)
            ·
              refine ⟨5893057569972558289856725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7857410093296744386475633 5893057569972558289856725)
              ·
                refine ⟨138118536796231834918517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5893057569972558289856725 138118536796231834918517)
                ·
                  rfl

theorem cell22_3631296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 7].length) (baseStart_3631296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631296 prefixEnd_3631296 := by exact prefixLift 3631296
  have htrace : WordTrace (prefixWord ++ tailWord_3631296) baseStart_3631296 baseEnd_3631296 := by
    simpa [prefixWord, tailWord_3631296, baseEnd_3631296] using wordTrace_append hprefix tailTrace_3631296
  have hstable : (prefixWord ++ tailWord_3631296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631296).length < 2 ^ (prefixWord ++ tailWord_3631296).sum := by decide
  have hdescent : baseEnd_3631296 < baseStart_3631296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631300 : List Nat := [2, 3, 3, 1, 2, 2, 1, 3, 2, 3]
def baseStart_3631300 : Nat := 118140960795 + 3631300 * 2 ^ 59
def prefixEnd_3631300 : Nat := 4983230072969 + 3 ^ 40 * 3631300 * 2
def baseEnd_3631300 : Nat := 1243068200447831837166641

theorem tailTrace_3631300 : CollatzResearch.WordTrace tailWord_3631300 prefixEnd_3631300 1243068200447831837166641 := by
  unfold tailWord_3631300
  simp only [CollatzResearch.WordTrace]
  refine ⟨66222195872213875755161677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88296261162951834340215569 66222195872213875755161677)
  ·
    refine ⟨24833323452080203408185629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66222195872213875755161677 24833323452080203408185629)
    ·
      refine ⟨9312496294530076278069611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24833323452080203408185629 9312496294530076278069611)
      ·
        refine ⟨13968744441795114417104417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9312496294530076278069611 13968744441795114417104417)
        ·
          refine ⟨10476558331346335812828313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13968744441795114417104417 10476558331346335812828313)
          ·
            refine ⟨7857418748509751859621235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10476558331346335812828313 7857418748509751859621235)
            ·
              refine ⟨11786128122764627789431853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7857418748509751859621235 11786128122764627789431853)
              ·
                refine ⟨4419798046036735421036945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11786128122764627789431853 4419798046036735421036945)
                ·
                  refine ⟨3314848534527551565777709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4419798046036735421036945 3314848534527551565777709)
                  ·
                    refine ⟨1243068200447831837166641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3314848534527551565777709 1243068200447831837166641)
                    ·
                      rfl

theorem cell22_3631300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_3631300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631300 prefixEnd_3631300 := by exact prefixLift 3631300
  have htrace : WordTrace (prefixWord ++ tailWord_3631300) baseStart_3631300 baseEnd_3631300 := by
    simpa [prefixWord, tailWord_3631300, baseEnd_3631300] using wordTrace_append hprefix tailTrace_3631300
  have hstable : (prefixWord ++ tailWord_3631300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631300).length < 2 ^ (prefixWord ++ tailWord_3631300).sum := by decide
  have hdescent : baseEnd_3631300 < baseStart_3631300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631311 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 5, 3]
def baseStart_3631311 : Nat := 118140960795 + 3631311 * 2 ^ 59
def prefixEnd_3631311 : Nat := 4983230072969 + 3 ^ 40 * 3631311 * 2
def baseEnd_3631311 : Nat := 1243071965972631475141607

theorem tailTrace_3631311 : CollatzResearch.WordTrace tailWord_3631311 prefixEnd_3631311 1243071965972631475141607 := by
  unfold tailWord_3631311
  simp only [CollatzResearch.WordTrace]
  refine ⟨132444792947387900388973787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88296528631591933592649191 132444792947387900388973787)
  ·
    refine ⟨198667189421081850583460681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132444792947387900388973787 198667189421081850583460681)
    ·
      refine ⟨149000392065811387937595511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198667189421081850583460681 149000392065811387937595511)
      ·
        refine ⟨223500588098717081906393267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149000392065811387937595511 223500588098717081906393267)
        ·
          refine ⟨335250882148075622859589901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223500588098717081906393267 335250882148075622859589901)
          ·
            refine ⟨125719080805528358572346213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335250882148075622859589901 125719080805528358572346213)
            ·
              refine ⟨23572327651036567232314915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125719080805528358572346213 23572327651036567232314915)
              ·
                refine ⟨35358491476554850848472373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23572327651036567232314915 35358491476554850848472373)
                ·
                  refine ⟨3314858575927017267044285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35358491476554850848472373 3314858575927017267044285)
                  ·
                    refine ⟨1243071965972631475141607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3314858575927017267044285 1243071965972631475141607)
                    ·
                      rfl

theorem cell22_3631311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5, 3].length) (baseStart_3631311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631311 prefixEnd_3631311 := by exact prefixLift 3631311
  have htrace : WordTrace (prefixWord ++ tailWord_3631311) baseStart_3631311 baseEnd_3631311 := by
    simpa [prefixWord, tailWord_3631311, baseEnd_3631311] using wordTrace_append hprefix tailTrace_3631311
  have hstable : (prefixWord ++ tailWord_3631311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631311).length < 2 ^ (prefixWord ++ tailWord_3631311).sum := by decide
  have hdescent : baseEnd_3631311 < baseStart_3631311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631330 : List Nat := [3, 3, 4, 1, 1, 10]
def baseStart_3631330 : Nat := 118140960795 + 3631330 * 2 ^ 59
def prefixEnd_3631330 : Nat := 4983230072969 + 3 ^ 40 * 3631330 * 2
def baseEnd_3631330 : Nat := 15346647778529898258229

theorem tailTrace_3631330 : CollatzResearch.WordTrace tailWord_3631330 prefixEnd_3631330 15346647778529898258229 := by
  unfold tailWord_3631330
  simp only [CollatzResearch.WordTrace]
  refine ⟨33111371483579766658478861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88296990622879377755943629 33111371483579766658478861)
  ·
    refine ⟨12416764306342412496929573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33111371483579766658478861 12416764306342412496929573)
    ·
      refine ⟨2328143307439202343174295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12416764306342412496929573 2328143307439202343174295)
      ·
        refine ⟨3492214961158803514761443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2328143307439202343174295 3492214961158803514761443)
        ·
          refine ⟨5238322441738205272142165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3492214961158803514761443 5238322441738205272142165)
          ·
            refine ⟨15346647778529898258229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5238322441738205272142165 15346647778529898258229)
            ·
              rfl

theorem cell22_3631330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 10].length) (baseStart_3631330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631330 prefixEnd_3631330 := by exact prefixLift 3631330
  have htrace : WordTrace (prefixWord ++ tailWord_3631330) baseStart_3631330 baseEnd_3631330 := by
    simpa [prefixWord, tailWord_3631330, baseEnd_3631330] using wordTrace_append hprefix tailTrace_3631330
  have hstable : (prefixWord ++ tailWord_3631330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631330).length < 2 ^ (prefixWord ++ tailWord_3631330).sum := by decide
  have hdescent : baseEnd_3631330 < baseStart_3631330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631356 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 1, 7]
def baseStart_3631356 : Nat := 118140960795 + 3631356 * 2 ^ 59
def prefixEnd_3631356 : Nat := 4983230072969 + 3 ^ 40 * 3631356 * 2
def baseEnd_3631356 : Nat := 1243087370392266357766469

theorem tailTrace_3631356 : CollatzResearch.WordTrace tailWord_3631356 prefixEnd_3631356 1243087370392266357766469 := by
  unfold tailWord_3631356
  simp only [CollatzResearch.WordTrace]
  refine ⟨66223217116112436537180961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88297622821483248716241281 66223217116112436537180961)
  ·
    refine ⟨49667412837084327402885721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66223217116112436537180961 49667412837084327402885721)
    ·
      refine ⟨37250559627813245552164291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49667412837084327402885721 37250559627813245552164291)
      ·
        refine ⟨55875839441719868328246437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37250559627813245552164291 55875839441719868328246437)
        ·
          refine ⟨10476719895322475311546207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55875839441719868328246437 10476719895322475311546207)
          ·
            refine ⟨15715079842983712967319311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10476719895322475311546207 15715079842983712967319311)
            ·
              refine ⟨23572619764475569450978967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15715079842983712967319311 23572619764475569450978967)
              ·
                refine ⟨35358929646713354176468451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23572619764475569450978967 35358929646713354176468451)
                ·
                  refine ⟨53038394470070031264702677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35358929646713354176468451 53038394470070031264702677)
                  ·
                    refine ⟨1243087370392266357766469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53038394470070031264702677 1243087370392266357766469)
                    ·
                      rfl

theorem cell22_3631356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_3631356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631356 prefixEnd_3631356 := by exact prefixLift 3631356
  have htrace : WordTrace (prefixWord ++ tailWord_3631356) baseStart_3631356 baseEnd_3631356 := by
    simpa [prefixWord, tailWord_3631356, baseEnd_3631356] using wordTrace_append hprefix tailTrace_3631356
  have hstable : (prefixWord ++ tailWord_3631356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631356).length < 2 ^ (prefixWord ++ tailWord_3631356).sum := by decide
  have hdescent : baseEnd_3631356 < baseStart_3631356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631358 : List Nat := [4, 2, 2, 1, 1, 1, 1, 5, 5]
def baseStart_3631358 : Nat := 118140960795 + 3631358 * 2 ^ 59
def prefixEnd_3631358 : Nat := 4983230072969 + 3 ^ 40 * 3631358 * 2
def baseEnd_3631358 : Nat := 414362685011046339738821

theorem tailTrace_3631358 : CollatzResearch.WordTrace tailWord_3631358 prefixEnd_3631358 414362685011046339738821 := by
  unfold tailWord_3631358
  simp only [CollatzResearch.WordTrace]
  refine ⟨16555813397277203426991841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88297671452145084943956485 16555813397277203426991841)
  ·
    refine ⟨12416860047957902570243881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16555813397277203426991841 12416860047957902570243881)
    ·
      refine ⟨9312645035968426927682911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12416860047957902570243881 9312645035968426927682911)
      ·
        refine ⟨13968967553952640391524367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9312645035968426927682911 13968967553952640391524367)
        ·
          refine ⟨20953451330928960587286551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13968967553952640391524367 20953451330928960587286551)
          ·
            refine ⟨31430176996393440880929827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20953451330928960587286551 31430176996393440880929827)
            ·
              refine ⟨47145265494590161321394741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31430176996393440880929827 47145265494590161321394741)
              ·
                refine ⟨4419868640117827623880757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47145265494590161321394741 4419868640117827623880757)
                ·
                  refine ⟨414362685011046339738821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4419868640117827623880757 414362685011046339738821)
                  ·
                    rfl

theorem cell22_3631358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_3631358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631358 prefixEnd_3631358 := by exact prefixLift 3631358
  have htrace : WordTrace (prefixWord ++ tailWord_3631358) baseStart_3631358 baseEnd_3631358 := by
    simpa [prefixWord, tailWord_3631358, baseEnd_3631358] using wordTrace_append hprefix tailTrace_3631358
  have hstable : (prefixWord ++ tailWord_3631358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631358).length < 2 ^ (prefixWord ++ tailWord_3631358).sum := by decide
  have hdescent : baseEnd_3631358 < baseStart_3631358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631371 : List Nat := [1, 1, 1, 1, 5, 2, 1, 3, 3, 4]
def baseStart_3631371 : Nat := 118140960795 + 3631371 * 2 ^ 59
def prefixEnd_3631371 : Nat := 4983230072969 + 3 ^ 40 * 3631371 * 2
def baseEnd_3631371 : Nat := 1243092505198811318641423

theorem tailTrace_3631371 : CollatzResearch.WordTrace tailWord_3631371 prefixEnd_3631371 1243092505198811318641423 := by
  unfold tailWord_3631371
  simp only [CollatzResearch.WordTrace]
  refine ⟨132446981327170530636157967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88297987551447020424105311 132446981327170530636157967)
  ·
    refine ⟨198670471990755795954236951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132446981327170530636157967 198670471990755795954236951)
    ·
      refine ⟨298005707986133693931355427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198670471990755795954236951 298005707986133693931355427)
      ·
        refine ⟨447008561979200540897033141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298005707986133693931355427 447008561979200540897033141)
        ·
          refine ⟨41907052685550050709096857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 447008561979200540897033141 41907052685550050709096857)
          ·
            refine ⟨31430289514162538031822643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41907052685550050709096857 31430289514162538031822643)
            ·
              refine ⟨47145434271243807047733965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31430289514162538031822643 47145434271243807047733965)
              ·
                refine ⟨17679537851716427642900237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47145434271243807047733965 17679537851716427642900237)
                ·
                  refine ⟨6629826694393660366087589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17679537851716427642900237 6629826694393660366087589)
                  ·
                    refine ⟨1243092505198811318641423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6629826694393660366087589 1243092505198811318641423)
                    ·
                      rfl

theorem cell22_3631371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 4].length) (baseStart_3631371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631371 prefixEnd_3631371 := by exact prefixLift 3631371
  have htrace : WordTrace (prefixWord ++ tailWord_3631371) baseStart_3631371 baseEnd_3631371 := by
    simpa [prefixWord, tailWord_3631371, baseEnd_3631371] using wordTrace_append hprefix tailTrace_3631371
  have hstable : (prefixWord ++ tailWord_3631371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631371).length < 2 ^ (prefixWord ++ tailWord_3631371).sum := by decide
  have hdescent : baseEnd_3631371 < baseStart_3631371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631390 : List Nat := [4, 3, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_3631390 : Nat := 118140960795 + 3631390 * 2 ^ 59
def prefixEnd_3631390 : Nat := 4983230072969 + 3 ^ 40 * 3631390 * 2
def baseEnd_3631390 : Nat := 1243099009287101602416365

theorem tailTrace_3631390 : CollatzResearch.WordTrace tailWord_3631390 prefixEnd_3631390 1243099009287101602416365 := by
  unfold tailWord_3631390
  simp only [CollatzResearch.WordTrace]
  refine ⟨16555959289262712110137453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88298449542734464587399749 16555959289262712110137453)
  ·
    refine ⟨6208484733473517041301545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16555959289262712110137453 6208484733473517041301545)
    ·
      refine ⟨4656363550105137780976159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6208484733473517041301545 4656363550105137780976159)
      ·
        refine ⟨6984545325157706671464239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4656363550105137780976159 6984545325157706671464239)
        ·
          refine ⟨10476817987736560007196359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6984545325157706671464239 10476817987736560007196359)
          ·
            refine ⟨15715226981604840010794539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10476817987736560007196359 15715226981604840010794539)
            ·
              refine ⟨23572840472407260016191809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15715226981604840010794539 23572840472407260016191809)
              ·
                refine ⟨17679630354305445012143857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23572840472407260016191809 17679630354305445012143857)
                ·
                  refine ⟨13259722765729083759107893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17679630354305445012143857 13259722765729083759107893)
                  ·
                    refine ⟨1243099009287101602416365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13259722765729083759107893 1243099009287101602416365)
                    ·
                      rfl

theorem cell22_3631390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_3631390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631390 prefixEnd_3631390 := by exact prefixLift 3631390
  have htrace : WordTrace (prefixWord ++ tailWord_3631390) baseStart_3631390 baseEnd_3631390 := by
    simpa [prefixWord, tailWord_3631390, baseEnd_3631390] using wordTrace_append hprefix tailTrace_3631390
  have hstable : (prefixWord ++ tailWord_3631390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631390).length < 2 ^ (prefixWord ++ tailWord_3631390).sum := by decide
  have hdescent : baseEnd_3631390 < baseStart_3631390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631416 : List Nat := [2, 1, 2, 1, 3, 1, 3, 2, 1, 6]
def baseStart_3631416 : Nat := 118140960795 + 3631416 * 2 ^ 59
def prefixEnd_3631416 : Nat := 4983230072969 + 3 ^ 40 * 3631416 * 2
def baseEnd_3631416 : Nat := 1243107909618446201266285

theorem tailTrace_3631416 : CollatzResearch.WordTrace tailWord_3631416 prefixEnd_3631416 1243107909618446201266285 := by
  unfold tailWord_3631416
  simp only [CollatzResearch.WordTrace]
  refine ⟨66224311306003751660773051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88299081741338335547697401 66224311306003751660773051)
  ·
    refine ⟨99336466959005627491159577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66224311306003751660773051 99336466959005627491159577)
    ·
      refine ⟨74502350219254220618369683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99336466959005627491159577 74502350219254220618369683)
      ·
        refine ⟨111753525328881330927554525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74502350219254220618369683 111753525328881330927554525)
        ·
          refine ⟨41907571998330499097832947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111753525328881330927554525 41907571998330499097832947)
          ·
            refine ⟨62861357997495748646749421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41907571998330499097832947 62861357997495748646749421)
            ·
              refine ⟨23573009249060905742531033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62861357997495748646749421 23573009249060905742531033)
              ·
                refine ⟨17679756936795679306898275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23573009249060905742531033 17679756936795679306898275)
                ·
                  refine ⟨26519635405193518960347413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17679756936795679306898275 26519635405193518960347413)
                  ·
                    refine ⟨1243107909618446201266285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26519635405193518960347413 1243107909618446201266285)
                    ·
                      rfl

theorem cell22_3631416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_3631416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631416 prefixEnd_3631416 := by exact prefixLift 3631416
  have htrace : WordTrace (prefixWord ++ tailWord_3631416) baseStart_3631416 baseEnd_3631416 := by
    simpa [prefixWord, tailWord_3631416, baseEnd_3631416] using wordTrace_append hprefix tailTrace_3631416
  have hstable : (prefixWord ++ tailWord_3631416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631416).length < 2 ^ (prefixWord ++ tailWord_3631416).sum := by decide
  have hdescent : baseEnd_3631416 < baseStart_3631416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631418 : List Nat := [3, 1, 1, 1, 4, 2, 3, 1, 1, 5]
def baseStart_3631418 : Nat := 118140960795 + 3631418 * 2 ^ 59
def prefixEnd_3631418 : Nat := 4983230072969 + 3 ^ 40 * 3631418 * 2
def baseEnd_3631418 : Nat := 1243108594259318862716279

theorem tailTrace_3631418 : CollatzResearch.WordTrace tailWord_3631418 prefixEnd_3631418 1243108594259318862716279 := by
  unfold tailWord_3631418
  simp only [CollatzResearch.WordTrace]
  refine ⟨33112173889500064415779727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88299130372000171775412605 33112173889500064415779727)
  ·
    refine ⟨49668260834250096623669591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33112173889500064415779727 49668260834250096623669591)
    ·
      refine ⟨74502391251375144935504387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49668260834250096623669591 74502391251375144935504387)
      ·
        refine ⟨111753586877062717403256581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74502391251375144935504387 111753586877062717403256581)
        ·
          refine ⟨20953797539449259513110609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111753586877062717403256581 20953797539449259513110609)
          ·
            refine ⟨15715348154586944634832957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20953797539449259513110609 15715348154586944634832957)
            ·
              refine ⟨5893255557970104238062359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15715348154586944634832957 5893255557970104238062359)
              ·
                refine ⟨8839883336955156357093539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5893255557970104238062359 8839883336955156357093539)
                ·
                  refine ⟨13259825005432734535640309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8839883336955156357093539 13259825005432734535640309)
                  ·
                    refine ⟨1243108594259318862716279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13259825005432734535640309 1243108594259318862716279)
                    ·
                      rfl

theorem cell22_3631418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_3631418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631418 prefixEnd_3631418 := by exact prefixLift 3631418
  have htrace : WordTrace (prefixWord ++ tailWord_3631418) baseStart_3631418 baseEnd_3631418 := by
    simpa [prefixWord, tailWord_3631418, baseEnd_3631418] using wordTrace_append hprefix tailTrace_3631418
  have hstable : (prefixWord ++ tailWord_3631418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631418).length < 2 ^ (prefixWord ++ tailWord_3631418).sum := by decide
  have hdescent : baseEnd_3631418 < baseStart_3631418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631431 : List Nat := [1, 1, 4, 1, 2, 2, 3, 8]
def baseStart_3631431 : Nat := 118140960795 + 3631431 * 2 ^ 59
def prefixEnd_3631431 : Nat := 4983230072969 + 3 ^ 40 * 3631431 * 2
def baseEnd_3631431 : Nat := 138123671602776795793471

theorem tailTrace_3631431 : CollatzResearch.WordTrace tailWord_3631431 prefixEnd_3631431 138123671602776795793471 := by
  unfold tailWord_3631431
  simp only [CollatzResearch.WordTrace]
  refine ⟨132449169706953160883342147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88299446471302107255561431 132449169706953160883342147)
  ·
    refine ⟨198673754560429741325013221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132449169706953160883342147 198673754560429741325013221)
    ·
      refine ⟨37251328980080576498439979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198673754560429741325013221 37251328980080576498439979)
      ·
        refine ⟨55876993470120864747659969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37251328980080576498439979 55876993470120864747659969)
        ·
          refine ⟨41907745102590648560744977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55876993470120864747659969 41907745102590648560744977)
          ·
            refine ⟨31430808826942986420558733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41907745102590648560744977 31430808826942986420558733)
            ·
              refine ⟨11786553310103619907709525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31430808826942986420558733 11786553310103619907709525)
              ·
                refine ⟨138123671602776795793471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11786553310103619907709525 138123671602776795793471)
                ·
                  rfl

theorem cell22_3631431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 8].length) (baseStart_3631431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631431 prefixEnd_3631431 := by exact prefixLift 3631431
  have htrace : WordTrace (prefixWord ++ tailWord_3631431) baseStart_3631431 baseEnd_3631431 := by
    simpa [prefixWord, tailWord_3631431, baseEnd_3631431] using wordTrace_append hprefix tailTrace_3631431
  have hstable : (prefixWord ++ tailWord_3631431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631431).length < 2 ^ (prefixWord ++ tailWord_3631431).sum := by decide
  have hdescent : baseEnd_3631431 < baseStart_3631431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631514 : List Nat := [3, 1, 1, 4, 1, 2, 4, 2, 1, 3]
def baseStart_3631514 : Nat := 118140960795 + 3631514 * 2 ^ 59
def prefixEnd_3631514 : Nat := 4983230072969 + 3 ^ 40 * 3631514 * 2
def baseEnd_3631514 : Nat := 1243141457021206612315985

theorem tailTrace_3631514 : CollatzResearch.WordTrace tailWord_3631514 prefixEnd_3631514 1243141457021206612315985 := by
  unfold tailWord_3631514
  simp only [CollatzResearch.WordTrace]
  refine ⟨33113049241413116514653399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88301464643768310705742397 33113049241413116514653399)
  ·
    refine ⟨49669573862119674771980099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33113049241413116514653399 49669573862119674771980099)
    ·
      refine ⟨74504360793179512157970149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49669573862119674771980099 74504360793179512157970149)
      ·
        refine ⟨13969567648721158529619403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74504360793179512157970149 13969567648721158529619403)
        ·
          refine ⟨20954351473081737794429105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13969567648721158529619403 20954351473081737794429105)
          ·
            refine ⟨15715763604811303345821829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20954351473081737794429105 15715763604811303345821829)
            ·
              refine ⟨2946705675902119377341593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15715763604811303345821829 2946705675902119377341593)
              ·
                refine ⟨2210029256926589533006195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2946705675902119377341593 2210029256926589533006195)
                ·
                  refine ⟨3315043885389884299509293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2210029256926589533006195 3315043885389884299509293)
                  ·
                    refine ⟨1243141457021206612315985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3315043885389884299509293 1243141457021206612315985)
                    ·
                      rfl

theorem cell22_3631514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2, 1, 3].length) (baseStart_3631514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631514 prefixEnd_3631514 := by exact prefixLift 3631514
  have htrace : WordTrace (prefixWord ++ tailWord_3631514) baseStart_3631514 baseEnd_3631514 := by
    simpa [prefixWord, tailWord_3631514, baseEnd_3631514] using wordTrace_append hprefix tailTrace_3631514
  have hstable : (prefixWord ++ tailWord_3631514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631514).length < 2 ^ (prefixWord ++ tailWord_3631514).sum := by decide
  have hdescent : baseEnd_3631514 < baseStart_3631514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631523 : List Nat := [1, 1, 1, 4, 1, 4, 1, 2, 3, 4]
def baseStart_3631523 : Nat := 118140960795 + 3631523 * 2 ^ 59
def prefixEnd_3631523 : Nat := 4983230072969 + 3 ^ 40 * 3631523 * 2
def baseEnd_3631523 : Nat := 1243144537905133588840957

theorem tailTrace_3631523 : CollatzResearch.WordTrace tailWord_3631523 prefixEnd_3631523 1243144537905133588840957 := by
  unfold tailWord_3631523
  simp only [CollatzResearch.WordTrace]
  refine ⟨132452525222619860595691223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88301683481746573730460815 132452525222619860595691223)
  ·
    refine ⟨198678787833929790893536835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132452525222619860595691223 198678787833929790893536835)
    ·
      refine ⟨298018181750894686340305253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198678787833929790893536835 298018181750894686340305253)
      ·
        refine ⟨55878409078292753688807235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 298018181750894686340305253 55878409078292753688807235)
        ·
          refine ⟨83817613617439130533210853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55878409078292753688807235 83817613617439130533210853)
          ·
            refine ⟨15715802553269836974977035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83817613617439130533210853 15715802553269836974977035)
            ·
              refine ⟨23573703829904755462465553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15715802553269836974977035 23573703829904755462465553)
              ·
                refine ⟨17680277872428566596849165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23573703829904755462465553 17680277872428566596849165)
                ·
                  refine ⟨6630104202160712473818437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17680277872428566596849165 6630104202160712473818437)
                  ·
                    refine ⟨1243144537905133588840957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6630104202160712473818437 1243144537905133588840957)
                    ·
                      rfl

theorem cell22_3631523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 4].length) (baseStart_3631523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631523 prefixEnd_3631523 := by exact prefixLift 3631523
  have htrace : WordTrace (prefixWord ++ tailWord_3631523) baseStart_3631523 baseEnd_3631523 := by
    simpa [prefixWord, tailWord_3631523, baseEnd_3631523] using wordTrace_append hprefix tailTrace_3631523
  have hstable : (prefixWord ++ tailWord_3631523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631523).length < 2 ^ (prefixWord ++ tailWord_3631523).sum := by decide
  have hdescent : baseEnd_3631523 < baseStart_3631523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631538 : List Nat := [3, 2, 1, 1, 1, 1, 5, 2, 6]
def baseStart_3631538 : Nat := 118140960795 + 3631538 * 2 ^ 59
def prefixEnd_3631538 : Nat := 4983230072969 + 3 ^ 40 * 3631538 * 2
def baseEnd_3631538 : Nat := 414383224237226183238637

theorem tailTrace_3631538 : CollatzResearch.WordTrace tailWord_3631538 prefixEnd_3631538 414383224237226183238637 := by
  unfold tailWord_3631538
  simp only [CollatzResearch.WordTrace]
  refine ⟨33113268079391379539371817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88302048211710345438324845 33113268079391379539371817)
  ·
    refine ⟨24834951059543534654528863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33113268079391379539371817 24834951059543534654528863)
    ·
      refine ⟨37252426589315301981793295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24834951059543534654528863 37252426589315301981793295)
      ·
        refine ⟨55878639883972952972689943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37252426589315301981793295 55878639883972952972689943)
        ·
          refine ⟨83817959825959429459034915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55878639883972952972689943 83817959825959429459034915)
          ·
            refine ⟨125726939738939144188552373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83817959825959429459034915 125726939738939144188552373)
            ·
              refine ⟨11786900600525544767676785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125726939738939144188552373 11786900600525544767676785)
              ·
                refine ⟨8840175450394158575757589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11786900600525544767676785 8840175450394158575757589)
                ·
                  refine ⟨414383224237226183238637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8840175450394158575757589 414383224237226183238637)
                  ·
                    rfl

theorem cell22_3631538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_3631538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631538 prefixEnd_3631538 := by exact prefixLift 3631538
  have htrace : WordTrace (prefixWord ++ tailWord_3631538) baseStart_3631538 baseEnd_3631538 := by
    simpa [prefixWord, tailWord_3631538, baseEnd_3631538] using wordTrace_append hprefix tailTrace_3631538
  have hstable : (prefixWord ++ tailWord_3631538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631538).length < 2 ^ (prefixWord ++ tailWord_3631538).sum := by decide
  have hdescent : baseEnd_3631538 < baseStart_3631538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631572 : List Nat := [2, 4, 1, 2, 2, 1, 2, 4, 4]
def baseStart_3631572 : Nat := 118140960795 + 3631572 * 2 ^ 59
def prefixEnd_3631572 : Nat := 4983230072969 + 3 ^ 40 * 3631572 * 2
def baseEnd_3631572 : Nat := 414387103868837931455269

theorem tailTrace_3631572 : CollatzResearch.WordTrace tailWord_3631572 prefixEnd_3631572 414387103868837931455269 := by
  unfold tailWord_3631572
  simp only [CollatzResearch.WordTrace]
  refine ⟨66227156199721170982112485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88302874932961561309483313 66227156199721170982112485)
  ·
    refine ⟨12417591787447719559146091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66227156199721170982112485 12417591787447719559146091)
    ·
      refine ⟨18626387681171579338719137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12417591787447719559146091 18626387681171579338719137)
      ·
        refine ⟨13969790760878684504039353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18626387681171579338719137 13969790760878684504039353)
        ·
          refine ⟨10477343070659013378029515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13969790760878684504039353 10477343070659013378029515)
          ·
            refine ⟨15716014605988520067044273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10477343070659013378029515 15716014605988520067044273)
            ·
              refine ⟨11787010954491390050283205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15716014605988520067044273 11787010954491390050283205)
              ·
                refine ⟨2210064553967135634428101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11787010954491390050283205 2210064553967135634428101)
                ·
                  refine ⟨414387103868837931455269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2210064553967135634428101 414387103868837931455269)
                  ·
                    rfl

theorem cell22_3631572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_3631572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631572 prefixEnd_3631572 := by exact prefixLift 3631572
  have htrace : WordTrace (prefixWord ++ tailWord_3631572) baseStart_3631572 baseEnd_3631572 := by
    simpa [prefixWord, tailWord_3631572, baseEnd_3631572] using wordTrace_append hprefix tailTrace_3631572
  have hstable : (prefixWord ++ tailWord_3631572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631572).length < 2 ^ (prefixWord ++ tailWord_3631572).sum := by decide
  have hdescent : baseEnd_3631572 < baseStart_3631572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631587 : List Nat := [1, 1, 1, 6, 3, 2, 1, 1, 1, 5]
def baseStart_3631587 : Nat := 118140960795 + 3631587 * 2 ^ 59
def prefixEnd_3631587 : Nat := 4983230072969 + 3 ^ 40 * 3631587 * 2
def baseEnd_3631587 : Nat := 1243166446413058755240761

theorem tailTrace_3631587 : CollatzResearch.WordTrace tailWord_3631587 prefixEnd_3631587 1243166446413058755240761 := by
  unfold tailWord_3631587
  simp only [CollatzResearch.WordTrace]
  refine ⟨132454859494387999526021015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88303239662925333017347343 132454859494387999526021015)
  ·
    refine ⟨198682289241581999289031523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132454859494387999526021015 198682289241581999289031523)
    ·
      refine ⟨298023433862372998933547285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198682289241581999289031523 298023433862372998933547285)
      ·
        refine ⟨13969848462298734325010029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 298023433862372998933547285 13969848462298734325010029)
        ·
          refine ⟨5238693173362025371878761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13969848462298734325010029 5238693173362025371878761)
          ·
            refine ⟨3929019880021519028909071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5238693173362025371878761 3929019880021519028909071)
            ·
              refine ⟨5893529820032278543363607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3929019880021519028909071 5893529820032278543363607)
              ·
                refine ⟨8840294730048417815045411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5893529820032278543363607 8840294730048417815045411)
                ·
                  refine ⟨13260442095072626722568117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8840294730048417815045411 13260442095072626722568117)
                  ·
                    refine ⟨1243166446413058755240761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13260442095072626722568117 1243166446413058755240761)
                    ·
                      rfl

theorem cell22_3631587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 5].length) (baseStart_3631587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631587 prefixEnd_3631587 := by exact prefixLift 3631587
  have htrace : WordTrace (prefixWord ++ tailWord_3631587) baseStart_3631587 baseEnd_3631587 := by
    simpa [prefixWord, tailWord_3631587, baseEnd_3631587] using wordTrace_append hprefix tailTrace_3631587
  have hstable : (prefixWord ++ tailWord_3631587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631587).length < 2 ^ (prefixWord ++ tailWord_3631587).sum := by decide
  have hdescent : baseEnd_3631587 < baseStart_3631587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631705 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 8, 3]
def baseStart_3631705 : Nat := 118140960795 + 3631705 * 2 ^ 59
def prefixEnd_3631705 : Nat := 4983230072969 + 3 ^ 40 * 3631705 * 2
def baseEnd_3631705 : Nat := 1243206840224545780790399

theorem tailTrace_3631705 : CollatzResearch.WordTrace tailWord_3631705 prefixEnd_3631705 1243206840224545780790399 := by
  unfold tailWord_3631705
  simp only [CollatzResearch.WordTrace]
  refine ⟨132459163307960505678816569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88306108871973670452544379 132459163307960505678816569)
  ·
    refine ⟨99344372480970379259112427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132459163307960505678816569 99344372480970379259112427)
    ·
      refine ⟨149016558721455568888668641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99344372480970379259112427 149016558721455568888668641)
      ·
        refine ⟨111762419041091676666501481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149016558721455568888668641 111762419041091676666501481)
        ·
          refine ⟨83821814280818757499876111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111762419041091676666501481 83821814280818757499876111)
          ·
            refine ⟨125732721421228136249814167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83821814280818757499876111 125732721421228136249814167)
            ·
              refine ⟨188599082131842204374721251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125732721421228136249814167 188599082131842204374721251)
              ·
                refine ⟨282898623197763306562081877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188599082131842204374721251 282898623197763306562081877)
                ·
                  refine ⟨3315218240598788748774397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 282898623197763306562081877 3315218240598788748774397)
                  ·
                    refine ⟨1243206840224545780790399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3315218240598788748774397 1243206840224545780790399)
                    ·
                      rfl

theorem cell22_3631705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8, 3].length) (baseStart_3631705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631705 prefixEnd_3631705 := by exact prefixLift 3631705
  have htrace : WordTrace (prefixWord ++ tailWord_3631705) baseStart_3631705 baseEnd_3631705 := by
    simpa [prefixWord, tailWord_3631705, baseEnd_3631705] using wordTrace_append hprefix tailTrace_3631705
  have hstable : (prefixWord ++ tailWord_3631705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631705).length < 2 ^ (prefixWord ++ tailWord_3631705).sum := by decide
  have hdescent : baseEnd_3631705 < baseStart_3631705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631722 : List Nat := [3, 1, 3, 2, 1, 1, 2, 2, 4, 3]
def baseStart_3631722 : Nat := 118140960795 + 3631722 * 2 ^ 59
def prefixEnd_3631722 : Nat := 4983230072969 + 3 ^ 40 * 3631722 * 2
def baseEnd_3631722 : Nat := 1243212659671963403115347

theorem tailTrace_3631722 : CollatzResearch.WordTrace tailWord_3631722 prefixEnd_3631722 1243212659671963403115347 := by
  unfold tailWord_3631722
  simp only [CollatzResearch.WordTrace]
  refine ⟨33114945837224729395546355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88306522232599278388123613 33114945837224729395546355)
  ·
    refine ⟨49672418755837094093319533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33114945837224729395546355 49672418755837094093319533)
    ·
      refine ⟨18627157033438910284994825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49672418755837094093319533 18627157033438910284994825)
      ·
        refine ⟨13970367775079182713746119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18627157033438910284994825 13970367775079182713746119)
        ·
          refine ⟨20955551662618774070619179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13970367775079182713746119 20955551662618774070619179)
          ·
            refine ⟨31433327493928161105928769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20955551662618774070619179 31433327493928161105928769)
            ·
              refine ⟨23574995620446120829446577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31433327493928161105928769 23574995620446120829446577)
              ·
                refine ⟨17681246715334590622084933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23574995620446120829446577 17681246715334590622084933)
                ·
                  refine ⟨3315233759125235741640925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17681246715334590622084933 3315233759125235741640925)
                  ·
                    refine ⟨1243212659671963403115347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3315233759125235741640925 1243212659671963403115347)
                    ·
                      rfl

theorem cell22_3631722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_3631722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631722 prefixEnd_3631722 := by exact prefixLift 3631722
  have htrace : WordTrace (prefixWord ++ tailWord_3631722) baseStart_3631722 baseEnd_3631722 := by
    simpa [prefixWord, tailWord_3631722, baseEnd_3631722] using wordTrace_append hprefix tailTrace_3631722
  have hstable : (prefixWord ++ tailWord_3631722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631722).length < 2 ^ (prefixWord ++ tailWord_3631722).sum := by decide
  have hdescent : baseEnd_3631722 < baseStart_3631722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631726 : List Nat := [4, 1, 2, 2, 2, 3, 2, 1, 1, 4]
def baseStart_3631726 : Nat := 118140960795 + 3631726 * 2 ^ 59
def prefixEnd_3631726 : Nat := 4983230072969 + 3 ^ 40 * 3631726 * 2
def baseEnd_3631726 : Nat := 1243214028953708726015335

theorem tailTrace_3631726 : CollatzResearch.WordTrace tailWord_3631726 prefixEnd_3631726 1243214028953708726015335 := by
  unfold tailWord_3631726
  simp only [CollatzResearch.WordTrace]
  refine ⟨16557491155110553283166379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88306619493922950843554021 16557491155110553283166379)
  ·
    refine ⟨24836236732665829924749569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16557491155110553283166379 24836236732665829924749569)
    ·
      refine ⟨18627177549499372443562177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24836236732665829924749569 18627177549499372443562177)
      ·
        refine ⟨13970383162124529332671633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18627177549499372443562177 13970383162124529332671633)
        ·
          refine ⟨10477787371593396999503725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13970383162124529332671633 10477787371593396999503725)
          ·
            refine ⟨3929170264347523874813897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10477787371593396999503725 3929170264347523874813897)
            ·
              refine ⟨2946877698260642906110423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3929170264347523874813897 2946877698260642906110423)
              ·
                refine ⟨4420316547390964359165635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2946877698260642906110423 4420316547390964359165635)
                ·
                  refine ⟨6630474821086446538748453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4420316547390964359165635 6630474821086446538748453)
                  ·
                    refine ⟨1243214028953708726015335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6630474821086446538748453 1243214028953708726015335)
                    ·
                      rfl

theorem cell22_3631726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_3631726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631726 prefixEnd_3631726 := by exact prefixLift 3631726
  have htrace : WordTrace (prefixWord ++ tailWord_3631726) baseStart_3631726 baseEnd_3631726 := by
    simpa [prefixWord, tailWord_3631726, baseEnd_3631726] using wordTrace_append hprefix tailTrace_3631726
  have hstable : (prefixWord ++ tailWord_3631726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631726).length < 2 ^ (prefixWord ++ tailWord_3631726).sum := by decide
  have hdescent : baseEnd_3631726 < baseStart_3631726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631767 : List Nat := [1, 1, 3, 3, 2, 1, 1, 4, 3, 3]
def baseStart_3631767 : Nat := 118140960795 + 3631767 * 2 ^ 59
def prefixEnd_3631767 : Nat := 4983230072969 + 3 ^ 40 * 3631767 * 2
def baseEnd_3631767 : Nat := 1243228064091598285740209

theorem tailTrace_3631767 : CollatzResearch.WordTrace tailWord_3631767 prefixEnd_3631767 1243228064091598285740209 := by
  unfold tailWord_3631767
  simp only [CollatzResearch.WordTrace]
  refine ⟨132461424633735890267573555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88307616422490593511715703 132461424633735890267573555)
  ·
    refine ⟨198692136950603835401360333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132461424633735890267573555 198692136950603835401360333)
    ·
      refine ⟨74509551356476438275510125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198692136950603835401360333 74509551356476438275510125)
      ·
        refine ⟨27941081758678664353316297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74509551356476438275510125 27941081758678664353316297)
        ·
          refine ⟨20955811319008998264987223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27941081758678664353316297 20955811319008998264987223)
          ·
            refine ⟨31433716978513497397480835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20955811319008998264987223 31433716978513497397480835)
            ·
              refine ⟨47150575467770246096221253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31433716978513497397480835 47150575467770246096221253)
              ·
                refine ⟨8840732900206921143041485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47150575467770246096221253 8840732900206921143041485)
                ·
                  refine ⟨3315274837577595428640557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8840732900206921143041485 3315274837577595428640557)
                  ·
                    refine ⟨1243228064091598285740209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3315274837577595428640557 1243228064091598285740209)
                    ·
                      rfl

theorem cell22_3631767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3, 3].length) (baseStart_3631767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631767 prefixEnd_3631767 := by exact prefixLift 3631767
  have htrace : WordTrace (prefixWord ++ tailWord_3631767) baseStart_3631767 baseEnd_3631767 := by
    simpa [prefixWord, tailWord_3631767, baseEnd_3631767] using wordTrace_append hprefix tailTrace_3631767
  have hstable : (prefixWord ++ tailWord_3631767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631767).length < 2 ^ (prefixWord ++ tailWord_3631767).sum := by decide
  have hdescent : baseEnd_3631767 < baseStart_3631767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631780 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 9]
def baseStart_3631780 : Nat := 118140960795 + 3631780 * 2 ^ 59
def prefixEnd_3631780 : Nat := 4983230072969 + 3 ^ 40 * 3631780 * 2
def baseEnd_3631780 : Nat := 414410838085756861721723

theorem tailTrace_3631780 : CollatzResearch.WordTrace tailWord_3631780 prefixEnd_3631780 414410838085756861721723 := by
  unfold tailWord_3631780
  simp only [CollatzResearch.WordTrace]
  refine ⟨66230949391344396743898397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88307932521792528991864529 66230949391344396743898397)
  ·
    refine ⟨24836606021754148778961899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66230949391344396743898397 24836606021754148778961899)
    ·
      refine ⟨37254909032631223168442849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24836606021754148778961899 37254909032631223168442849)
      ·
        refine ⟨27941181774473417376332137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37254909032631223168442849 27941181774473417376332137)
        ·
          refine ⟨20955886330855063032249103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27941181774473417376332137 20955886330855063032249103)
          ·
            refine ⟨31433829496282594548373655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20955886330855063032249103 31433829496282594548373655)
            ·
              refine ⟨47150744244423891822560483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31433829496282594548373655 47150744244423891822560483)
              ·
                refine ⟨70726116366635837733840725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47150744244423891822560483 70726116366635837733840725)
                ·
                  refine ⟨414410838085756861721723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70726116366635837733840725 414410838085756861721723)
                  ·
                    rfl

theorem cell22_3631780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_3631780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631780 prefixEnd_3631780 := by exact prefixLift 3631780
  have htrace : WordTrace (prefixWord ++ tailWord_3631780) baseStart_3631780 baseEnd_3631780 := by
    simpa [prefixWord, tailWord_3631780, baseEnd_3631780] using wordTrace_append hprefix tailTrace_3631780
  have hstable : (prefixWord ++ tailWord_3631780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631780).length < 2 ^ (prefixWord ++ tailWord_3631780).sum := by decide
  have hdescent : baseEnd_3631780 < baseStart_3631780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631786 : List Nat := [3, 1, 5, 2, 2, 1, 8]
def baseStart_3631786 : Nat := 118140960795 + 3631786 * 2 ^ 59
def prefixEnd_3631786 : Nat := 4983230072969 + 3 ^ 40 * 3631786 * 2
def baseEnd_3631786 : Nat := 46045724747403280352413

theorem tailTrace_3631786 : CollatzResearch.WordTrace tailWord_3631786 prefixEnd_3631786 46045724747403280352413 := by
  unfold tailWord_3631786
  simp only [CollatzResearch.WordTrace]
  refine ⟨33115529405166764128128803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88308078413778037675010141 33115529405166764128128803)
  ·
    refine ⟨49673294107750146192193205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33115529405166764128128803 49673294107750146192193205)
    ·
      refine ⟨4656871322601576205518113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49673294107750146192193205 4656871322601576205518113)
      ·
        refine ⟨3492653491951182154138585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4656871322601576205518113 3492653491951182154138585)
        ·
          refine ⟨2619490118963386615603939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3492653491951182154138585 2619490118963386615603939)
          ·
            refine ⟨3929235178445079923405909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2619490118963386615603939 3929235178445079923405909)
            ·
              refine ⟨46045724747403280352413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3929235178445079923405909 46045724747403280352413)
              ·
                rfl

theorem cell22_3631786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 8].length) (baseStart_3631786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631786 prefixEnd_3631786 := by exact prefixLift 3631786
  have htrace : WordTrace (prefixWord ++ tailWord_3631786) baseStart_3631786 baseEnd_3631786 := by
    simpa [prefixWord, tailWord_3631786, baseEnd_3631786] using wordTrace_append hprefix tailTrace_3631786
  have hstable : (prefixWord ++ tailWord_3631786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631786).length < 2 ^ (prefixWord ++ tailWord_3631786).sum := by decide
  have hdescent : baseEnd_3631786 < baseStart_3631786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631797 : List Nat := [1, 3, 3, 3, 1, 1, 2, 1, 7]
def baseStart_3631797 : Nat := 118140960795 + 3631797 * 2 ^ 59
def prefixEnd_3631797 : Nat := 4983230072969 + 3 ^ 40 * 3631797 * 2
def baseEnd_3631797 : Nat := 414412777901562735830039

theorem tailTrace_3631797 : CollatzResearch.WordTrace tailWord_3631797 prefixEnd_3631797 414412777901562735830039 := by
  unfold tailWord_3631797
  simp only [CollatzResearch.WordTrace]
  refine ⟨132462518823627205391165645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88308345882418136927443763 132462518823627205391165645)
  ·
    refine ⟨49673444558860202021687117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132462518823627205391165645 49673444558860202021687117)
    ·
      refine ⟨18627541709572575758132669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49673444558860202021687117 18627541709572575758132669)
      ·
        refine ⟨6985328141089715909299751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18627541709572575758132669 6985328141089715909299751)
        ·
          refine ⟨10477992211634573863949627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6985328141089715909299751 10477992211634573863949627)
          ·
            refine ⟨15716988317451860795924441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10477992211634573863949627 15716988317451860795924441)
            ·
              refine ⟨11787741238088895596943331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15716988317451860795924441 11787741238088895596943331)
              ·
                refine ⟨17681611857133343395414997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11787741238088895596943331 17681611857133343395414997)
                ·
                  refine ⟨414412777901562735830039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17681611857133343395414997 414412777901562735830039)
                  ·
                    rfl

theorem cell22_3631797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 7].length) (baseStart_3631797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631797 prefixEnd_3631797 := by exact prefixLift 3631797
  have htrace : WordTrace (prefixWord ++ tailWord_3631797) baseStart_3631797 baseEnd_3631797 := by
    simpa [prefixWord, tailWord_3631797, baseEnd_3631797] using wordTrace_append hprefix tailTrace_3631797
  have hstable : (prefixWord ++ tailWord_3631797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631797).length < 2 ^ (prefixWord ++ tailWord_3631797).sum := by decide
  have hdescent : baseEnd_3631797 < baseStart_3631797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631825 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 8]
def baseStart_3631825 : Nat := 118140960795 + 3631825 * 2 ^ 59
def prefixEnd_3631825 : Nat := 4983230072969 + 3 ^ 40 * 3631825 * 2
def baseEnd_3631825 : Nat := 414415972892301822596677

theorem tailTrace_3631825 : CollatzResearch.WordTrace tailWord_3631825 prefixEnd_3631825 414415972892301822596677 := by
  unfold tailWord_3631825
  simp only [CollatzResearch.WordTrace]
  refine ⟨132463540067525766173184929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88309026711683844115456619 132463540067525766173184929)
  ·
    refine ⟨99347655050644324629888697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132463540067525766173184929 99347655050644324629888697)
    ·
      refine ⟨74510741287983243472416523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99347655050644324629888697 74510741287983243472416523)
      ·
        refine ⟨111766111931974865208624785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74510741287983243472416523 111766111931974865208624785)
        ·
          refine ⟨83824583948981148906468589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111766111931974865208624785 83824583948981148906468589)
          ·
            refine ⟨31434218980867930839925721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83824583948981148906468589 31434218980867930839925721)
            ·
              refine ⟨23575664235650948129944291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31434218980867930839925721 23575664235650948129944291)
              ·
                refine ⟨35363496353476422194916437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23575664235650948129944291 35363496353476422194916437)
                ·
                  refine ⟨414415972892301822596677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35363496353476422194916437 414415972892301822596677)
                  ·
                    rfl

theorem cell22_3631825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 8].length) (baseStart_3631825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631825 prefixEnd_3631825 := by exact prefixLift 3631825
  have htrace : WordTrace (prefixWord ++ tailWord_3631825) baseStart_3631825 baseEnd_3631825 := by
    simpa [prefixWord, tailWord_3631825, baseEnd_3631825] using wordTrace_append hprefix tailTrace_3631825
  have hstable : (prefixWord ++ tailWord_3631825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631825).length < 2 ^ (prefixWord ++ tailWord_3631825).sum := by decide
  have hdescent : baseEnd_3631825 < baseStart_3631825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631874 : List Nat := [3, 4, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_3631874 : Nat := 118140960795 + 3631874 * 2 ^ 59
def prefixEnd_3631874 : Nat := 4983230072969 + 3 ^ 40 * 3631874 * 2
def baseEnd_3631874 : Nat := 1243264692378285673314881

theorem tailTrace_3631874 : CollatzResearch.WordTrace tailWord_3631874 prefixEnd_3631874 1243264692378285673314881 := by
  unfold tailWord_3631874
  simp only [CollatzResearch.WordTrace]
  refine ⟨33116331811087061885429669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88310218162898831694479117 33116331811087061885429669)
  ·
    refine ⟨6209312214578824103518063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33116331811087061885429669 6209312214578824103518063)
    ·
      refine ⟨9313968321868236155277095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6209312214578824103518063 9313968321868236155277095)
      ·
        refine ⟨13970952482802354232915643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9313968321868236155277095 13970952482802354232915643)
        ·
          refine ⟨20956428724203531349373465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13970952482802354232915643 20956428724203531349373465)
          ·
            refine ⟨15717321543152648512030099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20956428724203531349373465 15717321543152648512030099)
            ·
              refine ⟨23575982314728972768045149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15717321543152648512030099 23575982314728972768045149)
              ·
                refine ⟨8840993368023364788016931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23575982314728972768045149 8840993368023364788016931)
                ·
                  refine ⟨13261490052035047182025397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8840993368023364788016931 13261490052035047182025397)
                  ·
                    refine ⟨1243264692378285673314881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13261490052035047182025397 1243264692378285673314881)
                    ·
                      rfl

theorem cell22_3631874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_3631874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631874 prefixEnd_3631874 := by exact prefixLift 3631874
  have htrace : WordTrace (prefixWord ++ tailWord_3631874) baseStart_3631874 baseEnd_3631874 := by
    simpa [prefixWord, tailWord_3631874, baseEnd_3631874] using wordTrace_append hprefix tailTrace_3631874
  have hstable : (prefixWord ++ tailWord_3631874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631874).length < 2 ^ (prefixWord ++ tailWord_3631874).sum := by decide
  have hdescent : baseEnd_3631874 < baseStart_3631874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631887 : List Nat := [1, 1, 2, 1, 1, 1, 9, 6]
def baseStart_3631887 : Nat := 118140960795 + 3631887 * 2 ^ 59
def prefixEnd_3631887 : Nat := 4983230072969 + 3 ^ 40 * 3631887 * 2
def baseEnd_3631887 : Nat := 138141015838217552526649

theorem tailTrace_3631887 : CollatzResearch.WordTrace tailWord_3631887 prefixEnd_3631887 138141015838217552526649 := by
  unfold tailWord_3631887
  simp only [CollatzResearch.WordTrace]
  refine ⟨132465801393301150761941915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88310534262200767174627943 132465801393301150761941915)
  ·
    refine ⟨198698702089951726142912873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132465801393301150761941915 198698702089951726142912873)
    ·
      refine ⟨149024026567463794607184655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198698702089951726142912873 149024026567463794607184655)
      ·
        refine ⟨223536039851195691910776983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149024026567463794607184655 223536039851195691910776983)
        ·
          refine ⟨335304059776793537866165475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223536039851195691910776983 335304059776793537866165475)
          ·
            refine ⟨502956089665190306799248213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335304059776793537866165475 502956089665190306799248213)
            ·
              refine ⟨2947008337881974453901845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 502956089665190306799248213 2947008337881974453901845)
              ·
                refine ⟨138141015838217552526649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2947008337881974453901845 138141015838217552526649)
                ·
                  rfl

theorem cell22_3631887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 6].length) (baseStart_3631887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631887 prefixEnd_3631887 := by exact prefixLift 3631887
  have htrace : WordTrace (prefixWord ++ tailWord_3631887) baseStart_3631887 baseEnd_3631887 := by
    simpa [prefixWord, tailWord_3631887, baseEnd_3631887] using wordTrace_append hprefix tailTrace_3631887
  have hstable : (prefixWord ++ tailWord_3631887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631887).length < 2 ^ (prefixWord ++ tailWord_3631887).sum := by decide
  have hdescent : baseEnd_3631887 < baseStart_3631887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631908 : List Nat := [2, 3, 1, 3, 3, 2, 1, 2, 2, 3]
def baseStart_3631908 : Nat := 118140960795 + 3631908 * 2 ^ 59
def prefixEnd_3631908 : Nat := 4983230072969 + 3 ^ 40 * 3631908 * 2
def baseEnd_3631908 : Nat := 1243276331273120917964777

theorem tailTrace_3631908 : CollatzResearch.WordTrace tailWord_3631908 prefixEnd_3631908 1243276331273120917964777 := by
  unfold tailWord_3631908
  simp only [CollatzResearch.WordTrace]
  refine ⟨66233283663112535674228189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88311044884150047565637585 66233283663112535674228189)
  ·
    refine ⟨24837481373667200877835571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66233283663112535674228189 24837481373667200877835571)
    ·
      refine ⟨37256222060500801316753357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24837481373667200877835571 37256222060500801316753357)
      ·
        refine ⟨13971083272687800493782509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37256222060500801316753357 13971083272687800493782509)
        ·
          refine ⟨5239156227257925185168441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13971083272687800493782509 5239156227257925185168441)
          ·
            refine ⟨3929367170443443888876331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5239156227257925185168441 3929367170443443888876331)
            ·
              refine ⟨5894050755665165833314497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3929367170443443888876331 5894050755665165833314497)
              ·
                refine ⟨4420538066748874374985873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5894050755665165833314497 4420538066748874374985873)
                ·
                  refine ⟨3315403550061655781239405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4420538066748874374985873 3315403550061655781239405)
                  ·
                    refine ⟨1243276331273120917964777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3315403550061655781239405 1243276331273120917964777)
                    ·
                      rfl

theorem cell22_3631908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_3631908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631908 prefixEnd_3631908 := by exact prefixLift 3631908
  have htrace : WordTrace (prefixWord ++ tailWord_3631908) baseStart_3631908 baseEnd_3631908 := by
    simpa [prefixWord, tailWord_3631908, baseEnd_3631908] using wordTrace_append hprefix tailTrace_3631908
  have hstable : (prefixWord ++ tailWord_3631908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631908).length < 2 ^ (prefixWord ++ tailWord_3631908).sum := by decide
  have hdescent : baseEnd_3631908 < baseStart_3631908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631970 : List Nat := [3, 3, 2, 1, 4, 1, 1, 1, 3, 3]
def baseStart_3631970 : Nat := 118140960795 + 3631970 * 2 ^ 59
def prefixEnd_3631970 : Nat := 4983230072969 + 3 ^ 40 * 3631970 * 2
def baseEnd_3631970 : Nat := 1243297555140173422914587

theorem tailTrace_3631970 : CollatzResearch.WordTrace tailWord_3631970 prefixEnd_3631970 1243297555140173422914587 := by
  unfold tailWord_3631970
  simp only [CollatzResearch.WordTrace]
  refine ⟨33117207163000113984303341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88312552434666970624808909 33117207163000113984303341)
  ·
    refine ⟨12418952686125042744113753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33117207163000113984303341 12418952686125042744113753)
    ·
      refine ⟨9314214514593782058085315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12418952686125042744113753 9314214514593782058085315)
      ·
        refine ⟨13971321771890673087127973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9314214514593782058085315 13971321771890673087127973)
        ·
          refine ⟨2619622832229501203836495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13971321771890673087127973 2619622832229501203836495)
          ·
            refine ⟨3929434248344251805754743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2619622832229501203836495 3929434248344251805754743)
            ·
              refine ⟨5894151372516377708632115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3929434248344251805754743 5894151372516377708632115)
              ·
                refine ⟨8841227058774566562948173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5894151372516377708632115 8841227058774566562948173)
                ·
                  refine ⟨3315460147040462461105565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8841227058774566562948173 3315460147040462461105565)
                  ·
                    refine ⟨1243297555140173422914587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3315460147040462461105565 1243297555140173422914587)
                    ·
                      rfl

theorem cell22_3631970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_3631970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3631970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3631970 prefixEnd_3631970 := by exact prefixLift 3631970
  have htrace : WordTrace (prefixWord ++ tailWord_3631970) baseStart_3631970 baseEnd_3631970 := by
    simpa [prefixWord, tailWord_3631970, baseEnd_3631970] using wordTrace_append hprefix tailTrace_3631970
  have hstable : (prefixWord ++ tailWord_3631970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631970).length < 2 ^ (prefixWord ++ tailWord_3631970).sum := by decide
  have hdescent : baseEnd_3631970 < baseStart_3631970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632009 : List Nat := [1, 2, 1, 1, 5, 3, 1, 2, 1, 5]
def baseStart_3632009 : Nat := 118140960795 + 3632009 * 2 ^ 59
def prefixEnd_3632009 : Nat := 4983230072969 + 3 ^ 40 * 3632009 * 2
def baseEnd_3632009 : Nat := 1243310905637190321189467

theorem tailTrace_3632009 : CollatzResearch.WordTrace tailWord_3632009 prefixEnd_3632009 1243310905637190321189467 := by
  unfold tailWord_3632009
  simp only [CollatzResearch.WordTrace]
  refine ⟨132470251098859165597883081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88313500732572777065255387 132470251098859165597883081)
  ·
    refine ⟨99352688324144374198412311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132470251098859165597883081 99352688324144374198412311)
    ·
      refine ⟨149029032486216561297618467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99352688324144374198412311 149029032486216561297618467)
      ·
        refine ⟨223543548729324841946427701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149029032486216561297618467 223543548729324841946427701)
        ·
          refine ⟨20957207693374203932477597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 223543548729324841946427701 20957207693374203932477597)
          ·
            refine ⟨7858952885015326474679099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20957207693374203932477597 7858952885015326474679099)
            ·
              refine ⟨11788429327522989712018649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7858952885015326474679099 11788429327522989712018649)
              ·
                refine ⟨8841321995642242284013987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11788429327522989712018649 8841321995642242284013987)
                ·
                  refine ⟨13261982993463363426020981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8841321995642242284013987 13261982993463363426020981)
                  ·
                    refine ⟨1243310905637190321189467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13261982993463363426020981 1243310905637190321189467)
                    ·
                      rfl

theorem cell22_3632009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 5].length) (baseStart_3632009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632009 prefixEnd_3632009 := by exact prefixLift 3632009
  have htrace : WordTrace (prefixWord ++ tailWord_3632009) baseStart_3632009 baseEnd_3632009 := by
    simpa [prefixWord, tailWord_3632009, baseEnd_3632009] using wordTrace_append hprefix tailTrace_3632009
  have hstable : (prefixWord ++ tailWord_3632009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632009).length < 2 ^ (prefixWord ++ tailWord_3632009).sum := by decide
  have hdescent : baseEnd_3632009 < baseStart_3632009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632028 : List Nat := [2, 2, 3, 3, 2, 1, 1, 4, 4]
def baseStart_3632028 : Nat := 118140960795 + 3632028 * 2 ^ 59
def prefixEnd_3632028 : Nat := 4983230072969 + 3 ^ 40 * 3632028 * 2
def baseEnd_3632028 : Nat := 414439136575160201654803

theorem tailTrace_3632028 : CollatzResearch.WordTrace tailWord_3632028 prefixEnd_3632028 414439136575160201654803 := by
  unfold tailWord_3632028
  simp only [CollatzResearch.WordTrace]
  refine ⟨66235472042895165921412369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88313962723860221228549825 66235472042895165921412369)
  ·
    refine ⟨49676604032171374441059277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66235472042895165921412369 49676604032171374441059277)
    ·
      refine ⟨18628726512064265415397229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49676604032171374441059277 18628726512064265415397229)
      ·
        refine ⟨6985772442024099530773961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18628726512064265415397229 6985772442024099530773961)
        ·
          refine ⟨5239329331518074648080471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6985772442024099530773961 5239329331518074648080471)
          ·
            refine ⟨7858993997277111972120707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5239329331518074648080471 7858993997277111972120707)
            ·
              refine ⟨11788490995915667958181061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7858993997277111972120707 11788490995915667958181061)
              ·
                refine ⟨2210342061734187742158949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11788490995915667958181061 2210342061734187742158949)
                ·
                  refine ⟨414439136575160201654803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2210342061734187742158949 414439136575160201654803)
                  ·
                    rfl

theorem cell22_3632028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4, 4].length) (baseStart_3632028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632028 prefixEnd_3632028 := by exact prefixLift 3632028
  have htrace : WordTrace (prefixWord ++ tailWord_3632028) baseStart_3632028 baseEnd_3632028 := by
    simpa [prefixWord, tailWord_3632028, baseEnd_3632028] using wordTrace_append hprefix tailTrace_3632028
  have hstable : (prefixWord ++ tailWord_3632028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632028).length < 2 ^ (prefixWord ++ tailWord_3632028).sum := by decide
  have hdescent : baseEnd_3632028 < baseStart_3632028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632037 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 4, 7]
def baseStart_3632037 : Nat := 118140960795 + 3632037 * 2 ^ 59
def prefixEnd_3632037 : Nat := 4983230072969 + 3 ^ 40 * 3632037 * 2
def baseEnd_3632037 : Nat := 1243320490609407581489381

theorem tailTrace_3632037 : CollatzResearch.WordTrace tailWord_3632037 prefixEnd_3632037 1243320490609407581489381 := by
  unfold tailWord_3632037
  simp only [CollatzResearch.WordTrace]
  refine ⟨132471272342757726379902365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88314181561838484253268243 132471272342757726379902365)
  ·
    refine ⟨49676727128534147392463387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132471272342757726379902365 49676727128534147392463387)
    ·
      refine ⟨74515090692801221088695081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49676727128534147392463387 74515090692801221088695081)
      ·
        refine ⟨55886318019600915816521311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74515090692801221088695081 55886318019600915816521311)
        ·
          refine ⟨83829477029401373724781967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55886318019600915816521311 83829477029401373724781967)
          ·
            refine ⟨125744215544102060587172951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83829477029401373724781967 125744215544102060587172951)
            ·
              refine ⟨188616323316153090880759427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125744215544102060587172951 188616323316153090880759427)
              ·
                refine ⟨282924484974229636321139141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188616323316153090880759427 282924484974229636321139141)
                ·
                  refine ⟨53048340932668056810213589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 282924484974229636321139141 53048340932668056810213589)
                  ·
                    refine ⟨1243320490609407581489381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53048340932668056810213589 1243320490609407581489381)
                    ·
                      rfl

theorem cell22_3632037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_3632037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632037 prefixEnd_3632037 := by exact prefixLift 3632037
  have htrace : WordTrace (prefixWord ++ tailWord_3632037) baseStart_3632037 baseEnd_3632037 := by
    simpa [prefixWord, tailWord_3632037, baseEnd_3632037] using wordTrace_append hprefix tailTrace_3632037
  have hstable : (prefixWord ++ tailWord_3632037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632037).length < 2 ^ (prefixWord ++ tailWord_3632037).sum := by decide
  have hdescent : baseEnd_3632037 < baseStart_3632037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632067 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 9]
def baseStart_3632067 : Nat := 118140960795 + 3632067 * 2 ^ 59
def prefixEnd_3632067 : Nat := 4983230072969 + 3 ^ 40 * 3632067 * 2
def baseEnd_3632067 : Nat := 414443586740832501079763

theorem tailTrace_3632067 : CollatzResearch.WordTrace tailWord_3632067 prefixEnd_3632067 414443586740832501079763 := by
  unfold tailWord_3632067
  simp only [CollatzResearch.WordTrace]
  refine ⟨132472366532649041503494455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88314911021766027668996303 132472366532649041503494455)
  ·
    refine ⟨198708549798973562255241683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132472366532649041503494455 198708549798973562255241683)
    ·
      refine ⟨298062824698460343382862525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198708549798973562255241683 298062824698460343382862525)
      ·
        refine ⟨111773559261922628768573447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298062824698460343382862525 111773559261922628768573447)
        ·
          refine ⟨167660338892883943152860171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111773559261922628768573447 167660338892883943152860171)
          ·
            refine ⟨251490508339325914729290257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167660338892883943152860171 251490508339325914729290257)
            ·
              refine ⟨188617881254494436046967693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251490508339325914729290257 188617881254494436046967693)
              ·
                refine ⟨70731705470435413517612885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188617881254494436046967693 70731705470435413517612885)
                ·
                  refine ⟨414443586740832501079763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70731705470435413517612885 414443586740832501079763)
                  ·
                    rfl

theorem cell22_3632067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 9].length) (baseStart_3632067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632067 prefixEnd_3632067 := by exact prefixLift 3632067
  have htrace : WordTrace (prefixWord ++ tailWord_3632067) baseStart_3632067 baseEnd_3632067 := by
    simpa [prefixWord, tailWord_3632067, baseEnd_3632067] using wordTrace_append hprefix tailTrace_3632067
  have hstable : (prefixWord ++ tailWord_3632067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632067).length < 2 ^ (prefixWord ++ tailWord_3632067).sum := by decide
  have hdescent : baseEnd_3632067 < baseStart_3632067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632077 : List Nat := [1, 6, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_3632077 : Nat := 118140960795 + 3632077 * 2 ^ 59
def prefixEnd_3632077 : Nat := 4983230072969 + 3 ^ 40 * 3632077 * 2
def baseEnd_3632077 : Nat := 1243334183426860810489259

theorem tailTrace_3632077 : CollatzResearch.WordTrace tailWord_3632077 prefixEnd_3632077 1243334183426860810489259 := by
  unfold tailWord_3632077
  simp only [CollatzResearch.WordTrace]
  refine ⟨132472731262612813211358485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88315154175075208807572323 132472731262612813211358485)
  ·
    refine ⟨6209659277934975619282429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 132472731262612813211358485 6209659277934975619282429)
    ·
      refine ⟨2328622229225615857230911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6209659277934975619282429 2328622229225615857230911)
      ·
        refine ⟨3492933343838423785846367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2328622229225615857230911 3492933343838423785846367)
        ·
          refine ⟨5239400015757635678769551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3492933343838423785846367 5239400015757635678769551)
          ·
            refine ⟨7859100023636453518154327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5239400015757635678769551 7859100023636453518154327)
            ·
              refine ⟨11788650035454680277231491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7859100023636453518154327 11788650035454680277231491)
              ·
                refine ⟨17682975053182020415847237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11788650035454680277231491 17682975053182020415847237)
                ·
                  refine ⟨3315557822471628827971357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17682975053182020415847237 3315557822471628827971357)
                  ·
                    refine ⟨1243334183426860810489259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3315557822471628827971357 1243334183426860810489259)
                    ·
                      rfl

theorem cell22_3632077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_3632077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632077 prefixEnd_3632077 := by exact prefixLift 3632077
  have htrace : WordTrace (prefixWord ++ tailWord_3632077) baseStart_3632077 baseEnd_3632077 := by
    simpa [prefixWord, tailWord_3632077, baseEnd_3632077] using wordTrace_append hprefix tailTrace_3632077
  have hstable : (prefixWord ++ tailWord_3632077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632077).length < 2 ^ (prefixWord ++ tailWord_3632077).sum := by decide
  have hdescent : baseEnd_3632077 < baseStart_3632077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632088 : List Nat := [2, 1, 2, 2, 2, 3, 2, 4, 1, 3]
def baseStart_3632088 : Nat := 118140960795 + 3632088 * 2 ^ 59
def prefixEnd_3632088 : Nat := 4983230072969 + 3 ^ 40 * 3632088 * 2
def baseEnd_3632088 : Nat := 1243337948951660448464225

theorem tailTrace_3632088 : CollatzResearch.WordTrace tailWord_3632088 prefixEnd_3632088 1243337948951660448464225 := by
  unfold tailWord_3632088
  simp only [CollatzResearch.WordTrace]
  refine ⟨66236566232786481045004459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88315421643715308060005945 66236566232786481045004459)
  ·
    refine ⟨99354849349179721567506689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66236566232786481045004459 99354849349179721567506689)
    ·
      refine ⟨74516137011884791175630017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99354849349179721567506689 74516137011884791175630017)
      ·
        refine ⟨55887102758913593381722513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74516137011884791175630017 55887102758913593381722513)
        ·
          refine ⟨41915327069185195036291885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55887102758913593381722513 41915327069185195036291885)
          ·
            refine ⟨15718247650944448138609457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41915327069185195036291885 15718247650944448138609457)
            ·
              refine ⟨11788685738208336103957093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15718247650944448138609457 11788685738208336103957093)
              ·
                refine ⟨2210378575914063019491955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11788685738208336103957093 2210378575914063019491955)
                ·
                  refine ⟨3315567863871094529237933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2210378575914063019491955 3315567863871094529237933)
                  ·
                    refine ⟨1243337948951660448464225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3315567863871094529237933 1243337948951660448464225)
                    ·
                      rfl

theorem cell22_3632088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4, 1, 3].length) (baseStart_3632088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632088 prefixEnd_3632088 := by exact prefixLift 3632088
  have htrace : WordTrace (prefixWord ++ tailWord_3632088) baseStart_3632088 baseEnd_3632088 := by
    simpa [prefixWord, tailWord_3632088, baseEnd_3632088] using wordTrace_append hprefix tailTrace_3632088
  have hstable : (prefixWord ++ tailWord_3632088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632088).length < 2 ^ (prefixWord ++ tailWord_3632088).sum := by decide
  have hdescent : baseEnd_3632088 < baseStart_3632088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632099 : List Nat := [1, 1, 1, 6, 1, 1, 1, 3, 2, 5]
def baseStart_3632099 : Nat := 118140960795 + 3632099 * 2 ^ 59
def prefixEnd_3632099 : Nat := 4983230072969 + 3 ^ 40 * 3632099 * 2
def baseEnd_3632099 : Nat := 1243341714476460086439191

theorem tailTrace_3632099 : CollatzResearch.WordTrace tailWord_3632099 prefixEnd_3632099 1243341714476460086439191 := by
  unfold tailWord_3632099
  simp only [CollatzResearch.WordTrace]
  refine ⟨132473533668533110968659351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88315689112355407312439567 132473533668533110968659351)
  ·
    refine ⟨198710300502799666452989027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132473533668533110968659351 198710300502799666452989027)
    ·
      refine ⟨298065450754199499679483541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198710300502799666452989027 298065450754199499679483541)
      ·
        refine ⟨13971818004103101547475791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 298065450754199499679483541 13971818004103101547475791)
        ·
          refine ⟨20957727006154652321213687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13971818004103101547475791 20957727006154652321213687)
          ·
            refine ⟨31436590509231978481820531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20957727006154652321213687 31436590509231978481820531)
            ·
              refine ⟨47154885763847967722730797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31436590509231978481820531 47154885763847967722730797)
              ·
                refine ⟨17683082161442987896024049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47154885763847967722730797 17683082161442987896024049)
                ·
                  refine ⟨13262311621082240922018037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17683082161442987896024049 13262311621082240922018037)
                  ·
                    refine ⟨1243341714476460086439191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13262311621082240922018037 1243341714476460086439191)
                    ·
                      rfl

theorem cell22_3632099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 5].length) (baseStart_3632099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632099 prefixEnd_3632099 := by exact prefixLift 3632099
  have htrace : WordTrace (prefixWord ++ tailWord_3632099) baseStart_3632099 baseEnd_3632099 := by
    simpa [prefixWord, tailWord_3632099, baseEnd_3632099] using wordTrace_append hprefix tailTrace_3632099
  have hstable : (prefixWord ++ tailWord_3632099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632099).length < 2 ^ (prefixWord ++ tailWord_3632099).sum := by decide
  have hdescent : baseEnd_3632099 < baseStart_3632099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632176 : List Nat := [2, 1, 1, 1, 2, 4, 4, 1, 2, 4]
def baseStart_3632176 : Nat := 118140960795 + 3632176 * 2 ^ 59
def prefixEnd_3632176 : Nat := 4983230072969 + 3 ^ 40 * 3632176 * 2
def baseEnd_3632176 : Nat := 1243368073150057552263955

theorem tailTrace_3632176 : CollatzResearch.WordTrace tailWord_3632176 prefixEnd_3632176 1243368073150057552263955 := by
  unfold tailWord_3632176
  simp only [CollatzResearch.WordTrace]
  refine ⟨66238171044627076559606191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88317561392836102079474921 66238171044627076559606191)
  ·
    refine ⟨99357256566940614839409287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66238171044627076559606191 99357256566940614839409287)
    ·
      refine ⟨149035884850410922259113931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99357256566940614839409287 149035884850410922259113931)
      ·
        refine ⟨223553827275616383388670897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149035884850410922259113931 223553827275616383388670897)
        ·
          refine ⟨167665370456712287541503173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223553827275616383388670897 167665370456712287541503173)
          ·
            refine ⟨31437256960633553914031845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167665370456712287541503173 31437256960633553914031845)
            ·
              refine ⟨5894485680118791358880971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31437256960633553914031845 5894485680118791358880971)
              ·
                refine ⟨8841728520178187038321457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5894485680118791358880971 8841728520178187038321457)
                ·
                  refine ⟨6631296390133640278741093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8841728520178187038321457 6631296390133640278741093)
                  ·
                    refine ⟨1243368073150057552263955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6631296390133640278741093 1243368073150057552263955)
                    ·
                      rfl

theorem cell22_3632176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 2, 4].length) (baseStart_3632176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632176 prefixEnd_3632176 := by exact prefixLift 3632176
  have htrace : WordTrace (prefixWord ++ tailWord_3632176) baseStart_3632176 baseEnd_3632176 := by
    simpa [prefixWord, tailWord_3632176, baseEnd_3632176] using wordTrace_append hprefix tailTrace_3632176
  have hstable : (prefixWord ++ tailWord_3632176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632176).length < 2 ^ (prefixWord ++ tailWord_3632176).sum := by decide
  have hdescent : baseEnd_3632176 < baseStart_3632176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632240 : List Nat := [2, 1, 1, 1, 5, 1, 4, 3, 1, 3]
def baseStart_3632240 : Nat := 118140960795 + 3632240 * 2 ^ 59
def prefixEnd_3632240 : Nat := 4983230072969 + 3 ^ 40 * 3632240 * 2
def baseEnd_3632240 : Nat := 1243389981657982718663759

theorem tailTrace_3632240 : CollatzResearch.WordTrace tailWord_3632240 prefixEnd_3632240 1243389981657982718663759 := by
  unfold tailWord_3632240
  simp only [CollatzResearch.WordTrace]
  refine ⟨66239338180511146024771087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88319117574014861366361449 66239338180511146024771087)
  ·
    refine ⟨99359007270766719037156631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66239338180511146024771087 99359007270766719037156631)
    ·
      refine ⟨149038510906150078555734947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99359007270766719037156631 149038510906150078555734947)
      ·
        refine ⟨223557766359225117833602421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149038510906150078555734947 223557766359225117833602421)
        ·
          refine ⟨20958540596177354796900227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 223557766359225117833602421 20958540596177354796900227)
          ·
            refine ⟨31437810894266032195350341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20958540596177354796900227 31437810894266032195350341)
            ·
              refine ⟨5894589542674881036628189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31437810894266032195350341 5894589542674881036628189)
              ·
                refine ⟨2210471078503080388735571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5894589542674881036628189 2210471078503080388735571)
                ·
                  refine ⟨3315706617754620583103357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2210471078503080388735571 3315706617754620583103357)
                  ·
                    refine ⟨1243389981657982718663759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3315706617754620583103357 1243389981657982718663759)
                    ·
                      rfl

theorem cell22_3632240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3, 1, 3].length) (baseStart_3632240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632240 prefixEnd_3632240 := by exact prefixLift 3632240
  have htrace : WordTrace (prefixWord ++ tailWord_3632240) baseStart_3632240 baseEnd_3632240 := by
    simpa [prefixWord, tailWord_3632240, baseEnd_3632240] using wordTrace_append hprefix tailTrace_3632240
  have hstable : (prefixWord ++ tailWord_3632240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632240).length < 2 ^ (prefixWord ++ tailWord_3632240).sum := by decide
  have hdescent : baseEnd_3632240 < baseStart_3632240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632270 : List Nat := [4, 1, 1, 3, 2, 2, 3, 1, 5]
def baseStart_3632270 : Nat := 118140960795 + 3632270 * 2 ^ 59
def prefixEnd_3632270 : Nat := 4983230072969 + 3 ^ 40 * 3632270 * 2
def baseEnd_3632270 : Nat := 414466750423690880137889

theorem tailTrace_3632270 : CollatzResearch.WordTrace tailWord_3632270 prefixEnd_3632270 414466750423690880137889 := by
  unfold tailWord_3632270
  simp only [CollatzResearch.WordTrace]
  refine ⟨16559971318864200896641783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88319847033942404782089509 16559971318864200896641783)
  ·
    refine ⟨24839956978296301344962675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16559971318864200896641783 24839956978296301344962675)
    ·
      refine ⟨37259935467444452017444013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24839956978296301344962675 37259935467444452017444013)
      ·
        refine ⟨13972475800291669506541505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37259935467444452017444013 13972475800291669506541505)
        ·
          refine ⟨10479356850218752129906129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13972475800291669506541505 10479356850218752129906129)
          ·
            refine ⟨7859517637664064097429597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10479356850218752129906129 7859517637664064097429597)
            ·
              refine ⟨2947319114124024036536099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7859517637664064097429597 2947319114124024036536099)
              ·
                refine ⟨4420978671186036054804149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2947319114124024036536099 4420978671186036054804149)
                ·
                  refine ⟨414466750423690880137889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4420978671186036054804149 414466750423690880137889)
                  ·
                    rfl

theorem cell22_3632270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_3632270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632270 prefixEnd_3632270 := by exact prefixLift 3632270
  have htrace : WordTrace (prefixWord ++ tailWord_3632270) baseStart_3632270 baseEnd_3632270 := by
    simpa [prefixWord, tailWord_3632270, baseEnd_3632270] using wordTrace_append hprefix tailTrace_3632270
  have hstable : (prefixWord ++ tailWord_3632270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632270).length < 2 ^ (prefixWord ++ tailWord_3632270).sum := by decide
  have hdescent : baseEnd_3632270 < baseStart_3632270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632313 : List Nat := [1, 2, 1, 4, 1, 3, 2, 1, 4, 3]
def baseStart_3632313 : Nat := 118140960795 + 3632313 * 2 ^ 59
def prefixEnd_3632313 : Nat := 4983230072969 + 3 ^ 40 * 3632313 * 2
def baseEnd_3632313 : Nat := 1243414971049834861588535

theorem tailTrace_3632313 : CollatzResearch.WordTrace tailWord_3632313 prefixEnd_3632313 1243414971049834861588535 := by
  unfold tailWord_3632313
  simp only [CollatzResearch.WordTrace]
  refine ⟨132481338889757825516949593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88320892593171883677966395 132481338889757825516949593)
  ·
    refine ⟨99361004167318369137712195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132481338889757825516949593 99361004167318369137712195)
    ·
      refine ⟨149041506250977553706568293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99361004167318369137712195 149041506250977553706568293)
      ·
        refine ⟨27945282422058291319981555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149041506250977553706568293 27945282422058291319981555)
        ·
          refine ⟨41917923633087436979972333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27945282422058291319981555 41917923633087436979972333)
          ·
            refine ⟨15719221362407788867489625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41917923633087436979972333 15719221362407788867489625)
            ·
              refine ⟨11789416021805841650617219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15719221362407788867489625 11789416021805841650617219)
              ·
                refine ⟨17684124032708762475925829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11789416021805841650617219 17684124032708762475925829)
                ·
                  refine ⟨3315773256132892964236093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17684124032708762475925829 3315773256132892964236093)
                  ·
                    refine ⟨1243414971049834861588535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3315773256132892964236093 1243414971049834861588535)
                    ·
                      rfl

theorem cell22_3632313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4, 3].length) (baseStart_3632313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632313 prefixEnd_3632313 := by exact prefixLift 3632313
  have htrace : WordTrace (prefixWord ++ tailWord_3632313) baseStart_3632313 baseEnd_3632313 := by
    simpa [prefixWord, tailWord_3632313, baseEnd_3632313] using wordTrace_append hprefix tailTrace_3632313
  have hstable : (prefixWord ++ tailWord_3632313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632313).length < 2 ^ (prefixWord ++ tailWord_3632313).sum := by decide
  have hdescent : baseEnd_3632313 < baseStart_3632313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632330 : List Nat := [3, 1, 2, 1, 3, 3, 1, 3, 2, 3]
def baseStart_3632330 : Nat := 118140960795 + 3632330 * 2 ^ 59
def prefixEnd_3632330 : Nat := 4983230072969 + 3 ^ 40 * 3632330 * 2
def baseEnd_3632330 : Nat := 1243420790497252483913483

theorem tailTrace_3632330 : CollatzResearch.WordTrace tailWord_3632330 prefixEnd_3632330 1243420790497252483913483 := by
  unfold tailWord_3632330
  simp only [CollatzResearch.WordTrace]
  refine ⟨33120489732674059355079611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88321305953797491613545629 33120489732674059355079611)
  ·
    refine ⟨49680734599011089032619417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33120489732674059355079611 49680734599011089032619417)
    ·
      refine ⟨37260550949258316774464563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49680734599011089032619417 37260550949258316774464563)
      ·
        refine ⟨55890826423887475161696845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37260550949258316774464563 55890826423887475161696845)
        ·
          refine ⟨20959059908957803185636317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55890826423887475161696845 20959059908957803185636317)
          ·
            refine ⟨7859647465859176194613619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20959059908957803185636317 7859647465859176194613619)
            ·
              refine ⟨11789471198788764291920429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7859647465859176194613619 11789471198788764291920429)
              ·
                refine ⟨4421051699545786609470161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11789471198788764291920429 4421051699545786609470161)
                ·
                  refine ⟨3315788774659339957102621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4421051699545786609470161 3315788774659339957102621)
                  ·
                    refine ⟨1243420790497252483913483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3315788774659339957102621 1243420790497252483913483)
                    ·
                      rfl

theorem cell22_3632330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_3632330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632330 prefixEnd_3632330 := by exact prefixLift 3632330
  have htrace : WordTrace (prefixWord ++ tailWord_3632330) baseStart_3632330 baseEnd_3632330 := by
    simpa [prefixWord, tailWord_3632330, baseEnd_3632330] using wordTrace_append hprefix tailTrace_3632330
  have hstable : (prefixWord ++ tailWord_3632330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632330).length < 2 ^ (prefixWord ++ tailWord_3632330).sum := by decide
  have hdescent : baseEnd_3632330 < baseStart_3632330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632375 : List Nat := [1, 1, 3, 1, 1, 1, 2, 8, 1, 3]
def baseStart_3632375 : Nat := 118140960795 + 3632375 * 2 ^ 59
def prefixEnd_3632375 : Nat := 4983230072969 + 3 ^ 40 * 3632375 * 2
def baseEnd_3632375 : Nat := 1243436194916887366538345

theorem tailTrace_3632375 : CollatzResearch.WordTrace tailWord_3632375 prefixEnd_3632375 1243436194916887366538345 := by
  unfold tailWord_3632375
  simp only [CollatzResearch.WordTrace]
  refine ⟨132483600215533210105706579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88322400143688806737137719 132483600215533210105706579)
  ·
    refine ⟨198725400323299815158559869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132483600215533210105706579 198725400323299815158559869)
    ·
      refine ⟨74522025121237430684459951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198725400323299815158559869 74522025121237430684459951)
      ·
        refine ⟨111783037681856146026689927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74522025121237430684459951 111783037681856146026689927)
        ·
          refine ⟨167674556522784219040034891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111783037681856146026689927 167674556522784219040034891)
          ·
            refine ⟨251511834784176328560052337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167674556522784219040034891 251511834784176328560052337)
            ·
              refine ⟨188633876088132246420039253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251511834784176328560052337 188633876088132246420039253)
              ·
                refine ⟨2210553235407799762734835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 188633876088132246420039253 2210553235407799762734835)
                ·
                  refine ⟨3315829853111699644102253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2210553235407799762734835 3315829853111699644102253)
                  ·
                    refine ⟨1243436194916887366538345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3315829853111699644102253 1243436194916887366538345)
                    ·
                      rfl

theorem cell22_3632375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8, 1, 3].length) (baseStart_3632375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632375 prefixEnd_3632375 := by exact prefixLift 3632375
  have htrace : WordTrace (prefixWord ++ tailWord_3632375) baseStart_3632375 baseEnd_3632375 := by
    simpa [prefixWord, tailWord_3632375, baseEnd_3632375] using wordTrace_append hprefix tailTrace_3632375
  have hstable : (prefixWord ++ tailWord_3632375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632375).length < 2 ^ (prefixWord ++ tailWord_3632375).sum := by decide
  have hdescent : baseEnd_3632375 < baseStart_3632375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632433 : List Nat := [1, 2, 2, 3, 3, 1, 1, 3, 6]
def baseStart_3632433 : Nat := 118140960795 + 3632433 * 2 ^ 59
def prefixEnd_3632433 : Nat := 4983230072969 + 3 ^ 40 * 3632433 * 2
def baseEnd_3632433 : Nat := 414485349834064849529389

theorem tailTrace_3632433 : CollatzResearch.WordTrace tailWord_3632433 prefixEnd_3632433 414485349834064849529389 := by
  unfold tailWord_3632433
  simp only [CollatzResearch.WordTrace]
  refine ⟨132485715649323086011317953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88323810432882057340878635 132485715649323086011317953)
  ·
    refine ⟨99364286736992314508488465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132485715649323086011317953 99364286736992314508488465)
    ·
      refine ⟨74523215052744235881366349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99364286736992314508488465 74523215052744235881366349)
      ·
        refine ⟨27946205644779088455512381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74523215052744235881366349 27946205644779088455512381)
        ·
          refine ⟨10479827116792158170817143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27946205644779088455512381 10479827116792158170817143)
          ·
            refine ⟨15719740675188237256225715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10479827116792158170817143 15719740675188237256225715)
            ·
              refine ⟨23579611012782355884338573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15719740675188237256225715 23579611012782355884338573)
              ·
                refine ⟨8842354129793383456626965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23579611012782355884338573 8842354129793383456626965)
                ·
                  refine ⟨414485349834064849529389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8842354129793383456626965 414485349834064849529389)
                  ·
                    rfl

theorem cell22_3632433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 6].length) (baseStart_3632433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632433 prefixEnd_3632433 := by exact prefixLift 3632433
  have htrace : WordTrace (prefixWord ++ tailWord_3632433) baseStart_3632433 baseEnd_3632433 := by
    simpa [prefixWord, tailWord_3632433, baseEnd_3632433] using wordTrace_append hprefix tailTrace_3632433
  have hstable : (prefixWord ++ tailWord_3632433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632433).length < 2 ^ (prefixWord ++ tailWord_3632433).sum := by decide
  have hdescent : baseEnd_3632433 < baseStart_3632433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632452 : List Nat := [2, 3, 4, 1, 1, 1, 1, 4, 1, 4]
def baseStart_3632452 : Nat := 118140960795 + 3632452 * 2 ^ 59
def prefixEnd_3632452 : Nat := 4983230072969 + 3 ^ 40 * 3632452 * 2
def baseEnd_3632452 : Nat := 1243462553590484832363109

theorem tailTrace_3632452 : CollatzResearch.WordTrace tailWord_3632452 prefixEnd_3632452 1243462553590484832363109 := by
  unfold tailWord_3632452
  simp only [CollatzResearch.WordTrace]
  refine ⟨66243204318127126128129805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88324272424169501504173073 66243204318127126128129805)
  ·
    refine ⟨24841201619297672298048677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66243204318127126128129805 24841201619297672298048677)
    ·
      refine ⟨4657725303618313555884127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24841201619297672298048677 4657725303618313555884127)
      ·
        refine ⟨6986587955427470333826191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4657725303618313555884127 6986587955427470333826191)
        ·
          refine ⟨10479881933141205500739287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6986587955427470333826191 10479881933141205500739287)
          ·
            refine ⟨15719822899711808251108931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10479881933141205500739287 15719822899711808251108931)
            ·
              refine ⟨23579734349567712376663397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15719822899711808251108931 23579734349567712376663397)
              ·
                refine ⟨4421200190543946070624387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23579734349567712376663397 4421200190543946070624387)
                ·
                  refine ⟨6631800285815919105936581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4421200190543946070624387 6631800285815919105936581)
                  ·
                    refine ⟨1243462553590484832363109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6631800285815919105936581 1243462553590484832363109)
                    ·
                      rfl

theorem cell22_3632452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_3632452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632452 prefixEnd_3632452 := by exact prefixLift 3632452
  have htrace : WordTrace (prefixWord ++ tailWord_3632452) baseStart_3632452 baseEnd_3632452 := by
    simpa [prefixWord, tailWord_3632452, baseEnd_3632452] using wordTrace_append hprefix tailTrace_3632452
  have hstable : (prefixWord ++ tailWord_3632452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632452).length < 2 ^ (prefixWord ++ tailWord_3632452).sum := by decide
  have hdescent : baseEnd_3632452 < baseStart_3632452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632480 : List Nat := [2, 1, 1, 3, 4, 2, 1, 2, 2, 4]
def baseStart_3632480 : Nat := 118140960795 + 3632480 * 2 ^ 59
def prefixEnd_3632480 : Nat := 4983230072969 + 3 ^ 40 * 3632480 * 2
def baseEnd_3632480 : Nat := 1243472138562702092663023

theorem tailTrace_3632480 : CollatzResearch.WordTrace tailWord_3632480 prefixEnd_3632480 1243472138562702092663023 := by
  unfold tailWord_3632480
  simp only [CollatzResearch.WordTrace]
  refine ⟨66243714940076406519139447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88324953253435208692185929 66243714940076406519139447)
  ·
    refine ⟨99365572410114609778709171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66243714940076406519139447 99365572410114609778709171)
    ·
      refine ⟨149048358615171914668063757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99365572410114609778709171 149048358615171914668063757)
      ·
        refine ⟨55893134480689468000523909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149048358615171914668063757 55893134480689468000523909)
        ·
          refine ⟨10479962715129275250098233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55893134480689468000523909 10479962715129275250098233)
          ·
            refine ⟨7859972036346956437573675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10479962715129275250098233 7859972036346956437573675)
            ·
              refine ⟨11789958054520434656360513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7859972036346956437573675 11789958054520434656360513)
              ·
                refine ⟨8842468540890325992270385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11789958054520434656360513 8842468540890325992270385)
                ·
                  refine ⟨6631851405667744494202789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8842468540890325992270385 6631851405667744494202789)
                  ·
                    refine ⟨1243472138562702092663023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6631851405667744494202789 1243472138562702092663023)
                    ·
                      rfl

theorem cell22_3632480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 2, 4].length) (baseStart_3632480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632480 prefixEnd_3632480 := by exact prefixLift 3632480
  have htrace : WordTrace (prefixWord ++ tailWord_3632480) baseStart_3632480 baseEnd_3632480 := by
    simpa [prefixWord, tailWord_3632480, baseEnd_3632480] using wordTrace_append hprefix tailTrace_3632480
  have hstable : (prefixWord ++ tailWord_3632480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632480).length < 2 ^ (prefixWord ++ tailWord_3632480).sum := by decide
  have hdescent : baseEnd_3632480 < baseStart_3632480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632482 : List Nat := [3, 3, 2, 1, 1, 1, 2, 4, 2, 3]
def baseStart_3632482 : Nat := 118140960795 + 3632482 * 2 ^ 59
def prefixEnd_3632482 : Nat := 4983230072969 + 3 ^ 40 * 3632482 * 2
def baseEnd_3632482 : Nat := 1243472823203574754113017

theorem tailTrace_3632482 : CollatzResearch.WordTrace tailWord_3632482 prefixEnd_3632482 1243472823203574754113017 := by
  unfold tailWord_3632482
  simp only [CollatzResearch.WordTrace]
  refine ⟨33121875706536391844962925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88325001884097044919901133 33121875706536391844962925)
  ·
    refine ⟨12420703389951146941861097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33121875706536391844962925 12420703389951146941861097)
    ·
      refine ⟨9315527542463360206395823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12420703389951146941861097 9315527542463360206395823)
      ·
        refine ⟨13973291313695040309593735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9315527542463360206395823 13973291313695040309593735)
        ·
          refine ⟨20959936970542560464390603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13973291313695040309593735 20959936970542560464390603)
          ·
            refine ⟨31439905455813840696585905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20959936970542560464390603 31439905455813840696585905)
            ·
              refine ⟨23579929091860380522439429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31439905455813840696585905 23579929091860380522439429)
              ·
                refine ⟨4421236704723821347957393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23579929091860380522439429 4421236704723821347957393)
                ·
                  refine ⟨3315927528542866010968045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4421236704723821347957393 3315927528542866010968045)
                  ·
                    refine ⟨1243472823203574754113017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3315927528542866010968045 1243472823203574754113017)
                    ·
                      rfl

theorem cell22_3632482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_3632482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632482 prefixEnd_3632482 := by exact prefixLift 3632482
  have htrace : WordTrace (prefixWord ++ tailWord_3632482) baseStart_3632482 baseEnd_3632482 := by
    simpa [prefixWord, tailWord_3632482, baseEnd_3632482] using wordTrace_append hprefix tailTrace_3632482
  have hstable : (prefixWord ++ tailWord_3632482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632482).length < 2 ^ (prefixWord ++ tailWord_3632482).sum := by decide
  have hdescent : baseEnd_3632482 < baseStart_3632482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632514 : List Nat := [3, 4, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_3632514 : Nat := 118140960795 + 3632514 * 2 ^ 59
def prefixEnd_3632514 : Nat := 4983230072969 + 3 ^ 40 * 3632514 * 2
def baseEnd_3632514 : Nat := 1243483777457537337312919

theorem tailTrace_3632514 : CollatzResearch.WordTrace tailWord_3632514 prefixEnd_3632514 1243483777457537337312919 := by
  unfold tailWord_3632514
  simp only [CollatzResearch.WordTrace]
  refine ⟨33122167490507409211254149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88325779974686424563344397 33122167490507409211254149)
  ·
    refine ⟨6210406404470139227110153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33122167490507409211254149 6210406404470139227110153)
    ·
      refine ⟨4657804803352604420332615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6210406404470139227110153 4657804803352604420332615)
      ·
        refine ⟨6986707205028906630498923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4657804803352604420332615 6986707205028906630498923)
        ·
          refine ⟨10480060807543359945748385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6986707205028906630498923 10480060807543359945748385)
          ·
            refine ⟨7860045605657519959311289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10480060807543359945748385 7860045605657519959311289)
            ·
              refine ⟨5895034204243139969483467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7860045605657519959311289 5895034204243139969483467)
              ·
                refine ⟨8842551306364709954225201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5895034204243139969483467 8842551306364709954225201)
                ·
                  refine ⟨6631913479773532465668901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8842551306364709954225201 6631913479773532465668901)
                  ·
                    refine ⟨1243483777457537337312919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6631913479773532465668901 1243483777457537337312919)
                    ·
                      rfl

theorem cell22_3632514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_3632514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632514 prefixEnd_3632514 := by exact prefixLift 3632514
  have htrace : WordTrace (prefixWord ++ tailWord_3632514) baseStart_3632514 baseEnd_3632514 := by
    simpa [prefixWord, tailWord_3632514, baseEnd_3632514] using wordTrace_append hprefix tailTrace_3632514
  have hstable : (prefixWord ++ tailWord_3632514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632514).length < 2 ^ (prefixWord ++ tailWord_3632514).sum := by decide
  have hdescent : baseEnd_3632514 < baseStart_3632514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632557 : List Nat := [1, 5, 2, 2, 1, 1, 2, 3, 5]
def baseStart_3632557 : Nat := 118140960795 + 3632557 * 2 ^ 59
def prefixEnd_3632557 : Nat := 4983230072969 + 3 ^ 40 * 3632557 * 2
def baseEnd_3632557 : Nat := 414499499078766519495929

theorem tailTrace_3632557 : CollatzResearch.WordTrace tailWord_3632557 prefixEnd_3632557 414499499078766519495929 := by
  unfold tailWord_3632557
  simp only [CollatzResearch.WordTrace]
  refine ⟨132490238300873855188831925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88326825533915903459221283 132490238300873855188831925)
  ·
    refine ⟨12420959840706923923952993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132490238300873855188831925 12420959840706923923952993)
    ·
      refine ⟨9315719880530192942964745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12420959840706923923952993 9315719880530192942964745)
      ·
        refine ⟨6986789910397644707223559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9315719880530192942964745 6986789910397644707223559)
        ·
          refine ⟨10480184865596467060835339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6986789910397644707223559 10480184865596467060835339)
          ·
            refine ⟨15720277298394700591253009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10480184865596467060835339 15720277298394700591253009)
            ·
              refine ⟨11790207973796025443439757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15720277298394700591253009 11790207973796025443439757)
              ·
                refine ⟨4421327990173509541289909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11790207973796025443439757 4421327990173509541289909)
                ·
                  refine ⟨414499499078766519495929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4421327990173509541289909 414499499078766519495929)
                  ·
                    rfl

theorem cell22_3632557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_3632557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632557 prefixEnd_3632557 := by exact prefixLift 3632557
  have htrace : WordTrace (prefixWord ++ tailWord_3632557) baseStart_3632557 baseEnd_3632557 := by
    simpa [prefixWord, tailWord_3632557, baseEnd_3632557] using wordTrace_append hprefix tailTrace_3632557
  have hstable : (prefixWord ++ tailWord_3632557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632557).length < 2 ^ (prefixWord ++ tailWord_3632557).sum := by decide
  have hdescent : baseEnd_3632557 < baseStart_3632557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632568 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 8]
def baseStart_3632568 : Nat := 118140960795 + 3632568 * 2 ^ 59
def prefixEnd_3632568 : Nat := 4983230072969 + 3 ^ 40 * 3632568 * 2
def baseEnd_3632568 : Nat := 414500754253699732154251

theorem tailTrace_3632568 : CollatzResearch.WordTrace tailWord_3632568 prefixEnd_3632568 414500754253699732154251 := by
  unfold tailWord_3632568
  simp only [CollatzResearch.WordTrace]
  refine ⟨66245319751917002033741179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88327093002556002711654905 66245319751917002033741179)
  ·
    refine ⟨99367979627875503050611769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66245319751917002033741179 99367979627875503050611769)
    ·
      refine ⟨74525984720906627287958827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99367979627875503050611769 74525984720906627287958827)
      ·
        refine ⟨111788977081359940931938241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74525984720906627287958827 111788977081359940931938241)
        ·
          refine ⟨83841732811019955698953681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111788977081359940931938241 83841732811019955698953681)
          ·
            refine ⟨62881299608264966774215261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83841732811019955698953681 62881299608264966774215261)
            ·
              refine ⟨23580487353099362540330723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62881299608264966774215261 23580487353099362540330723)
              ·
                refine ⟨35370731029649043810496085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23580487353099362540330723 35370731029649043810496085)
                ·
                  refine ⟨414500754253699732154251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35370731029649043810496085 414500754253699732154251)
                  ·
                    rfl

theorem cell22_3632568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 8].length) (baseStart_3632568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632568 prefixEnd_3632568 := by exact prefixLift 3632568
  have htrace : WordTrace (prefixWord ++ tailWord_3632568) baseStart_3632568 baseEnd_3632568 := by
    simpa [prefixWord, tailWord_3632568, baseEnd_3632568] using wordTrace_append hprefix tailTrace_3632568
  have hstable : (prefixWord ++ tailWord_3632568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632568).length < 2 ^ (prefixWord ++ tailWord_3632568).sum := by decide
  have hdescent : baseEnd_3632568 < baseStart_3632568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632587 : List Nat := [1, 1, 1, 1, 3, 3, 6, 1, 1, 4]
def baseStart_3632587 : Nat := 118140960795 + 3632587 * 2 ^ 59
def prefixEnd_3632587 : Nat := 4983230072969 + 3 ^ 40 * 3632587 * 2
def baseEnd_3632587 : Nat := 1243508766849389480237695

theorem tailTrace_3632587 : CollatzResearch.WordTrace tailWord_3632587 prefixEnd_3632587 1243508766849389480237695 := by
  unfold tailWord_3632587
  simp only [CollatzResearch.WordTrace]
  refine ⟨132491332490765170312424015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88327554993843446874949343 132491332490765170312424015)
  ·
    refine ⟨198736998736147755468636023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132491332490765170312424015 198736998736147755468636023)
    ·
      refine ⟨298105498104221633202954035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198736998736147755468636023 298105498104221633202954035)
      ·
        refine ⟨447158247156332449804431053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298105498104221633202954035 447158247156332449804431053)
        ·
          refine ⟨167684342683624668676661645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 447158247156332449804431053 167684342683624668676661645)
          ·
            refine ⟨62881628506359250753748117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167684342683624668676661645 62881628506359250753748117)
            ·
              refine ⟨2947576336235589879081943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62881628506359250753748117 2947576336235589879081943)
              ·
                refine ⟨4421364504353384818622915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2947576336235589879081943 4421364504353384818622915)
                ·
                  refine ⟨6632046756530077227934373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4421364504353384818622915 6632046756530077227934373)
                  ·
                    refine ⟨1243508766849389480237695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6632046756530077227934373 1243508766849389480237695)
                    ·
                      rfl

theorem cell22_3632587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 1, 4].length) (baseStart_3632587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632587 prefixEnd_3632587 := by exact prefixLift 3632587
  have htrace : WordTrace (prefixWord ++ tailWord_3632587) baseStart_3632587 baseEnd_3632587 := by
    simpa [prefixWord, tailWord_3632587, baseEnd_3632587] using wordTrace_append hprefix tailTrace_3632587
  have hstable : (prefixWord ++ tailWord_3632587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632587).length < 2 ^ (prefixWord ++ tailWord_3632587).sum := by decide
  have hdescent : baseEnd_3632587 < baseStart_3632587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632602 : List Nat := [3, 1, 1, 2, 3, 2, 2, 4, 4]
def baseStart_3632602 : Nat := 118140960795 + 3632602 * 2 ^ 59
def prefixEnd_3632602 : Nat := 4983230072969 + 3 ^ 40 * 3632602 * 2
def baseEnd_3632602 : Nat := 414504633885311480370883

theorem tailTrace_3632602 : CollatzResearch.WordTrace tailWord_3632602 prefixEnd_3632602 414504633885311480370883 := by
  unfold tailWord_3632602
  simp only [CollatzResearch.WordTrace]
  refine ⟨33122969896427706968555015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88327919723807218582813373 33122969896427706968555015)
  ·
    refine ⟨49684454844641560452832523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33122969896427706968555015 49684454844641560452832523)
    ·
      refine ⟨74526682266962340679248785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49684454844641560452832523 74526682266962340679248785)
      ·
        refine ⟨55895011700221755509436589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74526682266962340679248785 55895011700221755509436589)
        ·
          refine ⟨20960629387583158316038721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55895011700221755509436589 20960629387583158316038721)
          ·
            refine ⟨15720472040687368737029041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20960629387583158316038721 15720472040687368737029041)
            ·
              refine ⟨11790354030515526552771781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15720472040687368737029041 11790354030515526552771781)
              ·
                refine ⟨2210691380721661228644709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11790354030515526552771781 2210691380721661228644709)
                ·
                  refine ⟨414504633885311480370883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2210691380721661228644709 414504633885311480370883)
                  ·
                    rfl

theorem cell22_3632602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4, 4].length) (baseStart_3632602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632602 prefixEnd_3632602 := by exact prefixLift 3632602
  have htrace : WordTrace (prefixWord ++ tailWord_3632602) baseStart_3632602 baseEnd_3632602 := by
    simpa [prefixWord, tailWord_3632602, baseEnd_3632602] using wordTrace_append hprefix tailTrace_3632602
  have hstable : (prefixWord ++ tailWord_3632602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632602).length < 2 ^ (prefixWord ++ tailWord_3632602).sum := by decide
  have hdescent : baseEnd_3632602 < baseStart_3632602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632615 : List Nat := [1, 1, 5, 2, 1, 2, 1, 2, 1, 6]
def baseStart_3632615 : Nat := 118140960795 + 3632615 * 2 ^ 59
def prefixEnd_3632615 : Nat := 4983230072969 + 3 ^ 40 * 3632615 * 2
def baseEnd_3632615 : Nat := 1243518351821606740537609

theorem tailTrace_3632615 : CollatzResearch.WordTrace tailWord_3632615 prefixEnd_3632615 1243518351821606740537609 := by
  unfold tailWord_3632615
  simp only [CollatzResearch.WordTrace]
  refine ⟨132492353734663731094443299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88328235823109154062962199 132492353734663731094443299)
  ·
    refine ⟨198738530601995596641664949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132492353734663731094443299 198738530601995596641664949)
    ·
      refine ⟨18631737243937087185156089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198738530601995596641664949 18631737243937087185156089)
      ·
        refine ⟨13973802932952815388867067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18631737243937087185156089 13973802932952815388867067)
        ·
          refine ⟨20960704399429223083300601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13973802932952815388867067 20960704399429223083300601)
          ·
            refine ⟨15720528299571917312475451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20960704399429223083300601 15720528299571917312475451)
            ·
              refine ⟨23580792449357875968713177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15720528299571917312475451 23580792449357875968713177)
              ·
                refine ⟨17685594337018406976534883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23580792449357875968713177 17685594337018406976534883)
                ·
                  refine ⟨26528391505527610464802325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17685594337018406976534883 26528391505527610464802325)
                  ·
                    refine ⟨1243518351821606740537609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26528391505527610464802325 1243518351821606740537609)
                    ·
                      rfl

theorem cell22_3632615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_3632615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632615 prefixEnd_3632615 := by exact prefixLift 3632615
  have htrace : WordTrace (prefixWord ++ tailWord_3632615) baseStart_3632615 baseEnd_3632615 := by
    simpa [prefixWord, tailWord_3632615, baseEnd_3632615] using wordTrace_append hprefix tailTrace_3632615
  have hstable : (prefixWord ++ tailWord_3632615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632615).length < 2 ^ (prefixWord ++ tailWord_3632615).sum := by decide
  have hdescent : baseEnd_3632615 < baseStart_3632615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632653 : List Nat := [1, 7, 1, 1, 3, 1, 1, 1, 6]
def baseStart_3632653 : Nat := 118140960795 + 3632653 * 2 ^ 59
def prefixEnd_3632653 : Nat := 4983230072969 + 3 ^ 40 * 3632653 * 2
def baseEnd_3632653 : Nat := 414510453332729102695831

theorem tailTrace_3632653 : CollatzResearch.WordTrace tailWord_3632653 prefixEnd_3632653 414510453332729102695831 := by
  unfold tailWord_3632653
  simp only [CollatzResearch.WordTrace]
  refine ⟨132493739708526063584326613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88329159805684042389551075 132493739708526063584326613)
  ·
    refine ⟨3105322024418579615257655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 132493739708526063584326613 3105322024418579615257655)
    ·
      refine ⟨4657983036627869422886483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3105322024418579615257655 4657983036627869422886483)
      ·
        refine ⟨6986974554941804134329725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4657983036627869422886483 6986974554941804134329725)
        ·
          refine ⟨2620115458103176550373647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6986974554941804134329725 2620115458103176550373647)
          ·
            refine ⟨3930173187154764825560471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2620115458103176550373647 3930173187154764825560471)
            ·
              refine ⟨5895259780732147238340707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3930173187154764825560471 5895259780732147238340707)
              ·
                refine ⟨8842889671098220857511061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5895259780732147238340707 8842889671098220857511061)
                ·
                  refine ⟨414510453332729102695831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8842889671098220857511061 414510453332729102695831)
                  ·
                    rfl

theorem cell22_3632653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_3632653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632653 prefixEnd_3632653 := by exact prefixLift 3632653
  have htrace : WordTrace (prefixWord ++ tailWord_3632653) baseStart_3632653 baseEnd_3632653 := by
    simpa [prefixWord, tailWord_3632653, baseEnd_3632653] using wordTrace_append hprefix tailTrace_3632653
  have hstable : (prefixWord ++ tailWord_3632653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632653).length < 2 ^ (prefixWord ++ tailWord_3632653).sum := by decide
  have hdescent : baseEnd_3632653 < baseStart_3632653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632690 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 4, 5]
def baseStart_3632690 : Nat := 118140960795 + 3632690 * 2 ^ 59
def prefixEnd_3632690 : Nat := 4983230072969 + 3 ^ 40 * 3632690 * 2
def baseEnd_3632690 : Nat := 1243544025854331544912379

theorem tailTrace_3632690 : CollatzResearch.WordTrace tailWord_3632690 prefixEnd_3632690 1243544025854331544912379 := by
  unfold tailWord_3632690
  simp only [CollatzResearch.WordTrace]
  refine ⟨33123772302348004725855881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88330059472928012602282349 33123772302348004725855881)
  ·
    refine ⟨24842829226761003544391911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33123772302348004725855881 24842829226761003544391911)
    ·
      refine ⟨37264243840141505316587867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24842829226761003544391911 37264243840141505316587867)
      ·
        refine ⟨55896365760212257974881801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37264243840141505316587867 55896365760212257974881801)
        ·
          refine ⟨41922274320159193481161351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55896365760212257974881801 41922274320159193481161351)
          ·
            refine ⟨62883411480238790221742027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41922274320159193481161351 62883411480238790221742027)
            ·
              refine ⟨94325117220358185332613041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62883411480238790221742027 94325117220358185332613041)
              ·
                refine ⟨70743837915268638999459781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94325117220358185332613041 70743837915268638999459781)
                ·
                  refine ⟨13264469609112869812398709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70743837915268638999459781 13264469609112869812398709)
                  ·
                    refine ⟨1243544025854331544912379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13264469609112869812398709 1243544025854331544912379)
                    ·
                      rfl

theorem cell22_3632690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_3632690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632690 prefixEnd_3632690 := by exact prefixLift 3632690
  have htrace : WordTrace (prefixWord ++ tailWord_3632690) baseStart_3632690 baseEnd_3632690 := by
    simpa [prefixWord, tailWord_3632690, baseEnd_3632690] using wordTrace_append hprefix tailTrace_3632690
  have hstable : (prefixWord ++ tailWord_3632690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632690).length < 2 ^ (prefixWord ++ tailWord_3632690).sum := by decide
  have hdescent : baseEnd_3632690 < baseStart_3632690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632720 : List Nat := [2, 1, 1, 1, 1, 3, 4, 3, 6]
def baseStart_3632720 : Nat := 118140960795 + 3632720 * 2 ^ 59
def prefixEnd_3632720 : Nat := 4983230072969 + 3 ^ 40 * 3632720 * 2
def baseEnd_3632720 : Nat := 414518098489140488887429

theorem tailTrace_3632720 : CollatzResearch.WordTrace tailWord_3632720 prefixEnd_3632720 414518098489140488887429 := by
  unfold tailWord_3632720
  simp only [CollatzResearch.WordTrace]
  refine ⟨66248091699641667013507807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88330788932855556018010409 66248091699641667013507807)
  ·
    refine ⟨99372137549462500520261711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66248091699641667013507807 99372137549462500520261711)
    ·
      refine ⟨149058206324193750780392567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99372137549462500520261711 149058206324193750780392567)
      ·
        refine ⟨223587309486290626170588851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149058206324193750780392567 223587309486290626170588851)
        ·
          refine ⟨335380964229435939255883277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223587309486290626170588851 335380964229435939255883277)
          ·
            refine ⟨125767861586038477220956229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335380964229435939255883277 125767861586038477220956229)
            ·
              refine ⟨23581474047382214478929293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125767861586038477220956229 23581474047382214478929293)
              ·
                refine ⟨8843052767768330429598485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23581474047382214478929293 8843052767768330429598485)
                ·
                  refine ⟨414518098489140488887429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8843052767768330429598485 414518098489140488887429)
                  ·
                    rfl

theorem cell22_3632720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 6].length) (baseStart_3632720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632720 prefixEnd_3632720 := by exact prefixLift 3632720
  have htrace : WordTrace (prefixWord ++ tailWord_3632720) baseStart_3632720 baseEnd_3632720 := by
    simpa [prefixWord, tailWord_3632720, baseEnd_3632720] using wordTrace_append hprefix tailTrace_3632720
  have hstable : (prefixWord ++ tailWord_3632720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632720).length < 2 ^ (prefixWord ++ tailWord_3632720).sum := by decide
  have hdescent : baseEnd_3632720 < baseStart_3632720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632722 : List Nat := [3, 2, 2, 1, 2, 2, 1, 2, 3, 4]
def baseStart_3632722 : Nat := 118140960795 + 3632722 * 2 ^ 59
def prefixEnd_3632722 : Nat := 4983230072969 + 3 ^ 40 * 3632722 * 2
def baseEnd_3632722 : Nat := 1243554980108294128112281

theorem tailTrace_3632722 : CollatzResearch.WordTrace tailWord_3632722 prefixEnd_3632722 1243554980108294128112281 := by
  unfold tailWord_3632722
  simp only [CollatzResearch.WordTrace]
  refine ⟨33124064086319022092147105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88330837563517392245725613 33124064086319022092147105)
  ·
    refine ⟨24843048064739266569110329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33124064086319022092147105 24843048064739266569110329)
    ·
      refine ⟨18632286048554449926832747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24843048064739266569110329 18632286048554449926832747)
      ·
        refine ⟨27948429072831674890249121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18632286048554449926832747 27948429072831674890249121)
        ·
          refine ⟨20961321804623756167686841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27948429072831674890249121 20961321804623756167686841)
          ·
            refine ⟨15720991353467817125765131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20961321804623756167686841 15720991353467817125765131)
            ·
              refine ⟨23581487030201725688647697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15720991353467817125765131 23581487030201725688647697)
              ·
                refine ⟨17686115272651294266485773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23581487030201725688647697 17686115272651294266485773)
                ·
                  refine ⟨6632293227244235349932165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17686115272651294266485773 6632293227244235349932165)
                  ·
                    refine ⟨1243554980108294128112281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6632293227244235349932165 1243554980108294128112281)
                    ·
                      rfl

theorem cell22_3632722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_3632722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632722 prefixEnd_3632722 := by exact prefixLift 3632722
  have htrace : WordTrace (prefixWord ++ tailWord_3632722) baseStart_3632722 baseEnd_3632722 := by
    simpa [prefixWord, tailWord_3632722, baseEnd_3632722] using wordTrace_append hprefix tailTrace_3632722
  have hstable : (prefixWord ++ tailWord_3632722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632722).length < 2 ^ (prefixWord ++ tailWord_3632722).sum := by decide
  have hdescent : baseEnd_3632722 < baseStart_3632722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632752 : List Nat := [2, 1, 1, 1, 6, 1, 2, 2, 1, 5]
def baseStart_3632752 : Nat := 118140960795 + 3632752 * 2 ^ 59
def prefixEnd_3632752 : Nat := 4983230072969 + 3 ^ 40 * 3632752 * 2
def baseEnd_3632752 : Nat := 1243565249721384049862189

theorem tailTrace_3632752 : CollatzResearch.WordTrace tailWord_3632752 prefixEnd_3632752 1243565249721384049862189 := by
  unfold tailWord_3632752
  simp only [CollatzResearch.WordTrace]
  refine ⟨66248675267583701746090255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88331567023444935661453673 66248675267583701746090255)
  ·
    refine ⟨99373012901375552619135383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66248675267583701746090255 99373012901375552619135383)
    ·
      refine ⟨149059519352063328928703075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99373012901375552619135383 149059519352063328928703075)
      ·
        refine ⟨223589279028094993393054613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149059519352063328928703075 223589279028094993393054613)
        ·
          refine ⟨10480747454441952815299435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 223589279028094993393054613 10480747454441952815299435)
          ·
            refine ⟨15721121181662929222949153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10480747454441952815299435 15721121181662929222949153)
            ·
              refine ⟨11790840886247196917211865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15721121181662929222949153 11790840886247196917211865)
              ·
                refine ⟨8843130664685397687908899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11790840886247196917211865 8843130664685397687908899)
                ·
                  refine ⟨13264695997028096531863349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8843130664685397687908899 13264695997028096531863349)
                  ·
                    refine ⟨1243565249721384049862189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13264695997028096531863349 1243565249721384049862189)
                    ·
                      rfl

theorem cell22_3632752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 1, 5].length) (baseStart_3632752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632752 prefixEnd_3632752 := by exact prefixLift 3632752
  have htrace : WordTrace (prefixWord ++ tailWord_3632752) baseStart_3632752 baseEnd_3632752 := by
    simpa [prefixWord, tailWord_3632752, baseEnd_3632752] using wordTrace_append hprefix tailTrace_3632752
  have hstable : (prefixWord ++ tailWord_3632752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632752).length < 2 ^ (prefixWord ++ tailWord_3632752).sum := by decide
  have hdescent : baseEnd_3632752 < baseStart_3632752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632754 : List Nat := [3, 2, 1, 2, 3, 1, 1, 5, 4]
def baseStart_3632754 : Nat := 118140960795 + 3632754 * 2 ^ 59
def prefixEnd_3632754 : Nat := 4983230072969 + 3 ^ 40 * 3632754 * 2
def baseEnd_3632754 : Nat := 414521978120752237104061

theorem tailTrace_3632754 : CollatzResearch.WordTrace tailWord_3632754 prefixEnd_3632754 414521978120752237104061 := by
  unfold tailWord_3632754
  simp only [CollatzResearch.WordTrace]
  refine ⟨33124355870290039458438329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88331615654106771889168877 33124355870290039458438329)
  ·
    refine ⟨24843266902717529593828747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33124355870290039458438329 24843266902717529593828747)
    ·
      refine ⟨37264900354076294390743121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24843266902717529593828747 37264900354076294390743121)
      ·
        refine ⟨27948675265557220793057341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37264900354076294390743121 27948675265557220793057341)
        ·
          refine ⟨10480753224583957797396503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27948675265557220793057341 10480753224583957797396503)
          ·
            refine ⟨15721129836875936696094755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10480753224583957797396503 15721129836875936696094755)
            ·
              refine ⟨23581694755313905044142133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15721129836875936696094755 23581694755313905044142133)
              ·
                refine ⟨2210783883310678597888325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23581694755313905044142133 2210783883310678597888325)
                ·
                  refine ⟨414521978120752237104061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2210783883310678597888325 414521978120752237104061)
                  ·
                    rfl

theorem cell22_3632754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_3632754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632754 prefixEnd_3632754 := by exact prefixLift 3632754
  have htrace : WordTrace (prefixWord ++ tailWord_3632754) baseStart_3632754 baseEnd_3632754 := by
    simpa [prefixWord, tailWord_3632754, baseEnd_3632754] using wordTrace_append hprefix tailTrace_3632754
  have hstable : (prefixWord ++ tailWord_3632754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632754).length < 2 ^ (prefixWord ++ tailWord_3632754).sum := by decide
  have hdescent : baseEnd_3632754 < baseStart_3632754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632769 : List Nat := [1, 2, 4, 2, 1, 3, 1, 1, 4, 3]
def baseStart_3632769 : Nat := 118140960795 + 3632769 * 2 ^ 59
def prefixEnd_3632769 : Nat := 4983230072969 + 3 ^ 40 * 3632769 * 2
def baseEnd_3632769 : Nat := 1243571069168801672187137

theorem tailTrace_3632769 : CollatzResearch.WordTrace tailWord_3632769 prefixEnd_3632769 1243571069168801672187137 := by
  unfold tailWord_3632769
  simp only [CollatzResearch.WordTrace]
  refine ⟨132497970576105815395549361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88331980384070543597032907 132497970576105815395549361)
  ·
    refine ⟨99373477932079361546662021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132497970576105815395549361 99373477932079361546662021)
    ·
      refine ⟨18632527112264880289999129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99373477932079361546662021 18632527112264880289999129)
      ·
        refine ⟨13974395334198660217499347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18632527112264880289999129 13974395334198660217499347)
        ·
          refine ⟨20961593001297990326249021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13974395334198660217499347 20961593001297990326249021)
          ·
            refine ⟨7860597375486746372343383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20961593001297990326249021 7860597375486746372343383)
            ·
              refine ⟨11790896063230119558515075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7860597375486746372343383 11790896063230119558515075)
              ·
                refine ⟨17686344094845179337772613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11790896063230119558515075 17686344094845179337772613)
                ·
                  refine ⟨3316189517783471125832365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17686344094845179337772613 3316189517783471125832365)
                  ·
                    refine ⟨1243571069168801672187137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3316189517783471125832365 1243571069168801672187137)
                    ·
                      rfl

theorem cell22_3632769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_3632769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632769 prefixEnd_3632769 := by exact prefixLift 3632769
  have htrace : WordTrace (prefixWord ++ tailWord_3632769) baseStart_3632769 baseEnd_3632769 := by
    simpa [prefixWord, tailWord_3632769, baseEnd_3632769] using wordTrace_append hprefix tailTrace_3632769
  have hstable : (prefixWord ++ tailWord_3632769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632769).length < 2 ^ (prefixWord ++ tailWord_3632769).sum := by decide
  have hdescent : baseEnd_3632769 < baseStart_3632769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632786 : List Nat := [3, 2, 3, 1, 3, 2, 1, 1, 1, 5]
def baseStart_3632786 : Nat := 118140960795 + 3632786 * 2 ^ 59
def prefixEnd_3632786 : Nat := 4983230072969 + 3 ^ 40 * 3632786 * 2
def baseEnd_3632786 : Nat := 1243576888616219294512085

theorem tailTrace_3632786 : CollatzResearch.WordTrace tailWord_3632786 prefixEnd_3632786 1243576888616219294512085 := by
  unfold tailWord_3632786
  simp only [CollatzResearch.WordTrace]
  refine ⟨33124647654261056824729553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88332393744696151532612141 33124647654261056824729553)
  ·
    refine ⟨24843485740695792618547165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33124647654261056824729553 24843485740695792618547165)
    ·
      refine ⟨9316307152760922231955187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24843485740695792618547165 9316307152760922231955187)
      ·
        refine ⟨13974460729141383347932781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9316307152760922231955187 13974460729141383347932781)
        ·
          refine ⟨5240422773428018755474793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13974460729141383347932781 5240422773428018755474793)
          ·
            refine ⟨3930317080071014066606095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5240422773428018755474793 3930317080071014066606095)
            ·
              refine ⟨5895475620106521099909143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3930317080071014066606095 5895475620106521099909143)
              ·
                refine ⟨8843213430159781649863715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5895475620106521099909143 8843213430159781649863715)
                ·
                  refine ⟨13264820145239672474795573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8843213430159781649863715 13264820145239672474795573)
                  ·
                    refine ⟨1243576888616219294512085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13264820145239672474795573 1243576888616219294512085)
                    ·
                      rfl

theorem cell22_3632786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_3632786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632786 prefixEnd_3632786 := by exact prefixLift 3632786
  have htrace : WordTrace (prefixWord ++ tailWord_3632786) baseStart_3632786 baseEnd_3632786 := by
    simpa [prefixWord, tailWord_3632786, baseEnd_3632786] using wordTrace_append hprefix tailTrace_3632786
  have hstable : (prefixWord ++ tailWord_3632786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632786).length < 2 ^ (prefixWord ++ tailWord_3632786).sum := by decide
  have hdescent : baseEnd_3632786 < baseStart_3632786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632799 : List Nat := [1, 1, 2, 7, 1, 1, 1, 8]
def baseStart_3632799 : Nat := 118140960795 + 3632799 * 2 ^ 59
def prefixEnd_3632799 : Nat := 4983230072969 + 3 ^ 40 * 3632799 * 2
def baseEnd_3632799 : Nat := 138175704309099065993005

theorem tailTrace_3632799 : CollatzResearch.WordTrace tailWord_3632799 prefixEnd_3632799 138175704309099065993005 := by
  unfold tailWord_3632799
  simp only [CollatzResearch.WordTrace]
  refine ⟨132499064765997130519141451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88332709843998087012760967 132499064765997130519141451)
  ·
    refine ⟨198748597148995695778712177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132499064765997130519141451 198748597148995695778712177)
    ·
      refine ⟨149061447861746771834034133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198748597148995695778712177 149061447861746771834034133)
      ·
        refine ⟨3493627684259689964860175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 149061447861746771834034133 3493627684259689964860175)
        ·
          refine ⟨5240441526389534947290263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3493627684259689964860175 5240441526389534947290263)
          ·
            refine ⟨7860662289584302420935395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5240441526389534947290263 7860662289584302420935395)
            ·
              refine ⟨11790993434376453631403093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7860662289584302420935395 11790993434376453631403093)
              ·
                refine ⟨138175704309099065993005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11790993434376453631403093 138175704309099065993005)
                ·
                  rfl

theorem cell22_3632799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 8].length) (baseStart_3632799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632799 prefixEnd_3632799 := by exact prefixLift 3632799
  have htrace : WordTrace (prefixWord ++ tailWord_3632799) baseStart_3632799 baseEnd_3632799 := by
    simpa [prefixWord, tailWord_3632799, baseEnd_3632799] using wordTrace_append hprefix tailTrace_3632799
  have hstable : (prefixWord ++ tailWord_3632799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632799).length < 2 ^ (prefixWord ++ tailWord_3632799).sum := by decide
  have hdescent : baseEnd_3632799 < baseStart_3632799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632874 : List Nat := [3, 1, 3, 1, 1, 1, 2, 5, 1, 4]
def baseStart_3632874 : Nat := 118140960795 + 3632874 * 2 ^ 59
def prefixEnd_3632874 : Nat := 4983230072969 + 3 ^ 40 * 3632874 * 2
def baseEnd_3632874 : Nat := 1243607012814616398311815

theorem tailTrace_3632874 : CollatzResearch.WordTrace tailWord_3632874 prefixEnd_3632874 1243607012814616398311815 := by
  unfold tailWord_3632874
  simp only [CollatzResearch.WordTrace]
  refine ⟨33125450060181354582030419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88334533493816945552081117 33125450060181354582030419)
  ·
    refine ⟨49688175090272031873045629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33125450060181354582030419 49688175090272031873045629)
    ·
      refine ⟨18633065658852011952392111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49688175090272031873045629 18633065658852011952392111)
      ·
        refine ⟨27949598488278017928588167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18633065658852011952392111 27949598488278017928588167)
        ·
          refine ⟨41924397732417026892882251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27949598488278017928588167 41924397732417026892882251)
          ·
            refine ⟨62886596598625540339323377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41924397732417026892882251 62886596598625540339323377)
            ·
              refine ⟨47164947448969155254492533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62886596598625540339323377 47164947448969155254492533)
              ·
                refine ⟨4421713823340858305108675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47164947448969155254492533 4421713823340858305108675)
                ·
                  refine ⟨6632570735011287457663013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4421713823340858305108675 6632570735011287457663013)
                  ·
                    refine ⟨1243607012814616398311815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6632570735011287457663013 1243607012814616398311815)
                    ·
                      rfl

theorem cell22_3632874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_3632874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632874 prefixEnd_3632874 := by exact prefixLift 3632874
  have htrace : WordTrace (prefixWord ++ tailWord_3632874) baseStart_3632874 baseEnd_3632874 := by
    simpa [prefixWord, tailWord_3632874, baseEnd_3632874] using wordTrace_append hprefix tailTrace_3632874
  have hstable : (prefixWord ++ tailWord_3632874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632874).length < 2 ^ (prefixWord ++ tailWord_3632874).sum := by decide
  have hdescent : baseEnd_3632874 < baseStart_3632874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632904 : List Nat := [2, 1, 3, 2, 2, 1, 4, 1, 1, 5]
def baseStart_3632904 : Nat := 118140960795 + 3632904 * 2 ^ 59
def prefixEnd_3632904 : Nat := 4983230072969 + 3 ^ 40 * 3632904 * 2
def baseEnd_3632904 : Nat := 1243617282427706320061723

theorem tailTrace_3632904 : CollatzResearch.WordTrace tailWord_3632904 prefixEnd_3632904 1243617282427706320061723 := by
  unfold tailWord_3632904
  simp only [CollatzResearch.WordTrace]
  refine ⟨66251447215308366725856883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88335262953744488967809177 66251447215308366725856883)
  ·
    refine ⟨99377170822962550088785325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66251447215308366725856883 99377170822962550088785325)
    ·
      refine ⟨37266439058610956283294497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99377170822962550088785325 37266439058610956283294497)
      ·
        refine ⟨27949829293958217212470873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37266439058610956283294497 27949829293958217212470873)
        ·
          refine ⟨20962371970468662909353155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27949829293958217212470873 20962371970468662909353155)
          ·
            refine ⟨31443557955702994364029733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20962371970468662909353155 31443557955702994364029733)
            ·
              refine ⟨5895667116694311443255575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31443557955702994364029733 5895667116694311443255575)
              ·
                refine ⟨8843500675041467164883363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5895667116694311443255575 8843500675041467164883363)
                ·
                  refine ⟨13265251012562200747325045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8843500675041467164883363 13265251012562200747325045)
                  ·
                    refine ⟨1243617282427706320061723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13265251012562200747325045 1243617282427706320061723)
                    ·
                      rfl

theorem cell22_3632904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_3632904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632904 prefixEnd_3632904 := by exact prefixLift 3632904
  have htrace : WordTrace (prefixWord ++ tailWord_3632904) baseStart_3632904 baseEnd_3632904 := by
    simpa [prefixWord, tailWord_3632904, baseEnd_3632904] using wordTrace_append hprefix tailTrace_3632904
  have hstable : (prefixWord ++ tailWord_3632904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632904).length < 2 ^ (prefixWord ++ tailWord_3632904).sum := by decide
  have hdescent : baseEnd_3632904 < baseStart_3632904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632919 : List Nat := [1, 1, 3, 4, 2, 2, 1, 1, 1, 6]
def baseStart_3632919 : Nat := 118140960795 + 3632919 * 2 ^ 59
def prefixEnd_3632919 : Nat := 4983230072969 + 3 ^ 40 * 3632919 * 2
def baseEnd_3632919 : Nat := 1243622417234251280936677

theorem tailTrace_3632919 : CollatzResearch.WordTrace tailWord_3632919 prefixEnd_3632919 1243622417234251280936677 := by
  unfold tailWord_3632919
  simp only [CollatzResearch.WordTrace]
  refine ⟨132503441525562391013509811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88335627683708260675673207 132503441525562391013509811)
  ·
    refine ⟨198755162288343586520264717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132503441525562391013509811 198755162288343586520264717)
    ·
      refine ⟨74533185858128844945099269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198755162288343586520264717 74533185858128844945099269)
      ·
        refine ⟨13974972348399158427206113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74533185858128844945099269 13974972348399158427206113)
        ·
          refine ⟨10481229261299368820404585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13974972348399158427206113 10481229261299368820404585)
          ·
            refine ⟨7860921945974526615303439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10481229261299368820404585 7860921945974526615303439)
            ·
              refine ⟨11791382918961789922955159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7860921945974526615303439 11791382918961789922955159)
              ·
                refine ⟨17687074378442684884432739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11791382918961789922955159 17687074378442684884432739)
                ·
                  refine ⟨26530611567664027326649109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17687074378442684884432739 26530611567664027326649109)
                  ·
                    refine ⟨1243622417234251280936677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26530611567664027326649109 1243622417234251280936677)
                    ·
                      rfl

theorem cell22_3632919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_3632919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3632919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3632919 prefixEnd_3632919 := by exact prefixLift 3632919
  have htrace : WordTrace (prefixWord ++ tailWord_3632919) baseStart_3632919 baseEnd_3632919 := by
    simpa [prefixWord, tailWord_3632919, baseEnd_3632919] using wordTrace_append hprefix tailTrace_3632919
  have hstable : (prefixWord ++ tailWord_3632919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632919).length < 2 ^ (prefixWord ++ tailWord_3632919).sum := by decide
  have hdescent : baseEnd_3632919 < baseStart_3632919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633000 : List Nat := [2, 1, 4, 2, 1, 1, 5, 2, 1, 3]
def baseStart_3633000 : Nat := 118140960795 + 3633000 * 2 ^ 59
def prefixEnd_3633000 : Nat := 4983230072969 + 3 ^ 40 * 3633000 * 2
def baseEnd_3633000 : Nat := 1243650145189594069661429

theorem tailTrace_3633000 : CollatzResearch.WordTrace tailWord_3633000 prefixEnd_3633000 1243650145189594069661429 := by
  unfold tailWord_3633000
  simp only [CollatzResearch.WordTrace]
  refine ⟨66253197919134470923604227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88337597225512627898138969 66253197919134470923604227)
  ·
    refine ⟨99379796878701706385406341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66253197919134470923604227 99379796878701706385406341)
    ·
      refine ⟨18633711914756569947263689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99379796878701706385406341 18633711914756569947263689)
      ·
        refine ⟨13975283936067427460447767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18633711914756569947263689 13975283936067427460447767)
        ·
          refine ⟨20962925904101141190671651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13975283936067427460447767 20962925904101141190671651)
          ·
            refine ⟨31444388856151711786007477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20962925904101141190671651 31444388856151711786007477)
            ·
              refine ⟨2947911455264222979938201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31444388856151711786007477 2947911455264222979938201)
              ·
                refine ⟨2210933591448167234953651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2947911455264222979938201 2210933591448167234953651)
                ·
                  refine ⟨3316400387172250852430477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2210933591448167234953651 3316400387172250852430477)
                  ·
                    refine ⟨1243650145189594069661429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3316400387172250852430477 1243650145189594069661429)
                    ·
                      rfl

theorem cell22_3633000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_3633000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3633000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3633000 prefixEnd_3633000 := by exact prefixLift 3633000
  have htrace : WordTrace (prefixWord ++ tailWord_3633000) baseStart_3633000 baseEnd_3633000 := by
    simpa [prefixWord, tailWord_3633000, baseEnd_3633000] using wordTrace_append hprefix tailTrace_3633000
  have hstable : (prefixWord ++ tailWord_3633000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633000).length < 2 ^ (prefixWord ++ tailWord_3633000).sum := by decide
  have hdescent : baseEnd_3633000 < baseStart_3633000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633009 : List Nat := [1, 2, 2, 2, 1, 3, 2, 2, 3, 4]
def baseStart_3633009 : Nat := 118140960795 + 3633009 * 2 ^ 59
def prefixEnd_3633009 : Nat := 4983230072969 + 3 ^ 40 * 3633009 * 2
def baseEnd_3633009 : Nat := 1243653226073521046186401

theorem tailTrace_3633009 : CollatzResearch.WordTrace tailWord_3633009 prefixEnd_3633009 1243653226073521046186401 := by
  unfold tailWord_3633009
  simp only [CollatzResearch.WordTrace]
  refine ⟨132506724095236336384286081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88337816063490890922857387 132506724095236336384286081)
  ·
    refine ⟨99380043071427252288214561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132506724095236336384286081 99380043071427252288214561)
    ·
      refine ⟨74535032303570439216160921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99380043071427252288214561 74535032303570439216160921)
      ·
        refine ⟨55901274227677829412120691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74535032303570439216160921 55901274227677829412120691)
        ·
          refine ⟨83851911341516744118181037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55901274227677829412120691 83851911341516744118181037)
          ·
            refine ⟨31444466753068779044317889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83851911341516744118181037 31444466753068779044317889)
            ·
              refine ⟨23583350064801584283238417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31444466753068779044317889 23583350064801584283238417)
              ·
                refine ⟨17687512548601188212428813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23583350064801584283238417 17687512548601188212428813)
                ·
                  refine ⟨6632817205725445579660805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17687512548601188212428813 6632817205725445579660805)
                  ·
                    refine ⟨1243653226073521046186401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6632817205725445579660805 1243653226073521046186401)
                    ·
                      rfl

theorem cell22_3633009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_3633009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3633009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3633009 prefixEnd_3633009 := by exact prefixLift 3633009
  have htrace : WordTrace (prefixWord ++ tailWord_3633009) baseStart_3633009 baseEnd_3633009 := by
    simpa [prefixWord, tailWord_3633009, baseEnd_3633009] using wordTrace_append hprefix tailTrace_3633009
  have hstable : (prefixWord ++ tailWord_3633009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633009).length < 2 ^ (prefixWord ++ tailWord_3633009).sum := by decide
  have hdescent : baseEnd_3633009 < baseStart_3633009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633073 : List Nat := [1, 2, 2, 4, 2, 1, 2, 3, 2, 3]
def baseStart_3633073 : Nat := 118140960795 + 3633073 * 2 ^ 59
def prefixEnd_3633073 : Nat := 4983230072969 + 3 ^ 40 * 3633073 * 2
def baseEnd_3633073 : Nat := 1243675134581446212586205

theorem tailTrace_3633073 : CollatzResearch.WordTrace tailWord_3633073 prefixEnd_3633073 1243675134581446212586205 := by
  unfold tailWord_3633073
  simp only [CollatzResearch.WordTrace]
  refine ⟨132509058367004475314615873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88339372244669650209743915 132509058367004475314615873)
  ·
    refine ⟨99381793775253356485961905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132509058367004475314615873 99381793775253356485961905)
    ·
      refine ⟨74536345331440017364471429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99381793775253356485961905 74536345331440017364471429)
      ·
        refine ⟨13975564749645003255838393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74536345331440017364471429 13975564749645003255838393)
        ·
          refine ⟨10481673562233752441878795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13975564749645003255838393 10481673562233752441878795)
          ·
            refine ⟨15722510343350628662818193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10481673562233752441878795 15722510343350628662818193)
            ·
              refine ⟨11791882757512971497113645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15722510343350628662818193 11791882757512971497113645)
              ·
                refine ⟨4421956034067364311417617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11791882757512971497113645 4421956034067364311417617)
                ·
                  refine ⟨3316467025550523233563213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4421956034067364311417617 3316467025550523233563213)
                  ·
                    refine ⟨1243675134581446212586205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3316467025550523233563213 1243675134581446212586205)
                    ·
                      rfl

theorem cell22_3633073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2, 3].length) (baseStart_3633073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3633073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3633073 prefixEnd_3633073 := by exact prefixLift 3633073
  have htrace : WordTrace (prefixWord ++ tailWord_3633073) baseStart_3633073 baseEnd_3633073 := by
    simpa [prefixWord, tailWord_3633073, baseEnd_3633073] using wordTrace_append hprefix tailTrace_3633073
  have hstable : (prefixWord ++ tailWord_3633073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633073).length < 2 ^ (prefixWord ++ tailWord_3633073).sum := by decide
  have hdescent : baseEnd_3633073 < baseStart_3633073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633208 : List Nat := [2, 1, 2, 1, 6, 1, 1, 2, 1, 5]
def baseStart_3633208 : Nat := 118140960795 + 3633208 * 2 ^ 59
def prefixEnd_3633208 : Nat := 4983230072969 + 3 ^ 40 * 3633208 * 2
def baseEnd_3633208 : Nat := 1243721347840350860460791

theorem tailTrace_3633208 : CollatzResearch.WordTrace tailWord_3633208 prefixEnd_3633208 1243721347840350860460791 := by
  unfold tailWord_3633208
  simp only [CollatzResearch.WordTrace]
  refine ⟨66256991110757696685390139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88342654814343595580520185 66256991110757696685390139)
  ·
    refine ⟨99385486666136545028085209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66256991110757696685390139 99385486666136545028085209)
    ·
      refine ⟨74539114999602408771063907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99385486666136545028085209 74539114999602408771063907)
      ·
        refine ⟨111808672499403613156595861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74539114999602408771063907 111808672499403613156595861)
        ·
          refine ⟨5241031523409544366715431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 111808672499403613156595861 5241031523409544366715431)
          ·
            refine ⟨7861547285114316550073147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5241031523409544366715431 7861547285114316550073147)
            ·
              refine ⟨11792320927671474825109721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7861547285114316550073147 11792320927671474825109721)
              ·
                refine ⟨8844240695753606118832291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11792320927671474825109721 8844240695753606118832291)
                ·
                  refine ⟨13266361043630409178248437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8844240695753606118832291 13266361043630409178248437)
                  ·
                    refine ⟨1243721347840350860460791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13266361043630409178248437 1243721347840350860460791)
                    ·
                      rfl

theorem cell22_3633208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_3633208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3633208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3633208 prefixEnd_3633208 := by exact prefixLift 3633208
  have htrace : WordTrace (prefixWord ++ tailWord_3633208) baseStart_3633208 baseEnd_3633208 := by
    simpa [prefixWord, tailWord_3633208, baseEnd_3633208] using wordTrace_append hprefix tailTrace_3633208
  have hstable : (prefixWord ++ tailWord_3633208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633208).length < 2 ^ (prefixWord ++ tailWord_3633208).sum := by decide
  have hdescent : baseEnd_3633208 < baseStart_3633208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633236 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_3633236 : Nat := 118140960795 + 3633236 * 2 ^ 59
def prefixEnd_3633236 : Nat := 4983230072969 + 3 ^ 40 * 3633236 * 2
def baseEnd_3633236 : Nat := 1243730932812568120760705

theorem tailTrace_3633236 : CollatzResearch.WordTrace tailWord_3633236 prefixEnd_3633236 1243730932812568120760705 := by
  unfold tailWord_3633236
  simp only [CollatzResearch.WordTrace]
  refine ⟨66257501732706977076399781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88343335643609302768533041 66257501732706977076399781)
  ·
    refine ⟨12423281574882558201824959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66257501732706977076399781 12423281574882558201824959)
    ·
      refine ⟨18634922362323837302737439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12423281574882558201824959 18634922362323837302737439)
      ·
        refine ⟨27952383543485755954106159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18634922362323837302737439 27952383543485755954106159)
        ·
          refine ⟨41928575315228633931159239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27952383543485755954106159 41928575315228633931159239)
          ·
            refine ⟨62892862972842950896738859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41928575315228633931159239 62892862972842950896738859)
            ·
              refine ⟨94339294459264426345108289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62892862972842950896738859 94339294459264426345108289)
              ·
                refine ⟨70754470844448319758831217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94339294459264426345108289 70754470844448319758831217)
                ·
                  refine ⟨53065853133336239819123413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70754470844448319758831217 53065853133336239819123413)
                  ·
                    refine ⟨1243730932812568120760705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53065853133336239819123413 1243730932812568120760705)
                    ·
                      rfl

theorem cell22_3633236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_3633236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3633236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3633236 prefixEnd_3633236 := by exact prefixLift 3633236
  have htrace : WordTrace (prefixWord ++ tailWord_3633236) baseStart_3633236 baseEnd_3633236 := by
    simpa [prefixWord, tailWord_3633236, baseEnd_3633236] using wordTrace_append hprefix tailTrace_3633236
  have hstable : (prefixWord ++ tailWord_3633236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633236).length < 2 ^ (prefixWord ++ tailWord_3633236).sum := by decide
  have hdescent : baseEnd_3633236 < baseStart_3633236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633253 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 5, 3]
def baseStart_3633253 : Nat := 118140960795 + 3633253 * 2 ^ 59
def prefixEnd_3633253 : Nat := 4983230072969 + 3 ^ 40 * 3633253 * 2
def baseEnd_3633253 : Nat := 1243736752259985743085653

theorem tailTrace_3633253 : CollatzResearch.WordTrace tailWord_3633253 prefixEnd_3633253 1243736752259985743085653 := by
  unfold tailWord_3633253
  simp only [CollatzResearch.WordTrace]
  refine ⟨132515623506352366056168413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88343749004234910704112275 132515623506352366056168413)
  ·
    refine ⟨49693358814882137271063155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132515623506352366056168413 49693358814882137271063155)
    ·
      refine ⟨74540038222323205906594733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49693358814882137271063155 74540038222323205906594733)
      ·
        refine ⟨27952514333371202214973025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74540038222323205906594733 27952514333371202214973025)
        ·
          refine ⟨20964385750028401661229769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27952514333371202214973025 20964385750028401661229769)
          ·
            refine ⟨15723289312521301245922327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20964385750028401661229769 15723289312521301245922327)
            ·
              refine ⟨23584933968781951868883491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15723289312521301245922327 23584933968781951868883491)
              ·
                refine ⟨35377400953172927803325237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23584933968781951868883491 35377400953172927803325237)
                ·
                  refine ⟨3316631339359961981561741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35377400953172927803325237 3316631339359961981561741)
                  ·
                    refine ⟨1243736752259985743085653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3316631339359961981561741 1243736752259985743085653)
                    ·
                      rfl

theorem cell22_3633253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5, 3].length) (baseStart_3633253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3633253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3633253 prefixEnd_3633253 := by exact prefixLift 3633253
  have htrace : WordTrace (prefixWord ++ tailWord_3633253) baseStart_3633253 baseEnd_3633253 := by
    simpa [prefixWord, tailWord_3633253, baseEnd_3633253] using wordTrace_append hprefix tailTrace_3633253
  have hstable : (prefixWord ++ tailWord_3633253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633253).length < 2 ^ (prefixWord ++ tailWord_3633253).sum := by decide
  have hdescent : baseEnd_3633253 < baseStart_3633253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633283 : List Nat := [1, 1, 1, 3, 3, 3, 3, 2, 5]
def baseStart_3633283 : Nat := 118140960795 + 3633283 * 2 ^ 59
def prefixEnd_3633283 : Nat := 4983230072969 + 3 ^ 40 * 3633283 * 2
def baseEnd_3633283 : Nat := 414582340624358554945187

theorem tailTrace_3633283 : CollatzResearch.WordTrace tailWord_3633283 prefixEnd_3633283 414582340624358554945187 := by
  unfold tailWord_3633283
  simp only [CollatzResearch.WordTrace]
  refine ⟨132516717696243681179760503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88344478464162454119840335 132516717696243681179760503)
  ·
    refine ⟨198775076544365521769640755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132516717696243681179760503 198775076544365521769640755)
    ·
      refine ⟨298162614816548282654461133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198775076544365521769640755 298162614816548282654461133)
      ·
        refine ⟨111810980556205605995422925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298162614816548282654461133 111810980556205605995422925)
        ·
          refine ⟨41929117708577102248283597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111810980556205605995422925 41929117708577102248283597)
          ·
            refine ⟨15723419140716413343106349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41929117708577102248283597 15723419140716413343106349)
            ·
              refine ⟨5896282177768655003664881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15723419140716413343106349 5896282177768655003664881)
              ·
                refine ⟨4422211633326491252748661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5896282177768655003664881 4422211633326491252748661)
                ·
                  refine ⟨414582340624358554945187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4422211633326491252748661 414582340624358554945187)
                  ·
                    rfl

theorem cell22_3633283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 5].length) (baseStart_3633283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3633283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3633283 prefixEnd_3633283 := by exact prefixLift 3633283
  have htrace : WordTrace (prefixWord ++ tailWord_3633283) baseStart_3633283 baseEnd_3633283 := by
    simpa [prefixWord, tailWord_3633283, baseEnd_3633283] using wordTrace_append hprefix tailTrace_3633283
  have hstable : (prefixWord ++ tailWord_3633283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633283).length < 2 ^ (prefixWord ++ tailWord_3633283).sum := by decide
  have hdescent : baseEnd_3633283 < baseStart_3633283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633298 : List Nat := [3, 2, 3, 1, 1, 1, 1, 3, 2, 5]
def baseStart_3633298 : Nat := 118140960795 + 3633298 * 2 ^ 59
def prefixEnd_3633298 : Nat := 4983230072969 + 3 ^ 40 * 3633298 * 2
def baseEnd_3633298 : Nat := 1243752156679620625710515

theorem tailTrace_3633298 : CollatzResearch.WordTrace tailWord_3633298 prefixEnd_3633298 1243752156679620625710515 := by
  unfold tailWord_3633298
  simp only [CollatzResearch.WordTrace]
  refine ⟨33129316197797334685389137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88344843194126225827704365 33129316197797334685389137)
  ·
    refine ⟨24846987148348001014041853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33129316197797334685389137 24846987148348001014041853)
    ·
      refine ⟨9317620180630500380265695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24846987148348001014041853 9317620180630500380265695)
      ·
        refine ⟨13976430270945750570398543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9317620180630500380265695 13976430270945750570398543)
        ·
          refine ⟨20964645406418625855597815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13976430270945750570398543 20964645406418625855597815)
          ·
            refine ⟨31446968109627938783396723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20964645406418625855597815 31446968109627938783396723)
            ·
              refine ⟨47170452164441908175095085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31446968109627938783396723 47170452164441908175095085)
              ·
                refine ⟨17688919561665715565660657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47170452164441908175095085 17688919561665715565660657)
                ·
                  refine ⟨13266689671249286674245493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17688919561665715565660657 13266689671249286674245493)
                  ·
                    refine ⟨1243752156679620625710515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13266689671249286674245493 1243752156679620625710515)
                    ·
                      rfl

theorem cell22_3633298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_3633298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3633298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3633298 prefixEnd_3633298 := by exact prefixLift 3633298
  have htrace : WordTrace (prefixWord ++ tailWord_3633298) baseStart_3633298 baseEnd_3633298 := by
    simpa [prefixWord, tailWord_3633298, baseEnd_3633298] using wordTrace_append hprefix tailTrace_3633298
  have hstable : (prefixWord ++ tailWord_3633298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633298).length < 2 ^ (prefixWord ++ tailWord_3633298).sum := by decide
  have hdescent : baseEnd_3633298 < baseStart_3633298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633371 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 1, 9]
def baseStart_3633371 : Nat := 118140960795 + 3633371 * 2 ^ 59
def prefixEnd_3633371 : Nat := 4983230072969 + 3 ^ 40 * 3633371 * 2
def baseEnd_3633371 : Nat := 1243777146071472768635291

theorem tailTrace_3633371 : CollatzResearch.WordTrace tailWord_3633371 prefixEnd_3633371 1243777146071472768635291 := by
  unfold tailWord_3633371
  simp only [CollatzResearch.WordTrace]
  refine ⟨132519927319924872208963967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88346618213283248139309311 132519927319924872208963967)
  ·
    refine ⟨198779890979887308313445951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132519927319924872208963967 198779890979887308313445951)
    ·
      refine ⟨298169836469830962470168927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198779890979887308313445951 298169836469830962470168927)
      ·
        refine ⟨447254754704746443705253391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298169836469830962470168927 447254754704746443705253391)
        ·
          refine ⟨670882132057119665557880087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447254754704746443705253391 670882132057119665557880087)
          ·
            refine ⟨1006323198085679498336820131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670882132057119665557880087 1006323198085679498336820131)
            ·
              refine ⟨1509484797128519247505230197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1006323198085679498336820131 1509484797128519247505230197)
              ·
                refine ⟨141514199730798679453615331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1509484797128519247505230197 141514199730798679453615331)
                ·
                  refine ⟨212271299596198019180422997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141514199730798679453615331 212271299596198019180422997)
                  ·
                    refine ⟨1243777146071472768635291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 212271299596198019180422997 1243777146071472768635291)
                    ·
                      rfl

theorem cell22_3633371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 9].length) (baseStart_3633371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3633371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3633371 prefixEnd_3633371 := by exact prefixLift 3633371
  have htrace : WordTrace (prefixWord ++ tailWord_3633371) baseStart_3633371 baseEnd_3633371 := by
    simpa [prefixWord, tailWord_3633371, baseEnd_3633371] using wordTrace_append hprefix tailTrace_3633371
  have hstable : (prefixWord ++ tailWord_3633371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633371).length < 2 ^ (prefixWord ++ tailWord_3633371).sum := by decide
  have hdescent : baseEnd_3633371 < baseStart_3633371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633439 : List Nat := [1, 1, 2, 4, 3, 2, 2, 3, 1, 3]
def baseStart_3633439 : Nat := 118140960795 + 3633439 * 2 ^ 59
def prefixEnd_3633439 : Nat := 4983230072969 + 3 ^ 40 * 3633439 * 2
def baseEnd_3633439 : Nat := 1243800423861143257935083

theorem tailTrace_3633439 : CollatzResearch.WordTrace tailWord_3633439 prefixEnd_3633439 1243800423861143257935083 := by
  unfold tailWord_3633439
  simp only [CollatzResearch.WordTrace]
  refine ⟨132522407483678519822439371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88348271655785679881626247 132522407483678519822439371)
  ·
    refine ⟨198783611225517779733659057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132522407483678519822439371 198783611225517779733659057)
    ·
      refine ⟨149087708419138334800244293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198783611225517779733659057 149087708419138334800244293)
      ·
        refine ⟨27953945328588437775045805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149087708419138334800244293 27953945328588437775045805)
        ·
          refine ⟨10482729498220664165642177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27953945328588437775045805 10482729498220664165642177)
          ·
            refine ⟨7862047123665498124231633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10482729498220664165642177 7862047123665498124231633)
            ·
              refine ⟨5896535342749123593173725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7862047123665498124231633 5896535342749123593173725)
              ·
                refine ⟨2211200753530921347440147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5896535342749123593173725 2211200753530921347440147)
                ·
                  refine ⟨3316801130296382021160221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2211200753530921347440147 3316801130296382021160221)
                  ·
                    refine ⟨1243800423861143257935083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3316801130296382021160221 1243800423861143257935083)
                    ·
                      rfl

theorem cell22_3633439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3, 1, 3].length) (baseStart_3633439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3633439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3633439 prefixEnd_3633439 := by exact prefixLift 3633439
  have htrace : WordTrace (prefixWord ++ tailWord_3633439) baseStart_3633439 baseEnd_3633439 := by
    simpa [prefixWord, tailWord_3633439, baseEnd_3633439] using wordTrace_append hprefix tailTrace_3633439
  have hstable : (prefixWord ++ tailWord_3633439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633439).length < 2 ^ (prefixWord ++ tailWord_3633439).sum := by decide
  have hdescent : baseEnd_3633439 < baseStart_3633439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633495 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 6, 3]
def baseStart_3633495 : Nat := 118140960795 + 3633495 * 2 ^ 59
def prefixEnd_3633495 : Nat := 4983230072969 + 3 ^ 40 * 3633495 * 2
def baseEnd_3633495 : Nat := 1243819593805577778534911

theorem tailTrace_3633495 : CollatzResearch.WordTrace tailWord_3633495 prefixEnd_3633495 1243819593805577778534911 := by
  unfold tailWord_3633495
  simp only [CollatzResearch.WordTrace]
  refine ⟨132524449971475641386477939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88349633314317094257651959 132524449971475641386477939)
  ·
    refine ⟨198786674957213462079716909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132524449971475641386477939 198786674957213462079716909)
    ·
      refine ⟨74545003108955048279893841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198786674957213462079716909 74545003108955048279893841)
      ·
        refine ⟨55908752331716286209920381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74545003108955048279893841 55908752331716286209920381)
        ·
          refine ⟨20965782124393607328720143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55908752331716286209920381 20965782124393607328720143)
          ·
            refine ⟨31448673186590410993080215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20965782124393607328720143 31448673186590410993080215)
            ·
              refine ⟨47173009779885616489620323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31448673186590410993080215 47173009779885616489620323)
              ·
                refine ⟨70759514669828424734430485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47173009779885616489620323 70759514669828424734430485)
                ·
                  refine ⟨3316852250148207409426429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70759514669828424734430485 3316852250148207409426429)
                  ·
                    refine ⟨1243819593805577778534911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3316852250148207409426429 1243819593805577778534911)
                    ·
                      rfl

theorem cell22_3633495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6, 3].length) (baseStart_3633495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3633495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3633495 prefixEnd_3633495 := by exact prefixLift 3633495
  have htrace : WordTrace (prefixWord ++ tailWord_3633495) baseStart_3633495 baseEnd_3633495 := by
    simpa [prefixWord, tailWord_3633495, baseEnd_3633495] using wordTrace_append hprefix tailTrace_3633495
  have hstable : (prefixWord ++ tailWord_3633495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633495).length < 2 ^ (prefixWord ++ tailWord_3633495).sum := by decide
  have hdescent : baseEnd_3633495 < baseStart_3633495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633512 : List Nat := [2, 1, 4, 2, 2, 1, 2, 1, 4, 3]
def baseStart_3633512 : Nat := 118140960795 + 3633512 * 2 ^ 59
def prefixEnd_3633512 : Nat := 4983230072969 + 3 ^ 40 * 3633512 * 2
def baseEnd_3633512 : Nat := 1243825413252995400859859

theorem tailTrace_3633512 : CollatzResearch.WordTrace tailWord_3633512 prefixEnd_3633512 1243825413252995400859859 := by
  unfold tailWord_3633512
  simp only [CollatzResearch.WordTrace]
  refine ⟨66262535006207026644923395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88350046674942702193231193 66262535006207026644923395)
  ·
    refine ⟨99393802509310539967385093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66262535006207026644923395 99393802509310539967385093)
    ·
      refine ⟨18636337970495726243884705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99393802509310539967385093 18636337970495726243884705)
      ·
        refine ⟨13977253477871794682913529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18636337970495726243884705 13977253477871794682913529)
        ·
          refine ⟨10482940108403846012185147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13977253477871794682913529 10482940108403846012185147)
          ·
            refine ⟨15724410162605769018277721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10482940108403846012185147 15724410162605769018277721)
            ·
              refine ⟨11793307621954326763708291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15724410162605769018277721 11793307621954326763708291)
              ·
                refine ⟨17689961432931490145562437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11793307621954326763708291 17689961432931490145562437)
                ·
                  refine ⟨3316867768674654402292957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17689961432931490145562437 3316867768674654402292957)
                  ·
                    refine ⟨1243825413252995400859859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3316867768674654402292957 1243825413252995400859859)
                    ·
                      rfl

theorem cell22_3633512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_3633512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3633512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3633512 prefixEnd_3633512 := by exact prefixLift 3633512
  have htrace : WordTrace (prefixWord ++ tailWord_3633512) baseStart_3633512 baseEnd_3633512 := by
    simpa [prefixWord, tailWord_3633512, baseEnd_3633512] using wordTrace_append hprefix tailTrace_3633512
  have hstable : (prefixWord ++ tailWord_3633512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633512).length < 2 ^ (prefixWord ++ tailWord_3633512).sum := by decide
  have hdescent : baseEnd_3633512 < baseStart_3633512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633525 : List Nat := [1, 3, 4, 1, 2, 1, 1, 9]
def baseStart_3633525 : Nat := 118140960795 + 3633525 * 2 ^ 59
def prefixEnd_3633525 : Nat := 4983230072969 + 3 ^ 40 * 3633525 * 2
def baseEnd_3633525 : Nat := 138203318157629744476091

theorem tailTrace_3633525 : CollatzResearch.WordTrace tailWord_3633525 prefixEnd_3633525 138203318157629744476091 := by
  unfold tailWord_3633525
  simp only [CollatzResearch.WordTrace]
  refine ⟨132525544161366956510070029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88350362774244637673380019 132525544161366956510070029)
  ·
    refine ⟨49697079060512608691276261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132525544161366956510070029 49697079060512608691276261)
    ·
      refine ⟨9318202323846114129614299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49697079060512608691276261 9318202323846114129614299)
      ·
        refine ⟨13977303485769171194421449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9318202323846114129614299 13977303485769171194421449)
        ·
          refine ⟨10482977614326878395816087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13977303485769171194421449 10482977614326878395816087)
          ·
            refine ⟨15724466421490317593724131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10482977614326878395816087 15724466421490317593724131)
            ·
              refine ⟨23586699632235476390586197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15724466421490317593724131 23586699632235476390586197)
              ·
                refine ⟨138203318157629744476091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23586699632235476390586197 138203318157629744476091)
                ·
                  rfl

theorem cell22_3633525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 9].length) (baseStart_3633525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3633525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3633525 prefixEnd_3633525 := by exact prefixLift 3633525
  have htrace : WordTrace (prefixWord ++ tailWord_3633525) baseStart_3633525 baseEnd_3633525 := by
    simpa [prefixWord, tailWord_3633525, baseEnd_3633525] using wordTrace_append hprefix tailTrace_3633525
  have hstable : (prefixWord ++ tailWord_3633525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633525).length < 2 ^ (prefixWord ++ tailWord_3633525).sum := by decide
  have hdescent : baseEnd_3633525 < baseStart_3633525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633585 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 1, 7]
def baseStart_3633585 : Nat := 118140960795 + 3633585 * 2 ^ 59
def prefixEnd_3633585 : Nat := 4983230072969 + 3 ^ 40 * 3633585 * 2
def baseEnd_3633585 : Nat := 1243850402644847543784635

theorem tailTrace_3633585 : CollatzResearch.WordTrace tailWord_3633585 prefixEnd_3633585 1243850402644847543784635 := by
  unfold tailWord_3633585
  simp only [CollatzResearch.WordTrace]
  refine ⟨132527732541149586757254209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88351821694099724504836139 132527732541149586757254209)
  ·
    refine ⟨99395799405862190067940657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132527732541149586757254209 99395799405862190067940657)
    ·
      refine ⟨74546849554396642550955493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99395799405862190067940657 74546849554396642550955493)
      ·
        refine ⟨13977534291449370478304155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74546849554396642550955493 13977534291449370478304155)
        ·
          refine ⟨20966301437174055717456233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13977534291449370478304155 20966301437174055717456233)
          ·
            refine ⟨15724726077880541788092175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20966301437174055717456233 15724726077880541788092175)
            ·
              refine ⟨23587089116820812682138263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15724726077880541788092175 23587089116820812682138263)
              ·
                refine ⟨35380633675231219023207395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23587089116820812682138263 35380633675231219023207395)
                ·
                  refine ⟨53070950512846828534811093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35380633675231219023207395 53070950512846828534811093)
                  ·
                    refine ⟨1243850402644847543784635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53070950512846828534811093 1243850402644847543784635)
                    ·
                      rfl

theorem cell22_3633585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_3633585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3633585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3633585 prefixEnd_3633585 := by exact prefixLift 3633585
  have htrace : WordTrace (prefixWord ++ tailWord_3633585) baseStart_3633585 baseEnd_3633585 := by
    simpa [prefixWord, tailWord_3633585, baseEnd_3633585] using wordTrace_append hprefix tailTrace_3633585
  have hstable : (prefixWord ++ tailWord_3633585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633585).length < 2 ^ (prefixWord ++ tailWord_3633585).sum := by decide
  have hdescent : baseEnd_3633585 < baseStart_3633585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633632 : List Nat := [2, 1, 1, 3, 1, 1, 3, 6, 4]
def baseStart_3633632 : Nat := 118140960795 + 3633632 * 2 ^ 59
def prefixEnd_3633632 : Nat := 4983230072969 + 3 ^ 40 * 3633632 * 2
def baseEnd_3633632 : Nat := 414622163901785029286497

theorem tailTrace_3633632 : CollatzResearch.WordTrace tailWord_3633632 prefixEnd_3633632 414622163901785029286497 := by
  unfold tailWord_3633632
  simp only [CollatzResearch.WordTrace]
  refine ⟨66264723385989656892107575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88352964514652875856143433 66264723385989656892107575)
  ·
    refine ⟨99397085078984485338161363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66264723385989656892107575 99397085078984485338161363)
    ·
      refine ⟨149095627618476728007242045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99397085078984485338161363 149095627618476728007242045)
      ·
        refine ⟨55910860356928773002715767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149095627618476728007242045 55910860356928773002715767)
        ·
          refine ⟨83866290535393159504073651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55910860356928773002715767 83866290535393159504073651)
          ·
            refine ⟨125799435803089739256110477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83866290535393159504073651 125799435803089739256110477)
            ·
              refine ⟨47174788426158652221041429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125799435803089739256110477 47174788426158652221041429)
              ·
                refine ⟨2211318207476186822861317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47174788426158652221041429 2211318207476186822861317)
                ·
                  refine ⟨414622163901785029286497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2211318207476186822861317 414622163901785029286497)
                  ·
                    rfl

theorem cell22_3633632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6, 4].length) (baseStart_3633632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3633632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3633632 prefixEnd_3633632 := by exact prefixLift 3633632
  have htrace : WordTrace (prefixWord ++ tailWord_3633632) baseStart_3633632 baseEnd_3633632 := by
    simpa [prefixWord, tailWord_3633632, baseEnd_3633632] using wordTrace_append hprefix tailTrace_3633632
  have hstable : (prefixWord ++ tailWord_3633632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633632).length < 2 ^ (prefixWord ++ tailWord_3633632).sum := by decide
  have hdescent : baseEnd_3633632 < baseStart_3633632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633752 : List Nat := [2, 1, 2, 2, 1, 2, 3, 2, 3, 4]
def baseStart_3633752 : Nat := 118140960795 + 3633752 * 2 ^ 59
def prefixEnd_3633752 : Nat := 4983230072969 + 3 ^ 40 * 3633752 * 2
def baseEnd_3633752 : Nat := 1243907570157714774859123

theorem tailTrace_3633752 : CollatzResearch.WordTrace tailWord_3633752 prefixEnd_3633752 1243907570157714774859123 := by
  unfold tailWord_3633752
  simp only [CollatzResearch.WordTrace]
  refine ⟨66266911765772287139291755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88355882354363049519055673 66266911765772287139291755)
  ·
    refine ⟨99400367648658430708937633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66266911765772287139291755 99400367648658430708937633)
    ·
      refine ⟨74550275736493823031703225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99400367648658430708937633 74550275736493823031703225)
      ·
        refine ⟨55912706802370367273777419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74550275736493823031703225 55912706802370367273777419)
        ·
          refine ⟨83869060203555550910666129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55912706802370367273777419 83869060203555550910666129)
          ·
            refine ⟨62901795152666663182999597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83869060203555550910666129 62901795152666663182999597)
            ·
              refine ⟨23588173182249998693624849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62901795152666663182999597 23588173182249998693624849)
              ·
                refine ⟨17691129886687499020218637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23588173182249998693624849 17691129886687499020218637)
                ·
                  refine ⟨6634173707507812132581989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17691129886687499020218637 6634173707507812132581989)
                  ·
                    refine ⟨1243907570157714774859123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6634173707507812132581989 1243907570157714774859123)
                    ·
                      rfl

theorem cell22_3633752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_3633752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3633752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3633752 prefixEnd_3633752 := by exact prefixLift 3633752
  have htrace : WordTrace (prefixWord ++ tailWord_3633752) baseStart_3633752 baseEnd_3633752 := by
    simpa [prefixWord, tailWord_3633752, baseEnd_3633752] using wordTrace_append hprefix tailTrace_3633752
  have hstable : (prefixWord ++ tailWord_3633752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633752).length < 2 ^ (prefixWord ++ tailWord_3633752).sum := by decide
  have hdescent : baseEnd_3633752 < baseStart_3633752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633799 : List Nat := [1, 1, 4, 2, 1, 2, 3, 1, 4, 3]
def baseStart_3633799 : Nat := 118140960795 + 3633799 * 2 ^ 59
def prefixEnd_3633799 : Nat := 4983230072969 + 3 ^ 40 * 3633799 * 2
def baseEnd_3633799 : Nat := 1243923659218222318933979

theorem tailTrace_3633799 : CollatzResearch.WordTrace tailWord_3633799 prefixEnd_3633799 1243923659218222318933979 := by
  unfold tailWord_3633799
  simp only [CollatzResearch.WordTrace]
  refine ⟨132535537762374301305544451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88357025174916200870362967 132535537762374301305544451)
  ·
    refine ⟨198803306643561451958316677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132535537762374301305544451 198803306643561451958316677)
    ·
      refine ⟨37275619995667772242184377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198803306643561451958316677 37275619995667772242184377)
      ·
        refine ⟨27956714996750829181638283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37275619995667772242184377 27956714996750829181638283)
        ·
          refine ⟨41935072495126243772457425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27956714996750829181638283 41935072495126243772457425)
          ·
            refine ⟨31451304371344682829343069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41935072495126243772457425 31451304371344682829343069)
            ·
              refine ⟨11794239139254256061003651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31451304371344682829343069 11794239139254256061003651)
              ·
                refine ⟨17691358708881384091505477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11794239139254256061003651 17691358708881384091505477)
                ·
                  refine ⟨3317129757915259517157277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17691358708881384091505477 3317129757915259517157277)
                  ·
                    refine ⟨1243923659218222318933979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3317129757915259517157277 1243923659218222318933979)
                    ·
                      rfl

theorem cell22_3633799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_3633799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3633799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3633799 prefixEnd_3633799 := by exact prefixLift 3633799
  have htrace : WordTrace (prefixWord ++ tailWord_3633799) baseStart_3633799 baseEnd_3633799 := by
    simpa [prefixWord, tailWord_3633799, baseEnd_3633799] using wordTrace_append hprefix tailTrace_3633799
  have hstable : (prefixWord ++ tailWord_3633799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633799).length < 2 ^ (prefixWord ++ tailWord_3633799).sum := by decide
  have hdescent : baseEnd_3633799 < baseStart_3633799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633842 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 1, 8]
def baseStart_3633842 : Nat := 118140960795 + 3633842 * 2 ^ 59
def prefixEnd_3633842 : Nat := 4983230072969 + 3 ^ 40 * 3633842 * 2
def baseEnd_3633842 : Nat := 1243938378996984540108847

theorem tailTrace_3633842 : CollatzResearch.WordTrace tailWord_3633842 prefixEnd_3633842 1243938378996984540108847 := by
  unfold tailWord_3633842
  simp only [CollatzResearch.WordTrace]
  refine ⟨33134276525304629912339945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88358070734145679766239853 33134276525304629912339945)
  ·
    refine ⟨24850707393978472434254959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33134276525304629912339945 24850707393978472434254959)
    ·
      refine ⟨37276061090967708651382439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24850707393978472434254959 37276061090967708651382439)
      ·
        refine ⟨55914091636451562977073659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37276061090967708651382439 55914091636451562977073659)
        ·
          refine ⟨83871137454677344465610489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55914091636451562977073659 83871137454677344465610489)
          ·
            refine ⟨62903353091008008349207867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83871137454677344465610489 62903353091008008349207867)
            ·
              refine ⟨94355029636512012523811801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62903353091008008349207867 94355029636512012523811801)
              ·
                refine ⟨70766272227384009392858851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94355029636512012523811801 70766272227384009392858851)
                ·
                  refine ⟨106149408341076014089288277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70766272227384009392858851 106149408341076014089288277)
                  ·
                    refine ⟨1243938378996984540108847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106149408341076014089288277 1243938378996984540108847)
                    ·
                      rfl

theorem cell22_3633842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_3633842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3633842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3633842 prefixEnd_3633842 := by exact prefixLift 3633842
  have htrace : WordTrace (prefixWord ++ tailWord_3633842) baseStart_3633842 baseEnd_3633842 := by
    simpa [prefixWord, tailWord_3633842, baseEnd_3633842] using wordTrace_append hprefix tailTrace_3633842
  have hstable : (prefixWord ++ tailWord_3633842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633842).length < 2 ^ (prefixWord ++ tailWord_3633842).sum := by decide
  have hdescent : baseEnd_3633842 < baseStart_3633842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633872 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 6, 5]
def baseStart_3633872 : Nat := 118140960795 + 3633872 * 2 ^ 59
def prefixEnd_3633872 : Nat := 4983230072969 + 3 ^ 40 * 3633872 * 2
def baseEnd_3633872 : Nat := 1243948648610074461858755

theorem tailTrace_3633872 : CollatzResearch.WordTrace tailWord_3633872 prefixEnd_3633872 1243948648610074461858755 := by
  unfold tailWord_3633872
  simp only [CollatzResearch.WordTrace]
  refine ⟨66269100145554917386475935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88358800194073223181967913 66269100145554917386475935)
  ·
    refine ⟨99403650218332376079713903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66269100145554917386475935 99403650218332376079713903)
    ·
      refine ⟨149105475327498564119570855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99403650218332376079713903 149105475327498564119570855)
      ·
        refine ⟨223658212991247846179356283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149105475327498564119570855 223658212991247846179356283)
        ·
          refine ⟨335487319486871769269034425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223658212991247846179356283 335487319486871769269034425)
          ·
            refine ⟨251615489615153826951775819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335487319486871769269034425 251615489615153826951775819)
            ·
              refine ⟨377423234422730740427663729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251615489615153826951775819 377423234422730740427663729)
              ·
                refine ⟨283067425817048055320747797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 377423234422730740427663729 283067425817048055320747797)
                ·
                  refine ⟨13268785585174127593160053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 283067425817048055320747797 13268785585174127593160053)
                  ·
                    refine ⟨1243948648610074461858755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13268785585174127593160053 1243948648610074461858755)
                    ·
                      rfl

theorem cell22_3633872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 6, 5].length) (baseStart_3633872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3633872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3633872 prefixEnd_3633872 := by exact prefixLift 3633872
  have htrace : WordTrace (prefixWord ++ tailWord_3633872) baseStart_3633872 baseEnd_3633872 := by
    simpa [prefixWord, tailWord_3633872, baseEnd_3633872] using wordTrace_append hprefix tailTrace_3633872
  have hstable : (prefixWord ++ tailWord_3633872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633872).length < 2 ^ (prefixWord ++ tailWord_3633872).sum := by decide
  have hdescent : baseEnd_3633872 < baseStart_3633872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633985 : List Nat := [1, 2, 5, 3, 1, 2, 1, 1, 1, 5]
def baseStart_3633985 : Nat := 118140960795 + 3633985 * 2 ^ 59
def prefixEnd_3633985 : Nat := 4983230072969 + 3 ^ 40 * 3633985 * 2
def baseEnd_3633985 : Nat := 1243987330819379833783409

theorem tailTrace_3633985 : CollatzResearch.WordTrace tailWord_3633985 prefixEnd_3633985 1243987330819379833783409 := by
  unfold tailWord_3633985
  simp only [CollatzResearch.WordTrace]
  refine ⟨132542321739700455071815409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88361547826466970047876939 132542321739700455071815409)
  ·
    refine ⟨99406741304775341303861557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132542321739700455071815409 99406741304775341303861557)
    ·
      refine ⟨9319381997322688247237021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99406741304775341303861557 9319381997322688247237021)
      ·
        refine ⟨3494768248996008092713883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9319381997322688247237021 3494768248996008092713883)
        ·
          refine ⟨5242152373494012139070825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3494768248996008092713883 5242152373494012139070825)
          ·
            refine ⟨3931614280120509104303119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5242152373494012139070825 3931614280120509104303119)
            ·
              refine ⟨5897421420180763656454679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3931614280120509104303119 5897421420180763656454679)
              ·
                refine ⟨8846132130271145484682019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5897421420180763656454679 8846132130271145484682019)
                ·
                  refine ⟨13269198195406718227023029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8846132130271145484682019 13269198195406718227023029)
                  ·
                    refine ⟨1243987330819379833783409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13269198195406718227023029 1243987330819379833783409)
                    ·
                      rfl

theorem cell22_3633985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_3633985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3633985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3633985 prefixEnd_3633985 := by exact prefixLift 3633985
  have htrace : WordTrace (prefixWord ++ tailWord_3633985) baseStart_3633985 baseEnd_3633985 := by
    simpa [prefixWord, tailWord_3633985, baseEnd_3633985] using wordTrace_append hprefix tailTrace_3633985
  have hstable : (prefixWord ++ tailWord_3633985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633985).length < 2 ^ (prefixWord ++ tailWord_3633985).sum := by decide
  have hdescent : baseEnd_3633985 < baseStart_3633985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634009 : List Nat := [1, 2, 1, 2, 2, 4, 1, 2, 7]
def baseStart_3634009 : Nat := 118140960795 + 3634009 * 2 ^ 59
def prefixEnd_3634009 : Nat := 4983230072969 + 3 ^ 40 * 3634009 * 2
def baseEnd_3634009 : Nat := 414665182169950590394445

theorem tailTrace_3634009 : CollatzResearch.WordTrace tailWord_3634009 prefixEnd_3634009 414665182169950590394445 := by
  unfold tailWord_3634009
  simp only [CollatzResearch.WordTrace]
  refine ⟨132543197091613507170689081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88362131394409004780459387 132543197091613507170689081)
  ·
    refine ⟨99407397818710130378016811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132543197091613507170689081 99407397818710130378016811)
    ·
      refine ⟨149111096728065195567025217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99407397818710130378016811 149111096728065195567025217)
      ·
        refine ⟨111833322546048896675268913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149111096728065195567025217 111833322546048896675268913)
        ·
          refine ⟨83874991909536672506451685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111833322546048896675268913 83874991909536672506451685)
          ·
            refine ⟨15726560983038126094959691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83874991909536672506451685 15726560983038126094959691)
            ·
              refine ⟨23589841474557189142439537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15726560983038126094959691 23589841474557189142439537)
              ·
                refine ⟨17692381105917891856829653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23589841474557189142439537 17692381105917891856829653)
                ·
                  refine ⟨414665182169950590394445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17692381105917891856829653 414665182169950590394445)
                  ·
                    rfl

theorem cell22_3634009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 7].length) (baseStart_3634009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634009 prefixEnd_3634009 := by exact prefixLift 3634009
  have htrace : WordTrace (prefixWord ++ tailWord_3634009) baseStart_3634009 baseEnd_3634009 := by
    simpa [prefixWord, tailWord_3634009, baseEnd_3634009] using wordTrace_append hprefix tailTrace_3634009
  have hstable : (prefixWord ++ tailWord_3634009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634009).length < 2 ^ (prefixWord ++ tailWord_3634009).sum := by decide
  have hdescent : baseEnd_3634009 < baseStart_3634009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634099 : List Nat := [1, 1, 1, 2, 3, 1, 2, 11]
def baseStart_3634099 : Nat := 118140960795 + 3634099 * 2 ^ 59
def prefixEnd_3634099 : Nat := 4983230072969 + 3 ^ 40 * 3634099 * 2
def baseEnd_3634099 : Nat := 138225150594346837381451

theorem tailTrace_3634099 : CollatzResearch.WordTrace tailWord_3634099 prefixEnd_3634099 138225150594346837381451 := by
  unfold tailWord_3634099
  simp only [CollatzResearch.WordTrace]
  refine ⟨132546479661287452541465351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88364319774191635027643567 132546479661287452541465351)
  ·
    refine ⟨198819719491931178812198027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132546479661287452541465351 198819719491931178812198027)
    ·
      refine ⟨298229579237896768218297041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198819719491931178812198027 298229579237896768218297041)
      ·
        refine ⟨223672184428422576163722781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298229579237896768218297041 223672184428422576163722781)
        ·
          refine ⟨83877069160658466061396043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223672184428422576163722781 83877069160658466061396043)
          ·
            refine ⟨125815603740987699092094065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83877069160658466061396043 125815603740987699092094065)
            ·
              refine ⟨94361702805740774319070549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125815603740987699092094065 94361702805740774319070549)
              ·
                refine ⟨138225150594346837381451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 94361702805740774319070549 138225150594346837381451)
                ·
                  rfl

theorem cell22_3634099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 11].length) (baseStart_3634099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634099 prefixEnd_3634099 := by exact prefixLift 3634099
  have htrace : WordTrace (prefixWord ++ tailWord_3634099) baseStart_3634099 baseEnd_3634099 := by
    simpa [prefixWord, tailWord_3634099, baseEnd_3634099] using wordTrace_append hprefix tailTrace_3634099
  have hstable : (prefixWord ++ tailWord_3634099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634099).length < 2 ^ (prefixWord ++ tailWord_3634099).sum := by decide
  have hdescent : baseEnd_3634099 < baseStart_3634099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634101 : List Nat := [1, 3, 3, 2, 1, 1, 2, 2, 1, 6]
def baseStart_3634101 : Nat := 118140960795 + 3634101 * 2 ^ 59
def prefixEnd_3634101 : Nat := 4983230072969 + 3 ^ 40 * 3634101 * 2
def baseEnd_3634101 : Nat := 1244027039989994197883053

theorem tailTrace_3634101 : CollatzResearch.WordTrace tailWord_3634101 prefixEnd_3634101 1244027039989994197883053 := by
  unfold tailWord_3634101
  simp only [CollatzResearch.WordTrace]
  refine ⟨132546552607280206883038157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88364368404853471255358771 132546552607280206883038157)
  ·
    refine ⟨49704957227730077581139309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132546552607280206883038157 49704957227730077581139309)
    ·
      refine ⟨18639358960398779092927241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49704957227730077581139309 18639358960398779092927241)
      ·
        refine ⟨13979519220299084319695431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18639358960398779092927241 13979519220299084319695431)
        ·
          refine ⟨20969278830448626479543147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13979519220299084319695431 20969278830448626479543147)
          ·
            refine ⟨31453918245672939719314721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20969278830448626479543147 31453918245672939719314721)
            ·
              refine ⟨23590438684254704789486041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31453918245672939719314721 23590438684254704789486041)
              ·
                refine ⟨17692829013191028592114531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23590438684254704789486041 17692829013191028592114531)
                ·
                  refine ⟨26539243519786542888171797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17692829013191028592114531 26539243519786542888171797)
                  ·
                    refine ⟨1244027039989994197883053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26539243519786542888171797 1244027039989994197883053)
                    ·
                      rfl

theorem cell22_3634101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_3634101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634101 prefixEnd_3634101 := by exact prefixLift 3634101
  have htrace : WordTrace (prefixWord ++ tailWord_3634101) baseStart_3634101 baseEnd_3634101 := by
    simpa [prefixWord, tailWord_3634101, baseEnd_3634101] using wordTrace_append hprefix tailTrace_3634101
  have hstable : (prefixWord ++ tailWord_3634101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634101).length < 2 ^ (prefixWord ++ tailWord_3634101).sum := by decide
  have hdescent : baseEnd_3634101 < baseStart_3634101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634103 : List Nat := [1, 1, 3, 1, 3, 1, 4, 3, 2, 3]
def baseStart_3634103 : Nat := 118140960795 + 3634103 * 2 ^ 59
def prefixEnd_3634103 : Nat := 4983230072969 + 3 ^ 40 * 3634103 * 2
def baseEnd_3634103 : Nat := 1244027724630866859333047

theorem tailTrace_3634103 : CollatzResearch.WordTrace tailWord_3634103 prefixEnd_3634103 1244027724630866859333047 := by
  unfold tailWord_3634103
  simp only [CollatzResearch.WordTrace]
  refine ⟨132546625553272961224610963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88364417035515307483073975 132546625553272961224610963)
  ·
    refine ⟨198819938329909441836916445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132546625553272961224610963 198819938329909441836916445)
    ·
      refine ⟨74557476873716040688843667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198819938329909441836916445 74557476873716040688843667)
      ·
        refine ⟨111836215310574061033265501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74557476873716040688843667 111836215310574061033265501)
        ·
          refine ⟨41938580741465272887474563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111836215310574061033265501 41938580741465272887474563)
          ·
            refine ⟨62907871112197909331211845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41938580741465272887474563 62907871112197909331211845)
            ·
              refine ⟨11795225833537107999602221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62907871112197909331211845 11795225833537107999602221)
              ·
                refine ⟨4423209687576415499850833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11795225833537107999602221 4423209687576415499850833)
                ·
                  refine ⟨3317407265682311624888125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4423209687576415499850833 3317407265682311624888125)
                  ·
                    refine ⟨1244027724630866859333047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3317407265682311624888125 1244027724630866859333047)
                    ·
                      rfl

theorem cell22_3634103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2, 3].length) (baseStart_3634103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634103 prefixEnd_3634103 := by exact prefixLift 3634103
  have htrace : WordTrace (prefixWord ++ tailWord_3634103) baseStart_3634103 baseEnd_3634103 := by
    simpa [prefixWord, tailWord_3634103, baseEnd_3634103] using wordTrace_append hprefix tailTrace_3634103
  have hstable : (prefixWord ++ tailWord_3634103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634103).length < 2 ^ (prefixWord ++ tailWord_3634103).sum := by decide
  have hdescent : baseEnd_3634103 < baseStart_3634103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634199 : List Nat := [1, 1, 3, 5, 1, 2, 3, 2, 1, 3]
def baseStart_3634199 : Nat := 118140960795 + 3634199 * 2 ^ 59
def prefixEnd_3634199 : Nat := 4983230072969 + 3 ^ 40 * 3634199 * 2
def baseEnd_3634199 : Nat := 1244060587392754608932753

theorem tailTrace_3634199 : CollatzResearch.WordTrace tailWord_3634199 prefixEnd_3634199 1244060587392754608932753 := by
  unfold tailWord_3634199
  simp only [CollatzResearch.WordTrace]
  refine ⟨132550126960925169620105651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88366751307283446413403767 132550126960925169620105651)
  ·
    refine ⟨198825190441387754430158477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132550126960925169620105651 198825190441387754430158477)
    ·
      refine ⟨74559446415520407911309429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198825190441387754430158477 74559446415520407911309429)
      ·
        refine ⟨6989948101455038241685259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74559446415520407911309429 6989948101455038241685259)
        ·
          refine ⟨10484922152182557362527889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6989948101455038241685259 10484922152182557362527889)
          ·
            refine ⟨7863691614136918021895917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10484922152182557362527889 7863691614136918021895917)
            ·
              refine ⟨2948884355301344258210969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7863691614136918021895917 2948884355301344258210969)
              ·
                refine ⟨2211663266476008193658227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2948884355301344258210969 2211663266476008193658227)
                ·
                  refine ⟨3317494899714012290487341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2211663266476008193658227 3317494899714012290487341)
                  ·
                    refine ⟨1244060587392754608932753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3317494899714012290487341 1244060587392754608932753)
                    ·
                      rfl

theorem cell22_3634199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2, 1, 3].length) (baseStart_3634199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634199 prefixEnd_3634199 := by exact prefixLift 3634199
  have htrace : WordTrace (prefixWord ++ tailWord_3634199) baseStart_3634199 baseEnd_3634199 := by
    simpa [prefixWord, tailWord_3634199, baseEnd_3634199] using wordTrace_append hprefix tailTrace_3634199
  have hstable : (prefixWord ++ tailWord_3634199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634199).length < 2 ^ (prefixWord ++ tailWord_3634199).sum := by decide
  have hdescent : baseEnd_3634199 < baseStart_3634199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634212 : List Nat := [2, 3, 1, 4, 1, 3, 2, 1, 5]
def baseStart_3634212 : Nat := 118140960795 + 3634212 * 2 ^ 59
def prefixEnd_3634212 : Nat := 4983230072969 + 3 ^ 40 * 3634212 * 2
def baseEnd_3634212 : Nat := 414688345852808969452571

theorem tailTrace_3634212 : CollatzResearch.WordTrace tailWord_3634212 prefixEnd_3634212 414688345852808969452571 := by
  unfold tailWord_3634212
  simp only [CollatzResearch.WordTrace]
  refine ⟨66275300554939036420164445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88367067406585381893552593 66275300554939036420164445)
  ·
    refine ⟨24853237708102138657561667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66275300554939036420164445 24853237708102138657561667)
    ·
      refine ⟨37279856562153207986342501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24853237708102138657561667 37279856562153207986342501)
      ·
        refine ⟨6989973105403726497439219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37279856562153207986342501 6989973105403726497439219)
        ·
          refine ⟨10484959658105589746158829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6989973105403726497439219 10484959658105589746158829)
          ·
            refine ⟨3931859871789596154809561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10484959658105589746158829 3931859871789596154809561)
            ·
              refine ⟨2948894903842197116107171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3931859871789596154809561 2948894903842197116107171)
              ·
                refine ⟨4423342355763295674160757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2948894903842197116107171 4423342355763295674160757)
                ·
                  refine ⟨414688345852808969452571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4423342355763295674160757 414688345852808969452571)
                  ·
                    rfl

theorem cell22_3634212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_3634212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634212 prefixEnd_3634212 := by exact prefixLift 3634212
  have htrace : WordTrace (prefixWord ++ tailWord_3634212) baseStart_3634212 baseEnd_3634212 := by
    simpa [prefixWord, tailWord_3634212, baseEnd_3634212] using wordTrace_append hprefix tailTrace_3634212
  have hstable : (prefixWord ++ tailWord_3634212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634212).length < 2 ^ (prefixWord ++ tailWord_3634212).sum := by decide
  have hdescent : baseEnd_3634212 < baseStart_3634212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634285 : List Nat := [1, 5, 1, 1, 2, 3, 3, 6]
def baseStart_3634285 : Nat := 118140960795 + 3634285 * 2 ^ 59
def prefixEnd_3634285 : Nat := 4983230072969 + 3 ^ 40 * 3634285 * 2
def baseEnd_3634285 : Nat := 138232225216697672364721

theorem tailTrace_3634285 : CollatzResearch.WordTrace tailWord_3634285 prefixEnd_3634285 138232225216697672364721 := by
  unfold tailWord_3634285
  simp only [CollatzResearch.WordTrace]
  refine ⟨132553263638613606307736309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88368842425742404205157539 132553263638613606307736309)
  ·
    refine ⟨12426868466120025591350279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132553263638613606307736309 12426868466120025591350279)
    ·
      refine ⟨18640302699180038387025419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12426868466120025591350279 18640302699180038387025419)
      ·
        refine ⟨27960454048770057580538129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18640302699180038387025419 27960454048770057580538129)
        ·
          refine ⟨20970340536577543185403597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27960454048770057580538129 20970340536577543185403597)
          ·
            refine ⟨7863877701216578694526349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20970340536577543185403597 7863877701216578694526349)
            ·
              refine ⟨2948954137956217010447381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7863877701216578694526349 2948954137956217010447381)
              ·
                refine ⟨138232225216697672364721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2948954137956217010447381 138232225216697672364721)
                ·
                  rfl

theorem cell22_3634285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 6].length) (baseStart_3634285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634285 prefixEnd_3634285 := by exact prefixLift 3634285
  have htrace : WordTrace (prefixWord ++ tailWord_3634285) baseStart_3634285 baseEnd_3634285 := by
    simpa [prefixWord, tailWord_3634285, baseEnd_3634285] using wordTrace_append hprefix tailTrace_3634285
  have hstable : (prefixWord ++ tailWord_3634285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634285).length < 2 ^ (prefixWord ++ tailWord_3634285).sum := by decide
  have hdescent : baseEnd_3634285 < baseStart_3634285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634313 : List Nat := [1, 2, 1, 1, 4, 4, 1, 1, 7]
def baseStart_3634313 : Nat := 118140960795 + 3634313 * 2 ^ 59
def prefixEnd_3634313 : Nat := 4983230072969 + 3 ^ 40 * 3634313 * 2
def baseEnd_3634313 : Nat := 414699870640832103860801

theorem tailTrace_3634313 : CollatzResearch.WordTrace tailWord_3634313 prefixEnd_3634313 414699870640832103860801 := by
  unfold tailWord_3634313
  simp only [CollatzResearch.WordTrace]
  refine ⟨132554284882512167089755593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88369523255008111393170395 132554284882512167089755593)
  ·
    refine ⟨99415713661884125317316695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132554284882512167089755593 99415713661884125317316695)
    ·
      refine ⟨149123570492826187975975043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99415713661884125317316695 149123570492826187975975043)
      ·
        refine ⟨223685355739239281963962565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149123570492826187975975043 223685355739239281963962565)
        ·
          refine ⟨41941004201107365368242981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223685355739239281963962565 41941004201107365368242981)
          ·
            refine ⟨7863938287707631006545559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41941004201107365368242981 7863938287707631006545559)
            ·
              refine ⟨11795907431561446509818339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7863938287707631006545559 11795907431561446509818339)
              ·
                refine ⟨17693861147342169764727509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11795907431561446509818339 17693861147342169764727509)
                ·
                  refine ⟨414699870640832103860801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17693861147342169764727509 414699870640832103860801)
                  ·
                    rfl

theorem cell22_3634313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 7].length) (baseStart_3634313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634313 prefixEnd_3634313 := by exact prefixLift 3634313
  have htrace : WordTrace (prefixWord ++ tailWord_3634313) baseStart_3634313 baseEnd_3634313 := by
    simpa [prefixWord, tailWord_3634313, baseEnd_3634313] using wordTrace_append hprefix tailTrace_3634313
  have hstable : (prefixWord ++ tailWord_3634313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634313).length < 2 ^ (prefixWord ++ tailWord_3634313).sum := by decide
  have hdescent : baseEnd_3634313 < baseStart_3634313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634375 : List Nat := [1, 1, 4, 1, 1, 1, 1, 8, 4]
def baseStart_3634375 : Nat := 118140960795 + 3634375 * 2 ^ 59
def prefixEnd_3634375 : Nat := 4983230072969 + 3 ^ 40 * 3634375 * 2
def baseEnd_3634375 : Nat := 414706945263182938844071

theorem tailTrace_3634375 : CollatzResearch.WordTrace tailWord_3634375 prefixEnd_3634375 414706945263182938844071 := by
  unfold tailWord_3634375
  simp only [CollatzResearch.WordTrace]
  refine ⟨132556546208287551678512579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88371030805525034452341719 132556546208287551678512579)
  ·
    refine ⟨198834819312431327517768869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132556546208287551678512579 198834819312431327517768869)
    ·
      refine ⟨37281528621080873909581663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198834819312431327517768869 37281528621080873909581663)
      ·
        refine ⟨55922292931621310864372495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37281528621080873909581663 55922292931621310864372495)
        ·
          refine ⟨83883439397431966296558743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55922292931621310864372495 83883439397431966296558743)
          ·
            refine ⟨125825159096147949444838115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83883439397431966296558743 125825159096147949444838115)
            ·
              refine ⟨188737738644221924167257173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125825159096147949444838115 188737738644221924167257173)
              ·
                refine ⟨2211770374736975673835045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 188737738644221924167257173 2211770374736975673835045)
                ·
                  refine ⟨414706945263182938844071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2211770374736975673835045 414706945263182938844071)
                  ·
                    rfl

theorem cell22_3634375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8, 4].length) (baseStart_3634375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634375 prefixEnd_3634375 := by exact prefixLift 3634375
  have htrace : WordTrace (prefixWord ++ tailWord_3634375) baseStart_3634375 baseEnd_3634375 := by
    simpa [prefixWord, tailWord_3634375, baseEnd_3634375] using wordTrace_append hprefix tailTrace_3634375
  have hstable : (prefixWord ++ tailWord_3634375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634375).length < 2 ^ (prefixWord ++ tailWord_3634375).sum := by decide
  have hdescent : baseEnd_3634375 < baseStart_3634375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634407 : List Nat := [1, 1, 5, 3, 2, 1, 1, 2, 1, 5]
def baseStart_3634407 : Nat := 118140960795 + 3634407 * 2 ^ 59
def prefixEnd_3634407 : Nat := 4983230072969 + 3 ^ 40 * 3634407 * 2
def baseEnd_3634407 : Nat := 1244131790043511399732115

theorem tailTrace_3634407 : CollatzResearch.WordTrace tailWord_3634407 prefixEnd_3634407 1244131790043511399732115 := by
  unfold tailWord_3634407
  simp only [CollatzResearch.WordTrace]
  refine ⟨132557713344171621143677475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88371808896114414095784983 132557713344171621143677475)
  ·
    refine ⟨198836570016257431715516213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132557713344171621143677475 198836570016257431715516213)
    ·
      refine ⟨18640928439024134223329645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198836570016257431715516213 18640928439024134223329645)
      ·
        refine ⟨6990348164634050333748617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18640928439024134223329645 6990348164634050333748617)
        ·
          refine ⟨5242761123475537750311463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6990348164634050333748617 5242761123475537750311463)
          ·
            refine ⟨7864141685213306625467195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5242761123475537750311463 7864141685213306625467195)
            ·
              refine ⟨11796212527819959938200793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7864141685213306625467195 11796212527819959938200793)
              ·
                refine ⟨8847159395864969953650595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11796212527819959938200793 8847159395864969953650595)
                ·
                  refine ⟨13270739093797454930475893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8847159395864969953650595 13270739093797454930475893)
                  ·
                    refine ⟨1244131790043511399732115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13270739093797454930475893 1244131790043511399732115)
                    ·
                      rfl

theorem cell22_3634407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_3634407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634407 prefixEnd_3634407 := by exact prefixLift 3634407
  have htrace : WordTrace (prefixWord ++ tailWord_3634407) baseStart_3634407 baseEnd_3634407 := by
    simpa [prefixWord, tailWord_3634407, baseEnd_3634407] using wordTrace_append hprefix tailTrace_3634407
  have hstable : (prefixWord ++ tailWord_3634407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634407).length < 2 ^ (prefixWord ++ tailWord_3634407).sum := by decide
  have hdescent : baseEnd_3634407 < baseStart_3634407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634469 : List Nat := [1, 3, 1, 2, 4, 1, 1, 5, 1, 3]
def baseStart_3634469 : Nat := 118140960795 + 3634469 * 2 ^ 59
def prefixEnd_3634469 : Nat := 4983230072969 + 3 ^ 40 * 3634469 * 2
def baseEnd_3634469 : Nat := 1244153013910563904681925

theorem tailTrace_3634469 : CollatzResearch.WordTrace tailWord_3634469 prefixEnd_3634469 1244153013910563904681925 := by
  unfold tailWord_3634469
  simp only [CollatzResearch.WordTrace]
  refine ⟨132559974669947005732434461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88373316446631337154956307 132559974669947005732434461)
  ·
    refine ⟨49709990501230127149662923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132559974669947005732434461 49709990501230127149662923)
    ·
      refine ⟨74564985751845190724494385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49709990501230127149662923 74564985751845190724494385)
      ·
        refine ⟨55923739313883893043370789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74564985751845190724494385 55923739313883893043370789)
        ·
          refine ⟨10485701121353229945632023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55923739313883893043370789 10485701121353229945632023)
          ·
            refine ⟨15728551682029844918448035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10485701121353229945632023 15728551682029844918448035)
            ·
              refine ⟨23592827523044767377672053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15728551682029844918448035 23592827523044767377672053)
              ·
                refine ⟨2211827580285446941656755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23592827523044767377672053 2211827580285446941656755)
                ·
                  refine ⟨3317741370428170412485133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2211827580285446941656755 3317741370428170412485133)
                  ·
                    refine ⟨1244153013910563904681925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3317741370428170412485133 1244153013910563904681925)
                    ·
                      rfl

theorem cell22_3634469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5, 1, 3].length) (baseStart_3634469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634469 prefixEnd_3634469 := by exact prefixLift 3634469
  have htrace : WordTrace (prefixWord ++ tailWord_3634469) baseStart_3634469 baseEnd_3634469 := by
    simpa [prefixWord, tailWord_3634469, baseEnd_3634469] using wordTrace_append hprefix tailTrace_3634469
  have hstable : (prefixWord ++ tailWord_3634469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634469).length < 2 ^ (prefixWord ++ tailWord_3634469).sum := by decide
  have hdescent : baseEnd_3634469 < baseStart_3634469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634482 : List Nat := [3, 2, 1, 1, 4, 1, 3, 2, 5]
def baseStart_3634482 : Nat := 118140960795 + 3634482 * 2 ^ 59
def prefixEnd_3634482 : Nat := 4983230072969 + 3 ^ 40 * 3634482 * 2
def baseEnd_3634482 : Nat := 414719154692078734702295

theorem tailTrace_3634482 : CollatzResearch.WordTrace tailWord_3634482 prefixEnd_3634482 414719154692078734702295 := by
  unfold tailWord_3634482
  simp only [CollatzResearch.WordTrace]
  refine ⟨33140112204724977238164425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88373632545933272635105133 33140112204724977238164425)
  ·
    refine ⟨24855084153543732928623319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33140112204724977238164425 24855084153543732928623319)
    ·
      refine ⟨37282626230315599392934979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24855084153543732928623319 37282626230315599392934979)
      ·
        refine ⟨55923939345473399089402469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37282626230315599392934979 55923939345473399089402469)
        ·
          refine ⟨10485738627276262329262963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55923939345473399089402469 10485738627276262329262963)
          ·
            refine ⟨15728607940914393493894445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10485738627276262329262963 15728607940914393493894445)
            ·
              refine ⟨5898227977842897560210417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15728607940914393493894445 5898227977842897560210417)
              ·
                refine ⟨4423670983382173170157813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5898227977842897560210417 4423670983382173170157813)
                ·
                  refine ⟨414719154692078734702295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4423670983382173170157813 414719154692078734702295)
                  ·
                    rfl

theorem cell22_3634482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_3634482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634482 prefixEnd_3634482 := by exact prefixLift 3634482
  have htrace : WordTrace (prefixWord ++ tailWord_3634482) baseStart_3634482 baseEnd_3634482 := by
    simpa [prefixWord, tailWord_3634482, baseEnd_3634482] using wordTrace_append hprefix tailTrace_3634482
  have hstable : (prefixWord ++ tailWord_3634482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634482).length < 2 ^ (prefixWord ++ tailWord_3634482).sum := by decide
  have hdescent : baseEnd_3634482 < baseStart_3634482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634497 : List Nat := [1, 2, 5, 2, 1, 1, 2, 1, 2, 5]
def baseStart_3634497 : Nat := 118140960795 + 3634497 * 2 ^ 59
def prefixEnd_3634497 : Nat := 4983230072969 + 3 ^ 40 * 3634497 * 2
def baseEnd_3634497 : Nat := 1244162598882781164981839

theorem tailTrace_3634497 : CollatzResearch.WordTrace tailWord_3634497 prefixEnd_3634497 1244162598882781164981839 := by
  unfold tailWord_3634497
  simp only [CollatzResearch.WordTrace]
  refine ⟨132560995913845566514453745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88373997275897044342969163 132560995913845566514453745)
  ·
    refine ⟨99420746935384174885840309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132560995913845566514453745 99420746935384174885840309)
    ·
      refine ⟨9320695025192266395547529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99420746935384174885840309 9320695025192266395547529)
      ·
        refine ⟨6990521268894199796660647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9320695025192266395547529 6990521268894199796660647)
        ·
          refine ⟨10485781903341299694990971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6990521268894199796660647 10485781903341299694990971)
          ·
            refine ⟨15728672855011949542486457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10485781903341299694990971 15728672855011949542486457)
            ·
              refine ⟨11796504641258962156864843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15728672855011949542486457 11796504641258962156864843)
              ·
                refine ⟨17694756961888443235297265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11796504641258962156864843 17694756961888443235297265)
                ·
                  refine ⟨13271067721416332426472949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17694756961888443235297265 13271067721416332426472949)
                  ·
                    refine ⟨1244162598882781164981839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13271067721416332426472949 1244162598882781164981839)
                    ·
                      rfl

theorem cell22_3634497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_3634497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634497 prefixEnd_3634497 := by exact prefixLift 3634497
  have htrace : WordTrace (prefixWord ++ tailWord_3634497) baseStart_3634497 baseEnd_3634497 := by
    simpa [prefixWord, tailWord_3634497, baseEnd_3634497] using wordTrace_append hprefix tailTrace_3634497
  have hstable : (prefixWord ++ tailWord_3634497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634497).length < 2 ^ (prefixWord ++ tailWord_3634497).sum := by decide
  have hdescent : baseEnd_3634497 < baseStart_3634497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634510 : List Nat := [4, 1, 1, 1, 1, 1, 3, 4, 6]
def baseStart_3634510 : Nat := 118140960795 + 3634510 * 2 ^ 59
def prefixEnd_3634510 : Nat := 4983230072969 + 3 ^ 40 * 3634510 * 2
def baseEnd_3634510 : Nat := 414722349682817821468933

theorem tailTrace_3634510 : CollatzResearch.WordTrace tailWord_3634510 prefixEnd_3634510 414722349682817821468933 := by
  unfold tailWord_3634510
  simp only [CollatzResearch.WordTrace]
  refine ⟨16570183757849808716834623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88374313375198979823117989 16570183757849808716834623)
  ·
    refine ⟨24855275636774713075251935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16570183757849808716834623 24855275636774713075251935)
    ·
      refine ⟨37282913455162069612877903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24855275636774713075251935 37282913455162069612877903)
      ·
        refine ⟨55924370182743104419316855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37282913455162069612877903 55924370182743104419316855)
        ·
          refine ⟨83886555274114656628975283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55924370182743104419316855 83886555274114656628975283)
          ·
            refine ⟨125829832911171984943462925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83886555274114656628975283 125829832911171984943462925)
            ·
              refine ⟨47186187341689494353798597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125829832911171984943462925 47186187341689494353798597)
              ·
                refine ⟨8847410126566780191337237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47186187341689494353798597 8847410126566780191337237)
                ·
                  refine ⟨414722349682817821468933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8847410126566780191337237 414722349682817821468933)
                  ·
                    rfl

theorem cell22_3634510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_3634510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634510 prefixEnd_3634510 := by exact prefixLift 3634510
  have htrace : WordTrace (prefixWord ++ tailWord_3634510) baseStart_3634510 baseEnd_3634510 := by
    simpa [prefixWord, tailWord_3634510, baseEnd_3634510] using wordTrace_append hprefix tailTrace_3634510
  have hstable : (prefixWord ++ tailWord_3634510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634510).length < 2 ^ (prefixWord ++ tailWord_3634510).sum := by decide
  have hdescent : baseEnd_3634510 < baseStart_3634510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634512 : List Nat := [2, 1, 1, 1, 1, 5, 4, 2, 1, 4]
def baseStart_3634512 : Nat := 118140960795 + 3634512 * 2 ^ 59
def prefixEnd_3634512 : Nat := 4983230072969 + 3 ^ 40 * 3634512 * 2
def baseEnd_3634512 : Nat := 1244167733689326125856793

theorem tailTrace_3634512 : CollatzResearch.WordTrace tailWord_3634512 prefixEnd_3634512 1244167733689326125856793 := by
  unfold tailWord_3634512
  simp only [CollatzResearch.WordTrace]
  refine ⟨66280771504395612038124895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88374362005860816050833193 66280771504395612038124895)
  ·
    refine ⟨99421157256593418057187343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66280771504395612038124895 99421157256593418057187343)
    ·
      refine ⟨149131735884890127085781015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99421157256593418057187343 149131735884890127085781015)
      ·
        refine ⟨223697603827335190628671523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149131735884890127085781015 223697603827335190628671523)
        ·
          refine ⟨335546405741002785943007285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223697603827335190628671523 335546405741002785943007285)
          ·
            refine ⟨31457475538219011182156933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 335546405741002785943007285 31457475538219011182156933)
            ·
              refine ⟨5898276663416064596654425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31457475538219011182156933 5898276663416064596654425)
              ·
                refine ⟨4423707497562048447490819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5898276663416064596654425 4423707497562048447490819)
                ·
                  refine ⟨6635561246343072671236229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4423707497562048447490819 6635561246343072671236229)
                  ·
                    refine ⟨1244167733689326125856793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6635561246343072671236229 1244167733689326125856793)
                    ·
                      rfl

theorem cell22_3634512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 1, 4].length) (baseStart_3634512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634512 prefixEnd_3634512 := by exact prefixLift 3634512
  have htrace : WordTrace (prefixWord ++ tailWord_3634512) baseStart_3634512 baseEnd_3634512 := by
    simpa [prefixWord, tailWord_3634512, baseEnd_3634512] using wordTrace_append hprefix tailTrace_3634512
  have hstable : (prefixWord ++ tailWord_3634512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634512).length < 2 ^ (prefixWord ++ tailWord_3634512).sum := by decide
  have hdescent : baseEnd_3634512 < baseStart_3634512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634544 : List Nat := [2, 1, 1, 1, 4, 2, 5, 2, 4]
def baseStart_3634544 : Nat := 118140960795 + 3634544 * 2 ^ 59
def prefixEnd_3634544 : Nat := 4983230072969 + 3 ^ 40 * 3634544 * 2
def baseEnd_3634544 : Nat := 414726229314429569685565

theorem tailTrace_3634544 : CollatzResearch.WordTrace tailWord_3634544 prefixEnd_3634544 414726229314429569685565 := by
  unfold tailWord_3634544
  simp only [CollatzResearch.WordTrace]
  refine ⟨66281355072337646770707343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88375140096450195694276457 66281355072337646770707343)
  ·
    refine ⟨99422032608506470156061015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66281355072337646770707343 99422032608506470156061015)
    ·
      refine ⟨149133048912759705234091523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99422032608506470156061015 149133048912759705234091523)
      ·
        refine ⟨223699573369139557851137285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149133048912759705234091523 223699573369139557851137285)
        ·
          refine ⟨41943670006713667097088241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223699573369139557851137285 41943670006713667097088241)
          ·
            refine ⟨31457752505035250322816181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41943670006713667097088241 31457752505035250322816181)
            ·
              refine ⟨2949164297347054717764017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31457752505035250322816181 2949164297347054717764017)
              ·
                refine ⟨2211873223010291038323013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2949164297347054717764017 2211873223010291038323013)
                ·
                  refine ⟨414726229314429569685565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2211873223010291038323013 414726229314429569685565)
                  ·
                    rfl

theorem cell22_3634544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2, 4].length) (baseStart_3634544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634544 prefixEnd_3634544 := by exact prefixLift 3634544
  have htrace : WordTrace (prefixWord ++ tailWord_3634544) baseStart_3634544 baseEnd_3634544 := by
    simpa [prefixWord, tailWord_3634544, baseEnd_3634544] using wordTrace_append hprefix tailTrace_3634544
  have hstable : (prefixWord ++ tailWord_3634544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634544).length < 2 ^ (prefixWord ++ tailWord_3634544).sum := by decide
  have hdescent : baseEnd_3634544 < baseStart_3634544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634555 : List Nat := [1, 1, 1, 1, 1, 6, 4, 7]
def baseStart_3634555 : Nat := 118140960795 + 3634555 * 2 ^ 59
def prefixEnd_3634555 : Nat := 4983230072969 + 3 ^ 40 * 3634555 * 2
def baseEnd_3634555 : Nat := 138242494829787594114629

theorem tailTrace_3634555 : CollatzResearch.WordTrace tailWord_3634555 prefixEnd_3634555 138242494829787594114629 := by
  unfold tailWord_3634555
  simp only [CollatzResearch.WordTrace]
  refine ⟨132563111347635442420065119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88375407565090294946710079 132563111347635442420065119)
  ·
    refine ⟨198844667021453163630097679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132563111347635442420065119 198844667021453163630097679)
    ·
      refine ⟨298267000532179745445146519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198844667021453163630097679 298267000532179745445146519)
      ·
        refine ⟨447400500798269618167719779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298267000532179745445146519 447400500798269618167719779)
        ·
          refine ⟨671100751197404427251579669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447400500798269618167719779 671100751197404427251579669)
          ·
            refine ⟨31457847712378332527417797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 671100751197404427251579669 31457847712378332527417797)
            ·
              refine ⟨5898346446070937348890837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31457847712378332527417797 5898346446070937348890837)
              ·
                refine ⟨138242494829787594114629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5898346446070937348890837 138242494829787594114629)
                ·
                  rfl

theorem cell22_3634555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 7].length) (baseStart_3634555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634555 prefixEnd_3634555 := by exact prefixLift 3634555
  have htrace : WordTrace (prefixWord ++ tailWord_3634555) baseStart_3634555 baseEnd_3634555 := by
    simpa [prefixWord, tailWord_3634555, baseEnd_3634555] using wordTrace_append hprefix tailTrace_3634555
  have hstable : (prefixWord ++ tailWord_3634555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634555).length < 2 ^ (prefixWord ++ tailWord_3634555).sum := by decide
  have hdescent : baseEnd_3634555 < baseStart_3634555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634707 : List Nat := [1, 1, 1, 2, 1, 8, 8]
def baseStart_3634707 : Nat := 118140960795 + 3634707 * 2 ^ 59
def prefixEnd_3634707 : Nat := 4983230072969 + 3 ^ 40 * 3634707 * 2
def baseEnd_3634707 : Nat := 46082758747200393230785

theorem tailTrace_3634707 : CollatzResearch.WordTrace tailWord_3634707 prefixEnd_3634707 46082758747200393230785 := by
  unfold tailWord_3634707
  simp only [CollatzResearch.WordTrace]
  refine ⟨132568655243084772379598375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88379103495389848253065583 132568655243084772379598375)
  ·
    refine ⟨198852982864627158569397563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132568655243084772379598375 198852982864627158569397563)
    ·
      refine ⟨298279474296940737854096345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198852982864627158569397563 298279474296940737854096345)
      ·
        refine ⟨223709605722705553390572259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298279474296940737854096345 223709605722705553390572259)
        ·
          refine ⟨335564408584058330085858389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223709605722705553390572259 335564408584058330085858389)
          ·
            refine ⟨3932395413094433555693653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 335564408584058330085858389 3932395413094433555693653)
            ·
              refine ⟨46082758747200393230785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3932395413094433555693653 46082758747200393230785)
              ·
                rfl

theorem cell22_3634707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 8].length) (baseStart_3634707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634707 prefixEnd_3634707 := by exact prefixLift 3634707
  have htrace : WordTrace (prefixWord ++ tailWord_3634707) baseStart_3634707 baseEnd_3634707 := by
    simpa [prefixWord, tailWord_3634707, baseEnd_3634707] using wordTrace_append hprefix tailTrace_3634707
  have hstable : (prefixWord ++ tailWord_3634707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634707).length < 2 ^ (prefixWord ++ tailWord_3634707).sum := by decide
  have hdescent : baseEnd_3634707 < baseStart_3634707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634709 : List Nat := [1, 3, 2, 1, 3, 3, 1, 2, 2, 4]
def baseStart_3634709 : Nat := 118140960795 + 3634709 * 2 ^ 59
def prefixEnd_3634709 : Nat := 4983230072969 + 3 ^ 40 * 3634709 * 2
def baseEnd_3634709 : Nat := 1244235170815283278681189

theorem tailTrace_3634709 : CollatzResearch.WordTrace tailWord_3634709 prefixEnd_3634709 1244235170815283278681189 := by
  unfold tailWord_3634709
  simp only [CollatzResearch.WordTrace]
  refine ⟨132568728189077526721171181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88379152126051684480780787 132568728189077526721171181)
  ·
    refine ⟨49713273070904072520439193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132568728189077526721171181 49713273070904072520439193)
    ·
      refine ⟨37284954803178054390329395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49713273070904072520439193 37284954803178054390329395)
      ·
        refine ⟨55927432204767081585494093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37284954803178054390329395 55927432204767081585494093)
        ·
          refine ⟨20972787076787655594560285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55927432204767081585494093 20972787076787655594560285)
          ·
            refine ⟨7864795153795370847960107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20972787076787655594560285 7864795153795370847960107)
            ·
              refine ⟨11797192730693056271940161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7864795153795370847960107 11797192730693056271940161)
              ·
                refine ⟨8847894548019792203955121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11797192730693056271940161 8847894548019792203955121)
                ·
                  refine ⟨6635920911014844152966341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8847894548019792203955121 6635920911014844152966341)
                  ·
                    refine ⟨1244235170815283278681189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6635920911014844152966341 1244235170815283278681189)
                    ·
                      rfl

theorem cell22_3634709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_3634709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634709 prefixEnd_3634709 := by exact prefixLift 3634709
  have htrace : WordTrace (prefixWord ++ tailWord_3634709) baseStart_3634709 baseEnd_3634709 := by
    simpa [prefixWord, tailWord_3634709, baseEnd_3634709] using wordTrace_append hprefix tailTrace_3634709
  have hstable : (prefixWord ++ tailWord_3634709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634709).length < 2 ^ (prefixWord ++ tailWord_3634709).sum := by decide
  have hdescent : baseEnd_3634709 < baseStart_3634709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634728 : List Nat := [2, 1, 5, 2, 2, 1, 1, 3, 2, 3]
def baseStart_3634728 : Nat := 118140960795 + 3634728 * 2 ^ 59
def prefixEnd_3634728 : Nat := 4983230072969 + 3 ^ 40 * 3634728 * 2
def baseEnd_3634728 : Nat := 1244241674903573562456131

theorem tailTrace_3634728 : CollatzResearch.WordTrace tailWord_3634728 prefixEnd_3634728 1244241674903573562456131 := by
  unfold tailWord_3634728
  simp only [CollatzResearch.WordTrace]
  refine ⟨66284710588004346483056419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88379614117339128644075225 66284710588004346483056419)
  ·
    refine ⟨99427065882006519724584629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66284710588004346483056419 99427065882006519724584629)
    ·
      refine ⟨9321287426438111224179809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99427065882006519724584629 9321287426438111224179809)
      ·
        refine ⟨6990965569828583418134857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9321287426438111224179809 6990965569828583418134857)
        ·
          refine ⟨5243224177371437563601143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6990965569828583418134857 5243224177371437563601143)
          ·
            refine ⟨7864836266057156345401715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5243224177371437563601143 7864836266057156345401715)
            ·
              refine ⟨11797254399085734518102573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7864836266057156345401715 11797254399085734518102573)
              ·
                refine ⟨4423970399657150444288465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11797254399085734518102573 4423970399657150444288465)
                ·
                  refine ⟨3317977799742862833216349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4423970399657150444288465 3317977799742862833216349)
                  ·
                    refine ⟨1244241674903573562456131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3317977799742862833216349 1244241674903573562456131)
                    ·
                      rfl

theorem cell22_3634728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_3634728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634728 prefixEnd_3634728 := by exact prefixLift 3634728
  have htrace : WordTrace (prefixWord ++ tailWord_3634728) baseStart_3634728 baseEnd_3634728 := by
    simpa [prefixWord, tailWord_3634728, baseEnd_3634728] using wordTrace_append hprefix tailTrace_3634728
  have hstable : (prefixWord ++ tailWord_3634728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634728).length < 2 ^ (prefixWord ++ tailWord_3634728).sum := by decide
  have hdescent : baseEnd_3634728 < baseStart_3634728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634767 : List Nat := [1, 1, 2, 1, 1, 2, 3, 4, 2, 5]
def baseStart_3634767 : Nat := 118140960795 + 3634767 * 2 ^ 59
def prefixEnd_3634767 : Nat := 4983230072969 + 3 ^ 40 * 3634767 * 2
def baseEnd_3634767 : Nat := 1244255025400590460731011

theorem tailTrace_3634767 : CollatzResearch.WordTrace tailWord_3634767 prefixEnd_3634767 1244255025400590460731011 := by
  unfold tailWord_3634767
  simp only [CollatzResearch.WordTrace]
  refine ⟨132570843622867402626782555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88380562415244935084521703 132570843622867402626782555)
  ·
    refine ⟨198856265434301103940173833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132570843622867402626782555 198856265434301103940173833)
    ·
      refine ⟨149142199075725827955130375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198856265434301103940173833 149142199075725827955130375)
      ·
        refine ⟨223713298613588741932695563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149142199075725827955130375 223713298613588741932695563)
        ·
          refine ⟨335569947920383112899043345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223713298613588741932695563 335569947920383112899043345)
          ·
            refine ⟨251677460940287334674282509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335569947920383112899043345 251677460940287334674282509)
            ·
              refine ⟨94379047852607750502855941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251677460940287334674282509 94379047852607750502855941)
              ·
                refine ⟨17696071472363953219285489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94379047852607750502855941 17696071472363953219285489)
                ·
                  refine ⟨13272053604272964914464117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17696071472363953219285489 13272053604272964914464117)
                  ·
                    refine ⟨1244255025400590460731011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13272053604272964914464117 1244255025400590460731011)
                    ·
                      rfl

theorem cell22_3634767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 5].length) (baseStart_3634767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634767 prefixEnd_3634767 := by exact prefixLift 3634767
  have htrace : WordTrace (prefixWord ++ tailWord_3634767) baseStart_3634767 baseEnd_3634767 := by
    simpa [prefixWord, tailWord_3634767, baseEnd_3634767] using wordTrace_append hprefix tailTrace_3634767
  have hstable : (prefixWord ++ tailWord_3634767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634767).length < 2 ^ (prefixWord ++ tailWord_3634767).sum := by decide
  have hdescent : baseEnd_3634767 < baseStart_3634767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634769 : List Nat := [1, 2, 2, 1, 3, 2, 4, 2, 5]
def baseStart_3634769 : Nat := 118140960795 + 3634769 * 2 ^ 59
def prefixEnd_3634769 : Nat := 4983230072969 + 3 ^ 40 * 3634769 * 2
def baseEnd_3634769 : Nat := 414751903347154374060335

theorem tailTrace_3634769 : CollatzResearch.WordTrace tailWord_3634769 prefixEnd_3634769 414751903347154374060335 := by
  unfold tailWord_3634769
  simp only [CollatzResearch.WordTrace]
  refine ⟨132570916568860156968355361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88380611045906771312236907 132570916568860156968355361)
  ·
    refine ⟨99428187426645117726266521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132570916568860156968355361 99428187426645117726266521)
    ·
      refine ⟨74571140569983838294699891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99428187426645117726266521 74571140569983838294699891)
      ·
        refine ⟨111856710854975757442049837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74571140569983838294699891 111856710854975757442049837)
        ·
          refine ⟨41946266570615909040768689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111856710854975757442049837 41946266570615909040768689)
          ·
            refine ⟨31459699927961931780576517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41946266570615909040768689 31459699927961931780576517)
            ·
              refine ⟨5898693736492862208858097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31459699927961931780576517 5898693736492862208858097)
              ·
                refine ⟨4424020302369646656643573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5898693736492862208858097 4424020302369646656643573)
                ·
                  refine ⟨414751903347154374060335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4424020302369646656643573 414751903347154374060335)
                  ·
                    rfl

theorem cell22_3634769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 5].length) (baseStart_3634769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634769 prefixEnd_3634769 := by exact prefixLift 3634769
  have htrace : WordTrace (prefixWord ++ tailWord_3634769) baseStart_3634769 baseEnd_3634769 := by
    simpa [prefixWord, tailWord_3634769, baseEnd_3634769] using wordTrace_append hprefix tailTrace_3634769
  have hstable : (prefixWord ++ tailWord_3634769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634769).length < 2 ^ (prefixWord ++ tailWord_3634769).sum := by decide
  have hdescent : baseEnd_3634769 < baseStart_3634769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634799 : List Nat := [1, 1, 2, 1, 3, 2, 1, 6, 1, 4]
def baseStart_3634799 : Nat := 118140960795 + 3634799 * 2 ^ 59
def prefixEnd_3634799 : Nat := 4983230072969 + 3 ^ 40 * 3634799 * 2
def baseEnd_3634799 : Nat := 1244265979654553043930913

theorem tailTrace_3634799 : CollatzResearch.WordTrace tailWord_3634799 prefixEnd_3634799 1244265979654553043930913 := by
  unfold tailWord_3634799
  simp only [CollatzResearch.WordTrace]
  refine ⟨132572010758751472091947451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88381340505834314727964967 132572010758751472091947451)
  ·
    refine ⟨198858016138127208137921177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132572010758751472091947451 198858016138127208137921177)
    ·
      refine ⟨149143512103595406103440883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198858016138127208137921177 149143512103595406103440883)
      ·
        refine ⟨223715268155393109155161325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149143512103595406103440883 223715268155393109155161325)
        ·
          refine ⟨83893225558272415933185497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223715268155393109155161325 83893225558272415933185497)
          ·
            refine ⟨62919919168704311949889123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83893225558272415933185497 62919919168704311949889123)
            ·
              refine ⟨94379878753056467924833685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62919919168704311949889123 94379878753056467924833685)
              ·
                refine ⟨4424056816549521933976579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94379878753056467924833685 4424056816549521933976579)
                ·
                  refine ⟨6636085224824282900964869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4424056816549521933976579 6636085224824282900964869)
                  ·
                    refine ⟨1244265979654553043930913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6636085224824282900964869 1244265979654553043930913)
                    ·
                      rfl

theorem cell22_3634799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 4].length) (baseStart_3634799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634799 prefixEnd_3634799 := by exact prefixLift 3634799
  have htrace : WordTrace (prefixWord ++ tailWord_3634799) baseStart_3634799 baseEnd_3634799 := by
    simpa [prefixWord, tailWord_3634799, baseEnd_3634799] using wordTrace_append hprefix tailTrace_3634799
  have hstable : (prefixWord ++ tailWord_3634799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634799).length < 2 ^ (prefixWord ++ tailWord_3634799).sum := by decide
  have hdescent : baseEnd_3634799 < baseStart_3634799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634850 : List Nat := [3, 3, 1, 4, 1, 1, 2, 2, 1, 4]
def baseStart_3634850 : Nat := 118140960795 + 3634850 * 2 ^ 59
def prefixEnd_3634850 : Nat := 4983230072969 + 3 ^ 40 * 3634850 * 2
def baseEnd_3634850 : Nat := 1244283437996805910905757

theorem tailTrace_3634850 : CollatzResearch.WordTrace tailWord_3634850 prefixEnd_3634850 1244283437996805910905757 := by
  unfold tailWord_3634850
  simp only [CollatzResearch.WordTrace]
  refine ⟨33143467720391676950513501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88382580587711138534702669 33143467720391676950513501)
  ·
    refine ⟨12428800395146878856442563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33143467720391676950513501 12428800395146878856442563)
    ·
      refine ⟨18643200592720318284663845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12428800395146878856442563 18643200592720318284663845)
      ·
        refine ⟨3495600111135059678374471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18643200592720318284663845 3495600111135059678374471)
        ·
          refine ⟨5243400166702589517561707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3495600111135059678374471 5243400166702589517561707)
          ·
            refine ⟨7865100250053884276342561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5243400166702589517561707 7865100250053884276342561)
            ·
              refine ⟨5898825187540413207256921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7865100250053884276342561 5898825187540413207256921)
              ·
                refine ⟨4424118890655309905442691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5898825187540413207256921 4424118890655309905442691)
                ·
                  refine ⟨6636178335982964858164037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4424118890655309905442691 6636178335982964858164037)
                  ·
                    refine ⟨1244283437996805910905757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6636178335982964858164037 1244283437996805910905757)
                    ·
                      rfl

theorem cell22_3634850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_3634850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634850 prefixEnd_3634850 := by exact prefixLift 3634850
  have htrace : WordTrace (prefixWord ++ tailWord_3634850) baseStart_3634850 baseEnd_3634850 := by
    simpa [prefixWord, tailWord_3634850, baseEnd_3634850] using wordTrace_append hprefix tailTrace_3634850
  have hstable : (prefixWord ++ tailWord_3634850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634850).length < 2 ^ (prefixWord ++ tailWord_3634850).sum := by decide
  have hdescent : baseEnd_3634850 < baseStart_3634850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634861 : List Nat := [1, 5, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_3634861 : Nat := 118140960795 + 3634861 * 2 ^ 59
def prefixEnd_3634861 : Nat := 4983230072969 + 3 ^ 40 * 3634861 * 2
def baseEnd_3634861 : Nat := 1244287203521605548880723

theorem tailTrace_3634861 : CollatzResearch.WordTrace tailWord_3634861 prefixEnd_3634861 1244287203521605548880723 := by
  unfold tailWord_3634861
  simp only [CollatzResearch.WordTrace]
  refine ⟨132574272084526856680704437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88382848056351237787136291 132574272084526856680704437)
  ·
    refine ⟨12428838007924392813816041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132574272084526856680704437 12428838007924392813816041)
    ·
      refine ⟨9321628505943294610362031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12428838007924392813816041 9321628505943294610362031)
      ·
        refine ⟨13982442758914941915543047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9321628505943294610362031 13982442758914941915543047)
        ·
          refine ⟨20973664138372412873314571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13982442758914941915543047 20973664138372412873314571)
          ·
            refine ⟨31460496207558619309971857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20973664138372412873314571 31460496207558619309971857)
            ·
              refine ⟨23595372155668964482478893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31460496207558619309971857 23595372155668964482478893)
              ·
                refine ⟨8848264558375861680929585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23595372155668964482478893 8848264558375861680929585)
                ·
                  refine ⟨6636198418781896260697189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8848264558375861680929585 6636198418781896260697189)
                  ·
                    refine ⟨1244287203521605548880723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6636198418781896260697189 1244287203521605548880723)
                    ·
                      rfl

theorem cell22_3634861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_3634861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634861 prefixEnd_3634861 := by exact prefixLift 3634861
  have htrace : WordTrace (prefixWord ++ tailWord_3634861) baseStart_3634861 baseEnd_3634861 := by
    simpa [prefixWord, tailWord_3634861, baseEnd_3634861] using wordTrace_append hprefix tailTrace_3634861
  have hstable : (prefixWord ++ tailWord_3634861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634861).length < 2 ^ (prefixWord ++ tailWord_3634861).sum := by decide
  have hdescent : baseEnd_3634861 < baseStart_3634861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634882 : List Nat := [3, 5, 1, 2, 1, 2, 1, 1, 6]
def baseStart_3634882 : Nat := 118140960795 + 3634882 * 2 ^ 59
def prefixEnd_3634882 : Nat := 4983230072969 + 3 ^ 40 * 3634882 * 2
def baseEnd_3634882 : Nat := 414764797416922831368553

theorem tailTrace_3634882 : CollatzResearch.WordTrace tailWord_3634882 prefixEnd_3634882 414764797416922831368553 := by
  unfold tailWord_3634882
  simp only [CollatzResearch.WordTrace]
  refine ⟨33143759504362694316804725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88383358678300518178145933 33143759504362694316804725)
  ·
    refine ⟨3107227453534002592200443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33143759504362694316804725 3107227453534002592200443)
    ·
      refine ⟨4660841180301003888300665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3107227453534002592200443 4660841180301003888300665)
      ·
        refine ⟨3495630885225752916225499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4660841180301003888300665 3495630885225752916225499)
        ·
          refine ⟨5243446327838629374338249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3495630885225752916225499 5243446327838629374338249)
          ·
            refine ⟨3932584745878972030753687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5243446327838629374338249 3932584745878972030753687)
            ·
              refine ⟨5898877118818458046130531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3932584745878972030753687 5898877118818458046130531)
              ·
                refine ⟨8848315678227687069195797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5898877118818458046130531 8848315678227687069195797)
                ·
                  refine ⟨414764797416922831368553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8848315678227687069195797 414764797416922831368553)
                  ·
                    rfl

theorem cell22_3634882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_3634882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634882 prefixEnd_3634882 := by exact prefixLift 3634882
  have htrace : WordTrace (prefixWord ++ tailWord_3634882) baseStart_3634882 baseEnd_3634882 := by
    simpa [prefixWord, tailWord_3634882, baseEnd_3634882] using wordTrace_append hprefix tailTrace_3634882
  have hstable : (prefixWord ++ tailWord_3634882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634882).length < 2 ^ (prefixWord ++ tailWord_3634882).sum := by decide
  have hdescent : baseEnd_3634882 < baseStart_3634882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634893 : List Nat := [1, 6, 2, 1, 1, 2, 2, 7]
def baseStart_3634893 : Nat := 118140960795 + 3634893 * 2 ^ 59
def prefixEnd_3634893 : Nat := 4983230072969 + 3 ^ 40 * 3634893 * 2
def baseEnd_3634893 : Nat := 138255350863952014675625

theorem tailTrace_3634893 : CollatzResearch.WordTrace tailWord_3634893 prefixEnd_3634893 138255350863952014675625 := by
  unfold tailWord_3634893
  simp only [CollatzResearch.WordTrace]
  refine ⟨132575439220410926145869333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88383626146940617430579555 132575439220410926145869333)
  ·
    refine ⟨6214473713456762163087625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 132575439220410926145869333 6214473713456762163087625)
    ·
      refine ⟨4660855285092571622315719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6214473713456762163087625 4660855285092571622315719)
      ·
        refine ⟨6991282927638857433473579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4660855285092571622315719 6991282927638857433473579)
        ·
          refine ⟨10486924391458286150210369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6991282927638857433473579 10486924391458286150210369)
          ·
            refine ⟨7865193293593714612657777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10486924391458286150210369 7865193293593714612657777)
            ·
              refine ⟨5898894970195285959493333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7865193293593714612657777 5898894970195285959493333)
              ·
                refine ⟨138255350863952014675625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5898894970195285959493333 138255350863952014675625)
                ·
                  rfl

theorem cell22_3634893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 7].length) (baseStart_3634893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634893 prefixEnd_3634893 := by exact prefixLift 3634893
  have htrace : WordTrace (prefixWord ++ tailWord_3634893) baseStart_3634893 baseEnd_3634893 := by
    simpa [prefixWord, tailWord_3634893, baseEnd_3634893] using wordTrace_append hprefix tailTrace_3634893
  have hstable : (prefixWord ++ tailWord_3634893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634893).length < 2 ^ (prefixWord ++ tailWord_3634893).sum := by decide
  have hdescent : baseEnd_3634893 < baseStart_3634893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634942 : List Nat := [4, 2, 2, 1, 3, 1, 1, 4, 1, 3]
def baseStart_3634942 : Nat := 118140960795 + 3634942 * 2 ^ 59
def prefixEnd_3634942 : Nat := 4983230072969 + 3 ^ 40 * 3634942 * 2
def baseEnd_3634942 : Nat := 1244314931476948337605475

theorem tailTrace_3634942 : CollatzResearch.WordTrace tailWord_3634942 prefixEnd_3634942 1244314931476948337605475 := by
  unfold tailWord_3634942
  simp only [CollatzResearch.WordTrace]
  refine ⟨16572153299654175939300385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88384817598155605009602053 16572153299654175939300385)
  ·
    refine ⟨12429114974740631954475289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16572153299654175939300385 12429114974740631954475289)
    ·
      refine ⟨9321836231055473965856467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12429114974740631954475289 9321836231055473965856467)
      ·
        refine ⟨13982754346583210948784701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9321836231055473965856467 13982754346583210948784701)
        ·
          refine ⟨5243532879968704105794263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13982754346583210948784701 5243532879968704105794263)
          ·
            refine ⟨7865299319953056158691395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5243532879968704105794263 7865299319953056158691395)
            ·
              refine ⟨11797948979929584238037093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7865299319953056158691395 11797948979929584238037093)
              ·
                refine ⟨2212115433736797044631955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11797948979929584238037093 2212115433736797044631955)
                ·
                  refine ⟨3318173150605195566947933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2212115433736797044631955 3318173150605195566947933)
                  ·
                    refine ⟨1244314931476948337605475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3318173150605195566947933 1244314931476948337605475)
                    ·
                      rfl

theorem cell22_3634942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_3634942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634942 prefixEnd_3634942 := by exact prefixLift 3634942
  have htrace : WordTrace (prefixWord ++ tailWord_3634942) baseStart_3634942 baseEnd_3634942 := by
    simpa [prefixWord, tailWord_3634942, baseEnd_3634942] using wordTrace_append hprefix tailTrace_3634942
  have hstable : (prefixWord ++ tailWord_3634942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634942).length < 2 ^ (prefixWord ++ tailWord_3634942).sum := by decide
  have hdescent : baseEnd_3634942 < baseStart_3634942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634981 : List Nat := [1, 3, 1, 2, 3, 2, 2, 2, 1, 5]
def baseStart_3634981 : Nat := 118140960795 + 3634981 * 2 ^ 59
def prefixEnd_3634981 : Nat := 4983230072969 + 3 ^ 40 * 3634981 * 2
def baseEnd_3634981 : Nat := 1244328281973965235880355

theorem tailTrace_3634981 : CollatzResearch.WordTrace tailWord_3634981 prefixEnd_3634981 1244328281973965235880355 := by
  unfold tailWord_3634981
  simp only [CollatzResearch.WordTrace]
  refine ⟨132578648844092117175072797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88385765896061411450048531 132578648844092117175072797)
  ·
    refine ⟨49716993316534543940652299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132578648844092117175072797 49716993316534543940652299)
    ·
      refine ⟨74575489974801815910978449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49716993316534543940652299 74575489974801815910978449)
      ·
        refine ⟨55931617481101361933233837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74575489974801815910978449 55931617481101361933233837)
        ·
          refine ⟨20974356555413010724962689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55931617481101361933233837 20974356555413010724962689)
          ·
            refine ⟨15730767416559758043722017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20974356555413010724962689 15730767416559758043722017)
            ·
              refine ⟨11798075562419818532791513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15730767416559758043722017 11798075562419818532791513)
              ·
                refine ⟨8848556671814863899593635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11798075562419818532791513 8848556671814863899593635)
                ·
                  refine ⟨13272835007722295849390453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8848556671814863899593635 13272835007722295849390453)
                  ·
                    refine ⟨1244328281973965235880355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13272835007722295849390453 1244328281973965235880355)
                    ·
                      rfl

theorem cell22_3634981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_3634981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3634981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3634981 prefixEnd_3634981 := by exact prefixLift 3634981
  have htrace : WordTrace (prefixWord ++ tailWord_3634981) baseStart_3634981 baseEnd_3634981 := by
    simpa [prefixWord, tailWord_3634981, baseEnd_3634981] using wordTrace_append hprefix tailTrace_3634981
  have hstable : (prefixWord ++ tailWord_3634981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634981).length < 2 ^ (prefixWord ++ tailWord_3634981).sum := by decide
  have hdescent : baseEnd_3634981 < baseStart_3634981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635028 : List Nat := [2, 4, 1, 1, 3, 1, 4, 6]
def baseStart_3635028 : Nat := 118140960795 + 3635028 * 2 ^ 59
def prefixEnd_3635028 : Nat := 4983230072969 + 3 ^ 40 * 3635028 * 2
def baseEnd_3635028 : Nat := 138260485670496975550579

theorem tailTrace_3635028 : CollatzResearch.WordTrace tailWord_3635028 prefixEnd_3635028 138260485670496975550579 := by
  unfold tailWord_3635028
  simp only [CollatzResearch.WordTrace]
  refine ⟨66290181537460922101016869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88386908716614562801355825 66290181537460922101016869)
  ·
    refine ⟨12429409038273922893940663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66290181537460922101016869 12429409038273922893940663)
    ·
      refine ⟨18644113557410884340910995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12429409038273922893940663 18644113557410884340910995)
      ·
        refine ⟨27966170336116326511366493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18644113557410884340910995 27966170336116326511366493)
        ·
          refine ⟨10487313876043622441762435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27966170336116326511366493 10487313876043622441762435)
          ·
            refine ⟨15730970814065433662643653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10487313876043622441762435 15730970814065433662643653)
            ·
              refine ⟨2949557027637268811745685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15730970814065433662643653 2949557027637268811745685)
              ·
                refine ⟨138260485670496975550579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2949557027637268811745685 138260485670496975550579)
                ·
                  rfl

theorem cell22_3635028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 6].length) (baseStart_3635028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635028 prefixEnd_3635028 := by exact prefixLift 3635028
  have htrace : WordTrace (prefixWord ++ tailWord_3635028) baseStart_3635028 baseEnd_3635028 := by
    simpa [prefixWord, tailWord_3635028, baseEnd_3635028] using wordTrace_append hprefix tailTrace_3635028
  have hstable : (prefixWord ++ tailWord_3635028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635028).length < 2 ^ (prefixWord ++ tailWord_3635028).sum := by decide
  have hdescent : baseEnd_3635028 < baseStart_3635028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635056 : List Nat := [2, 1, 1, 1, 4, 1, 1, 6, 5]
def baseStart_3635056 : Nat := 118140960795 + 3635056 * 2 ^ 59
def prefixEnd_3635056 : Nat := 4983230072969 + 3 ^ 40 * 3635056 * 2
def baseEnd_3635056 : Nat := 414784652002230013418375

theorem tailTrace_3635056 : CollatzResearch.WordTrace tailWord_3635056 prefixEnd_3635056 414784652002230013418375 := by
  unfold tailWord_3635056
  simp only [CollatzResearch.WordTrace]
  refine ⟨66290692159410202492026511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88387589545880269989368681 66290692159410202492026511)
  ·
    refine ⟨99436038239115303738039767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66290692159410202492026511 99436038239115303738039767)
    ·
      refine ⟨149154057358672955607059651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99436038239115303738039767 149154057358672955607059651)
      ·
        refine ⟨223731086038009433410589477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149154057358672955607059651 223731086038009433410589477)
        ·
          refine ⟨41949578632126768764485527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223731086038009433410589477 41949578632126768764485527)
          ·
            refine ⟨62924367948190153146728291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41949578632126768764485527 62924367948190153146728291)
            ·
              refine ⟨94386551922285229720092437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62924367948190153146728291 94386551922285229720092437)
              ·
                refine ⟨4424369621357120143129333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94386551922285229720092437 4424369621357120143129333)
                ·
                  refine ⟨414784652002230013418375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4424369621357120143129333 414784652002230013418375)
                  ·
                    rfl

theorem cell22_3635056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 5].length) (baseStart_3635056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635056 prefixEnd_3635056 := by exact prefixLift 3635056
  have htrace : WordTrace (prefixWord ++ tailWord_3635056) baseStart_3635056 baseEnd_3635056 := by
    simpa [prefixWord, tailWord_3635056, baseEnd_3635056] using wordTrace_append hprefix tailTrace_3635056
  have hstable : (prefixWord ++ tailWord_3635056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635056).length < 2 ^ (prefixWord ++ tailWord_3635056).sum := by decide
  have hdescent : baseEnd_3635056 < baseStart_3635056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635131 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 6, 4]
def baseStart_3635131 : Nat := 118140960795 + 3635131 * 2 ^ 59
def prefixEnd_3635131 : Nat := 4983230072969 + 3 ^ 40 * 3635131 * 2
def baseEnd_3635131 : Nat := 1244379630039414844629895

theorem tailTrace_3635131 : CollatzResearch.WordTrace tailWord_3635131 prefixEnd_3635131 1244379630039414844629895 := by
  unfold tailWord_3635131
  simp only [CollatzResearch.WordTrace]
  refine ⟨132584119793548692793033247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88389413195699128528688831 132584119793548692793033247)
  ·
    refine ⟨198876179690323039189549871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132584119793548692793033247 198876179690323039189549871)
    ·
      refine ⟨298314269535484558784324807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198876179690323039189549871 298314269535484558784324807)
      ·
        refine ⟨447471404303226838176487211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298314269535484558784324807 447471404303226838176487211)
        ·
          refine ⟨671207106454840257264730817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447471404303226838176487211 671207106454840257264730817)
          ·
            refine ⟨503405329841130192948548113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 671207106454840257264730817 503405329841130192948548113)
            ·
              refine ⟨377553997380847644711411085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503405329841130192948548113 377553997380847644711411085)
              ·
                refine ⟨141582749017817866766779157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 377553997380847644711411085 141582749017817866766779157)
                ·
                  refine ⟨6636691360210212504692773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 141582749017817866766779157 6636691360210212504692773)
                  ·
                    refine ⟨1244379630039414844629895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6636691360210212504692773 1244379630039414844629895)
                    ·
                      rfl

theorem cell22_3635131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 4].length) (baseStart_3635131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635131 prefixEnd_3635131 := by exact prefixLift 3635131
  have htrace : WordTrace (prefixWord ++ tailWord_3635131) baseStart_3635131 baseEnd_3635131 := by
    simpa [prefixWord, tailWord_3635131, baseEnd_3635131] using wordTrace_append hprefix tailTrace_3635131
  have hstable : (prefixWord ++ tailWord_3635131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635131).length < 2 ^ (prefixWord ++ tailWord_3635131).sum := by decide
  have hdescent : baseEnd_3635131 < baseStart_3635131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635133 : List Nat := [1, 4, 1, 2, 3, 1, 1, 3, 1, 5]
def baseStart_3635133 : Nat := 118140960795 + 3635133 * 2 ^ 59
def prefixEnd_3635133 : Nat := 4983230072969 + 3 ^ 40 * 3635133 * 2
def baseEnd_3635133 : Nat := 1244380314680287506079889

theorem tailTrace_3635133 : CollatzResearch.WordTrace tailWord_3635133 prefixEnd_3635133 1244380314680287506079889 := by
  unfold tailWord_3635133
  simp only [CollatzResearch.WordTrace]
  refine ⟨132584192739541447134606053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88389461826360964756404035 132584192739541447134606053)
  ·
    refine ⟨24859536138664021337738635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132584192739541447134606053 24859536138664021337738635)
    ·
      refine ⟨37289304207996032006607953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24859536138664021337738635 37289304207996032006607953)
      ·
        refine ⟨27966978155997024004955965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37289304207996032006607953 27966978155997024004955965)
        ·
          refine ⟨10487616808498884001858487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27966978155997024004955965 10487616808498884001858487)
          ·
            refine ⟨15731425212748326002787731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10487616808498884001858487 15731425212748326002787731)
            ·
              refine ⟨23597137819122489004181597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15731425212748326002787731 23597137819122489004181597)
              ·
                refine ⟨8848926682170933376568099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23597137819122489004181597 8848926682170933376568099)
                ·
                  refine ⟨13273390023256400064852149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8848926682170933376568099 13273390023256400064852149)
                  ·
                    refine ⟨1244380314680287506079889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13273390023256400064852149 1244380314680287506079889)
                    ·
                      rfl

theorem cell22_3635133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_3635133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635133 prefixEnd_3635133 := by exact prefixLift 3635133
  have htrace : WordTrace (prefixWord ++ tailWord_3635133) baseStart_3635133 baseEnd_3635133 := by
    simpa [prefixWord, tailWord_3635133, baseEnd_3635133] using wordTrace_append hprefix tailTrace_3635133
  have hstable : (prefixWord ++ tailWord_3635133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635133).length < 2 ^ (prefixWord ++ tailWord_3635133).sum := by decide
  have hdescent : baseEnd_3635133 < baseStart_3635133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635146 : List Nat := [3, 1, 2, 1, 2, 1, 2, 10]
def baseStart_3635146 : Nat := 118140960795 + 3635146 * 2 ^ 59
def prefixEnd_3635146 : Nat := 4983230072969 + 3 ^ 40 * 3635146 * 2
def baseEnd_3635146 : Nat := 138264973871773311722761

theorem tailTrace_3635146 : CollatzResearch.WordTrace tailWord_3635146 prefixEnd_3635146 138264973871773311722761 := by
  unfold tailWord_3635146
  simp only [CollatzResearch.WordTrace]
  refine ⟨33146166722123587588707323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88389777925662900236552861 33146166722123587588707323)
  ·
    refine ⟨49719250083185381383060985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33146166722123587588707323 49719250083185381383060985)
    ·
      refine ⟨37289437562389036037295739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49719250083185381383060985 37289437562389036037295739)
      ·
        refine ⟨55934156343583554055943609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37289437562389036037295739 55934156343583554055943609)
        ·
          refine ⟨41950617257687665541957707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55934156343583554055943609 41950617257687665541957707)
          ·
            refine ⟨62925925886531498312936561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41950617257687665541957707 62925925886531498312936561)
            ·
              refine ⟨47194444414898623734702421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62925925886531498312936561 47194444414898623734702421)
              ·
                refine ⟨138264973871773311722761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47194444414898623734702421 138264973871773311722761)
                ·
                  rfl

theorem cell22_3635146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 10].length) (baseStart_3635146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635146 prefixEnd_3635146 := by exact prefixLift 3635146
  have htrace : WordTrace (prefixWord ++ tailWord_3635146) baseStart_3635146 baseEnd_3635146 := by
    simpa [prefixWord, tailWord_3635146, baseEnd_3635146] using wordTrace_append hprefix tailTrace_3635146
  have hstable : (prefixWord ++ tailWord_3635146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635146).length < 2 ^ (prefixWord ++ tailWord_3635146).sum := by decide
  have hdescent : baseEnd_3635146 < baseStart_3635146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635148 : List Nat := [2, 2, 1, 4, 1, 3, 1, 1, 1, 6]
def baseStart_3635148 : Nat := 118140960795 + 3635148 * 2 ^ 59
def prefixEnd_3635148 : Nat := 4983230072969 + 3 ^ 40 * 3635148 * 2
def baseEnd_3635148 : Nat := 1244385449486832466954843

theorem tailTrace_3635148 : CollatzResearch.WordTrace tailWord_3635148 prefixEnd_3635148 1244385449486832466954843 := by
  unfold tailWord_3635148
  simp only [CollatzResearch.WordTrace]
  refine ⟨66292369917243552348201049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88389826556324736464268065 66292369917243552348201049)
  ·
    refine ⟨49719277437932664261150787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66292369917243552348201049 49719277437932664261150787)
    ·
      refine ⟨74578916156898996391726181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49719277437932664261150787 74578916156898996391726181)
      ·
        refine ⟨13983546779418561823448659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74578916156898996391726181 13983546779418561823448659)
        ·
          refine ⟨20975320169127842735172989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13983546779418561823448659 20975320169127842735172989)
          ·
            refine ⟨7865745063422941025689871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20975320169127842735172989 7865745063422941025689871)
            ·
              refine ⟨11798617595134411538534807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7865745063422941025689871 11798617595134411538534807)
              ·
                refine ⟨17697926392701617307802211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11798617595134411538534807 17697926392701617307802211)
                ·
                  refine ⟨26546889589052425961703317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17697926392701617307802211 26546889589052425961703317)
                  ·
                    refine ⟨1244385449486832466954843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26546889589052425961703317 1244385449486832466954843)
                    ·
                      rfl

theorem cell22_3635148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_3635148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635148 prefixEnd_3635148 := by exact prefixLift 3635148
  have htrace : WordTrace (prefixWord ++ tailWord_3635148) baseStart_3635148 baseEnd_3635148 := by
    simpa [prefixWord, tailWord_3635148, baseEnd_3635148] using wordTrace_append hprefix tailTrace_3635148
  have hstable : (prefixWord ++ tailWord_3635148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635148).length < 2 ^ (prefixWord ++ tailWord_3635148).sum := by decide
  have hdescent : baseEnd_3635148 < baseStart_3635148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635154 : List Nat := [3, 2, 2, 3, 2, 2, 2, 1, 1, 4]
def baseStart_3635154 : Nat := 118140960795 + 3635154 * 2 ^ 59
def prefixEnd_3635154 : Nat := 4983230072969 + 3 ^ 40 * 3635154 * 2
def baseEnd_3635154 : Nat := 1244387503409450451304825

theorem tailTrace_3635154 : CollatzResearch.WordTrace tailWord_3635154 prefixEnd_3635154 1244387503409450451304825 := by
  unfold tailWord_3635154
  simp only [CollatzResearch.WordTrace]
  refine ⟨33146239668116341930280129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88389972448310245147413677 33146239668116341930280129)
  ·
    refine ⟨24859679751087256447710097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33146239668116341930280129 24859679751087256447710097)
    ·
      refine ⟨18644759813315442335782573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24859679751087256447710097 18644759813315442335782573)
      ·
        refine ⟨6991784929993290875918465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18644759813315442335782573 6991784929993290875918465)
        ·
          refine ⟨5243838697494968156938849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6991784929993290875918465 5243838697494968156938849)
          ·
            refine ⟨3932879023121226117704137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5243838697494968156938849 3932879023121226117704137)
            ·
              refine ⟨2949659267340919588278103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3932879023121226117704137 2949659267340919588278103)
              ·
                refine ⟨4424488901011379382417155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2949659267340919588278103 4424488901011379382417155)
                ·
                  refine ⟨6636733351517069073625733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4424488901011379382417155 6636733351517069073625733)
                  ·
                    refine ⟨1244387503409450451304825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6636733351517069073625733 1244387503409450451304825)
                    ·
                      rfl

theorem cell22_3635154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_3635154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635154 prefixEnd_3635154 := by exact prefixLift 3635154
  have htrace : WordTrace (prefixWord ++ tailWord_3635154) baseStart_3635154 baseEnd_3635154 := by
    simpa [prefixWord, tailWord_3635154, baseEnd_3635154] using wordTrace_append hprefix tailTrace_3635154
  have hstable : (prefixWord ++ tailWord_3635154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635154).length < 2 ^ (prefixWord ++ tailWord_3635154).sum := by decide
  have hdescent : baseEnd_3635154 < baseStart_3635154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635167 : List Nat := [1, 1, 2, 3, 4, 3, 1, 2, 2, 3]
def baseStart_3635167 : Nat := 118140960795 + 3635167 * 2 ^ 59
def prefixEnd_3635167 : Nat := 4983230072969 + 3 ^ 40 * 3635167 * 2
def baseEnd_3635167 : Nat := 1244391953575122750729785

theorem tailTrace_3635167 : CollatzResearch.WordTrace tailWord_3635167 prefixEnd_3635167 1244391953575122750729785 := by
  unfold tailWord_3635167
  simp only [CollatzResearch.WordTrace]
  refine ⟨132585432821418270941343755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88390288547612180627562503 132585432821418270941343755)
  ·
    refine ⟨198878149232127406412015633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132585432821418270941343755 198878149232127406412015633)
    ·
      refine ⟨149158611924095554809011725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198878149232127406412015633 149158611924095554809011725)
      ·
        refine ⟨55934479471535833053379397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149158611924095554809011725 55934479471535833053379397)
        ·
          refine ⟨10487714900912968697508637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55934479471535833053379397 10487714900912968697508637)
          ·
            refine ⟨3932893087842363261565739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10487714900912968697508637 3932893087842363261565739)
            ·
              refine ⟨5899339631763544892348609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3932893087842363261565739 5899339631763544892348609)
              ·
                refine ⟨4424504723822658669261457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5899339631763544892348609 4424504723822658669261457)
                ·
                  refine ⟨3318378542866994001946093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4424504723822658669261457 3318378542866994001946093)
                  ·
                    refine ⟨1244391953575122750729785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3318378542866994001946093 1244391953575122750729785)
                    ·
                      rfl

theorem cell22_3635167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2, 3].length) (baseStart_3635167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635167 prefixEnd_3635167 := by exact prefixLift 3635167
  have htrace : WordTrace (prefixWord ++ tailWord_3635167) baseStart_3635167 baseEnd_3635167 := by
    simpa [prefixWord, tailWord_3635167, baseEnd_3635167] using wordTrace_append hprefix tailTrace_3635167
  have hstable : (prefixWord ++ tailWord_3635167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635167).length < 2 ^ (prefixWord ++ tailWord_3635167).sum := by decide
  have hdescent : baseEnd_3635167 < baseStart_3635167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635242 : List Nat := [3, 1, 4, 1, 2, 1, 4, 1, 5]
def baseStart_3635242 : Nat := 118140960795 + 3635242 * 2 ^ 59
def prefixEnd_3635242 : Nat := 4983230072969 + 3 ^ 40 * 3635242 * 2
def baseEnd_3635242 : Nat := 414805875869282518368185

theorem tailTrace_3635242 : CollatzResearch.WordTrace tailWord_3635242 prefixEnd_3635242 414805875869282518368185 := by
  unfold tailWord_3635242
  simp only [CollatzResearch.WordTrace]
  refine ⟨33147042074036639687580995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88392112197431039166882653 33147042074036639687580995)
  ·
    refine ⟨49720563111054959531371493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33147042074036639687580995 49720563111054959531371493)
    ·
      refine ⟨9322605583322804912132155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49720563111054959531371493 9322605583322804912132155)
      ·
        refine ⟨13983908374984207368198233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9322605583322804912132155 13983908374984207368198233)
        ·
          refine ⟨10487931281238155526148675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13983908374984207368198233 10487931281238155526148675)
          ·
            refine ⟨15731896921857233289223013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10487931281238155526148675 15731896921857233289223013)
            ·
              refine ⟨2949730672848231241729315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15731896921857233289223013 2949730672848231241729315)
              ·
                refine ⟨4424596009272346862593973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2949730672848231241729315 4424596009272346862593973)
                ·
                  refine ⟨414805875869282518368185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4424596009272346862593973 414805875869282518368185)
                  ·
                    rfl

theorem cell22_3635242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 5].length) (baseStart_3635242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635242 prefixEnd_3635242 := by exact prefixLift 3635242
  have htrace : WordTrace (prefixWord ++ tailWord_3635242) baseStart_3635242 baseEnd_3635242 := by
    simpa [prefixWord, tailWord_3635242, baseEnd_3635242] using wordTrace_append hprefix tailTrace_3635242
  have hstable : (prefixWord ++ tailWord_3635242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635242).length < 2 ^ (prefixWord ++ tailWord_3635242).sum := by decide
  have hdescent : baseEnd_3635242 < baseStart_3635242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635253 : List Nat := [1, 3, 3, 1, 1, 1, 2, 4, 6]
def baseStart_3635253 : Nat := 118140960795 + 3635253 * 2 ^ 59
def prefixEnd_3635253 : Nat := 4983230072969 + 3 ^ 40 * 3635253 * 2
def baseEnd_3635253 : Nat := 414807131044215731026507

theorem tailTrace_3635253 : CollatzResearch.WordTrace tailWord_3635253 prefixEnd_3635253 414807131044215731026507 := by
  unfold tailWord_3635253
  simp only [CollatzResearch.WordTrace]
  refine ⟨132588569499106707628974413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88392379666071138419316275 132588569499106707628974413)
  ·
    refine ⟨49720713562165015360865405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132588569499106707628974413 49720713562165015360865405)
    ·
      refine ⟨18645267585811880760324527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49720713562165015360865405 18645267585811880760324527)
      ·
        refine ⟨27967901378717821140486791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18645267585811880760324527 27967901378717821140486791)
        ·
          refine ⟨41951852068076731710730187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27967901378717821140486791 41951852068076731710730187)
          ·
            refine ⟨62927778102115097566095281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41951852068076731710730187 62927778102115097566095281)
            ·
              refine ⟨47195833576586323174571461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62927778102115097566095281 47195833576586323174571461)
              ·
                refine ⟨8849218795609935595232149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47195833576586323174571461 8849218795609935595232149)
                ·
                  refine ⟨414807131044215731026507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8849218795609935595232149 414807131044215731026507)
                  ·
                    rfl

theorem cell22_3635253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 6].length) (baseStart_3635253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635253 prefixEnd_3635253 := by exact prefixLift 3635253
  have htrace : WordTrace (prefixWord ++ tailWord_3635253) baseStart_3635253 baseEnd_3635253 := by
    simpa [prefixWord, tailWord_3635253, baseEnd_3635253] using wordTrace_append hprefix tailTrace_3635253
  have hstable : (prefixWord ++ tailWord_3635253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635253).length < 2 ^ (prefixWord ++ tailWord_3635253).sum := by decide
  have hdescent : baseEnd_3635253 < baseStart_3635253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635255 : List Nat := [1, 1, 3, 1, 2, 2, 5, 2, 1, 4]
def baseStart_3635255 : Nat := 118140960795 + 3635255 * 2 ^ 59
def prefixEnd_3635255 : Nat := 4983230072969 + 3 ^ 40 * 3635255 * 2
def baseEnd_3635255 : Nat := 1244422077773519854529515

theorem tailTrace_3635255 : CollatzResearch.WordTrace tailWord_3635255 prefixEnd_3635255 1244422077773519854529515 := by
  unfold tailWord_3635255
  simp only [CollatzResearch.WordTrace]
  refine ⟨132588642445099461970547219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88392428296732974647031479 132588642445099461970547219)
  ·
    refine ⟨198882963667649192955820829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132588642445099461970547219 198882963667649192955820829)
    ·
      refine ⟨74581111375368447358432811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198882963667649192955820829 74581111375368447358432811)
      ·
        refine ⟨111871667063052671037649217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74581111375368447358432811 111871667063052671037649217)
        ·
          refine ⟨83903750297289503278236913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111871667063052671037649217 83903750297289503278236913)
          ·
            refine ⟨62927812722967127458677685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83903750297289503278236913 62927812722967127458677685)
            ·
              refine ⟨5899482442778168199251033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62927812722967127458677685 5899482442778168199251033)
              ·
                refine ⟨4424611832083626149438275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5899482442778168199251033 4424611832083626149438275)
                ·
                  refine ⟨6636917748125439224157413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4424611832083626149438275 6636917748125439224157413)
                  ·
                    refine ⟨1244422077773519854529515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6636917748125439224157413 1244422077773519854529515)
                    ·
                      rfl

theorem cell22_3635255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_3635255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635255 prefixEnd_3635255 := by exact prefixLift 3635255
  have htrace : WordTrace (prefixWord ++ tailWord_3635255) baseStart_3635255 baseEnd_3635255 := by
    simpa [prefixWord, tailWord_3635255, baseEnd_3635255] using wordTrace_append hprefix tailTrace_3635255
  have hstable : (prefixWord ++ tailWord_3635255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635255).length < 2 ^ (prefixWord ++ tailWord_3635255).sum := by decide
  have hdescent : baseEnd_3635255 < baseStart_3635255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635287 : List Nat := [1, 1, 3, 2, 2, 1, 6, 2, 4]
def baseStart_3635287 : Nat := 118140960795 + 3635287 * 2 ^ 59
def prefixEnd_3635287 : Nat := 4983230072969 + 3 ^ 40 * 3635287 * 2
def baseEnd_3635287 : Nat := 414811010675827479243139

theorem tailTrace_3635287 : CollatzResearch.WordTrace tailWord_3635287 prefixEnd_3635287 414811010675827479243139 := by
  unfold tailWord_3635287
  simp only [CollatzResearch.WordTrace]
  refine ⟨132589809580983531435712115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88393206387322354290474743 132589809580983531435712115)
  ·
    refine ⟨198884714371475297153568173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132589809580983531435712115 198884714371475297153568173)
    ·
      refine ⟨74581767889303236432588065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198884714371475297153568173 74581767889303236432588065)
      ·
        refine ⟨55936325916977427324441049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74581767889303236432588065 55936325916977427324441049)
        ·
          refine ⟨41952244437733070493330787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55936325916977427324441049 41952244437733070493330787)
          ·
            refine ⟨62928366656599605739996181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41952244437733070493330787 62928366656599605739996181)
            ·
              refine ⟨2949767187028106519062321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62928366656599605739996181 2949767187028106519062321)
              ·
                refine ⟨2212325390271079889296741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2949767187028106519062321 2212325390271079889296741)
                ·
                  refine ⟨414811010675827479243139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2212325390271079889296741 414811010675827479243139)
                  ·
                    rfl

theorem cell22_3635287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2, 4].length) (baseStart_3635287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635287 prefixEnd_3635287 := by exact prefixLift 3635287
  have htrace : WordTrace (prefixWord ++ tailWord_3635287) baseStart_3635287 baseEnd_3635287 := by
    simpa [prefixWord, tailWord_3635287, baseEnd_3635287] using wordTrace_append hprefix tailTrace_3635287
  have hstable : (prefixWord ++ tailWord_3635287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635287).length < 2 ^ (prefixWord ++ tailWord_3635287).sum := by decide
  have hdescent : baseEnd_3635287 < baseStart_3635287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635394 : List Nat := [3, 5, 1, 1, 1, 1, 2, 1, 7]
def baseStart_3635394 : Nat := 118140960795 + 3635394 * 2 ^ 59
def prefixEnd_3635394 : Nat := 4983230072969 + 3 ^ 40 * 3635394 * 2
def baseEnd_3635394 : Nat := 414823220104723275101363

theorem tailTrace_3635394 : CollatzResearch.WordTrace tailWord_3635394 prefixEnd_3635394 414823220104723275101363 := by
  unfold tailWord_3635394
  simp only [CollatzResearch.WordTrace]
  refine ⟨33148428047898972177464309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88395808127730592473238157 33148428047898972177464309)
  ·
    refine ⟨3107665129490528641637279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33148428047898972177464309 3107665129490528641637279)
    ·
      refine ⟨4661497694235792962455919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3107665129490528641637279 4661497694235792962455919)
      ·
        refine ⟨6992246541353689443683879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4661497694235792962455919 6992246541353689443683879)
        ·
          refine ⟨10488369812030534165525819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6992246541353689443683879 10488369812030534165525819)
          ·
            refine ⟨15732554718045801248288729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10488369812030534165525819 15732554718045801248288729)
            ·
              refine ⟨11799416038534350936216547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15732554718045801248288729 11799416038534350936216547)
              ·
                refine ⟨17699124057801526404324821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11799416038534350936216547 17699124057801526404324821)
                ·
                  refine ⟨414823220104723275101363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17699124057801526404324821 414823220104723275101363)
                  ·
                    rfl

theorem cell22_3635394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_3635394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635394 prefixEnd_3635394 := by exact prefixLift 3635394
  have htrace : WordTrace (prefixWord ++ tailWord_3635394) baseStart_3635394 baseEnd_3635394 := by
    simpa [prefixWord, tailWord_3635394, baseEnd_3635394] using wordTrace_append hprefix tailTrace_3635394
  have hstable : (prefixWord ++ tailWord_3635394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635394).length < 2 ^ (prefixWord ++ tailWord_3635394).sum := by decide
  have hdescent : baseEnd_3635394 < baseStart_3635394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635452 : List Nat := [2, 2, 2, 1, 4, 1, 2, 2, 2, 4]
def baseStart_3635452 : Nat := 118140960795 + 3635452 * 2 ^ 59
def prefixEnd_3635452 : Nat := 4983230072969 + 3 ^ 40 * 3635452 * 2
def baseEnd_3635452 : Nat := 1244489514899477007353911

theorem tailTrace_3635452 : CollatzResearch.WordTrace tailWord_3635452 prefixEnd_3635452 1244489514899477007353911 := by
  unfold tailWord_3635452
  simp only [CollatzResearch.WordTrace]
  refine ⟨66297913812692882307734305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88397218416923843076979073 66297913812692882307734305)
  ·
    refine ⟨49723435359519661730800729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66297913812692882307734305 49723435359519661730800729)
    ·
      refine ⟨37292576519639746298100547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49723435359519661730800729 37292576519639746298100547)
      ·
        refine ⟨55938864779459619447150821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37292576519639746298100547 55938864779459619447150821)
        ·
          refine ⟨10488537146148678646340779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55938864779459619447150821 10488537146148678646340779)
          ·
            refine ⟨15732805719223017969511169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10488537146148678646340779 15732805719223017969511169)
            ·
              refine ⟨11799604289417263477133377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15732805719223017969511169 11799604289417263477133377)
              ·
                refine ⟨8849703217062947607850033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11799604289417263477133377 8849703217062947607850033)
                ·
                  refine ⟨6637277412797210705887525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8849703217062947607850033 6637277412797210705887525)
                  ·
                    refine ⟨1244489514899477007353911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6637277412797210705887525 1244489514899477007353911)
                    ·
                      rfl

theorem cell22_3635452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_3635452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635452 prefixEnd_3635452 := by exact prefixLift 3635452
  have htrace : WordTrace (prefixWord ++ tailWord_3635452) baseStart_3635452 baseEnd_3635452 := by
    simpa [prefixWord, tailWord_3635452, baseEnd_3635452] using wordTrace_append hprefix tailTrace_3635452
  have hstable : (prefixWord ++ tailWord_3635452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635452).length < 2 ^ (prefixWord ++ tailWord_3635452).sum := by decide
  have hdescent : baseEnd_3635452 < baseStart_3635452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635480 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 2, 6]
def baseStart_3635480 : Nat := 118140960795 + 3635480 * 2 ^ 59
def prefixEnd_3635480 : Nat := 4983230072969 + 3 ^ 40 * 3635480 * 2
def baseEnd_3635480 : Nat := 1244499099871694267653825

theorem tailTrace_3635480 : CollatzResearch.WordTrace tailWord_3635480 prefixEnd_3635480 1244499099871694267653825 := by
  unfold tailWord_3635480
  simp only [CollatzResearch.WordTrace]
  refine ⟨66298424434642162698743947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88397899246189550264991929 66298424434642162698743947)
  ·
    refine ⟨99447636651963244048115921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66298424434642162698743947 99447636651963244048115921)
    ·
      refine ⟨74585727488972433036086941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99447636651963244048115921 74585727488972433036086941)
      ·
        refine ⟨27969647808364662388532603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74585727488972433036086941 27969647808364662388532603)
        ·
          refine ⟨41954471712546993582798905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27969647808364662388532603 41954471712546993582798905)
          ·
            refine ⟨31465853784410245187099179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41954471712546993582798905 31465853784410245187099179)
            ·
              refine ⟨47198780676615367780648769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31465853784410245187099179 47198780676615367780648769)
              ·
                refine ⟨35399085507461525835486577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47198780676615367780648769 35399085507461525835486577)
                ·
                  refine ⟨26549314130596144376614933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35399085507461525835486577 26549314130596144376614933)
                  ·
                    refine ⟨1244499099871694267653825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26549314130596144376614933 1244499099871694267653825)
                    ·
                      rfl

theorem cell22_3635480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_3635480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635480 prefixEnd_3635480 := by exact prefixLift 3635480
  have htrace : WordTrace (prefixWord ++ tailWord_3635480) baseStart_3635480 baseEnd_3635480 := by
    simpa [prefixWord, tailWord_3635480, baseEnd_3635480] using wordTrace_append hprefix tailTrace_3635480
  have hstable : (prefixWord ++ tailWord_3635480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635480).length < 2 ^ (prefixWord ++ tailWord_3635480).sum := by decide
  have hdescent : baseEnd_3635480 < baseStart_3635480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635486 : List Nat := [4, 3, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_3635486 : Nat := 118140960795 + 3635486 * 2 ^ 59
def prefixEnd_3635486 : Nat := 4983230072969 + 3 ^ 40 * 3635486 * 2
def baseEnd_3635486 : Nat := 1244501153794312252003807

theorem tailTrace_3635486 : CollatzResearch.WordTrace tailWord_3635486 prefixEnd_3635486 1244501153794312252003807 := by
  unfold tailWord_3635486
  simp only [CollatzResearch.WordTrace]
  refine ⟨16574633463407823552775789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88398045138175058948137541 16574633463407823552775789)
  ·
    refine ⟨6215487548777933832290921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16574633463407823552775789 6215487548777933832290921)
    ·
      refine ⟨4661615661583450374218191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6215487548777933832290921 4661615661583450374218191)
      ·
        refine ⟨6992423492375175561327287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4661615661583450374218191 6992423492375175561327287)
        ·
          refine ⟨10488635238562763341990931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6992423492375175561327287 10488635238562763341990931)
          ·
            refine ⟨15732952857844145012986397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10488635238562763341990931 15732952857844145012986397)
            ·
              refine ⟨5899857321691554379869899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15732952857844145012986397 5899857321691554379869899)
              ·
                refine ⟨8849785982537331569804849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5899857321691554379869899 8849785982537331569804849)
                ·
                  refine ⟨6637339486902998677353637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8849785982537331569804849 6637339486902998677353637)
                  ·
                    refine ⟨1244501153794312252003807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6637339486902998677353637 1244501153794312252003807)
                    ·
                      rfl

theorem cell22_3635486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_3635486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635486 prefixEnd_3635486 := by exact prefixLift 3635486
  have htrace : WordTrace (prefixWord ++ tailWord_3635486) baseStart_3635486 baseEnd_3635486 := by
    simpa [prefixWord, tailWord_3635486, baseEnd_3635486] using wordTrace_append hprefix tailTrace_3635486
  have hstable : (prefixWord ++ tailWord_3635486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635486).length < 2 ^ (prefixWord ++ tailWord_3635486).sum := by decide
  have hdescent : baseEnd_3635486 < baseStart_3635486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635512 : List Nat := [2, 1, 2, 1, 3, 1, 5, 2, 5]
def baseStart_3635512 : Nat := 118140960795 + 3635512 * 2 ^ 59
def prefixEnd_3635512 : Nat := 4983230072969 + 3 ^ 40 * 3635512 * 2
def baseEnd_3635512 : Nat := 414836684708552283617909

theorem tailTrace_3635512 : CollatzResearch.WordTrace tailWord_3635512 prefixEnd_3635512 414836684708552283617909 := by
  unfold tailWord_3635512
  simp only [CollatzResearch.WordTrace]
  refine ⟨66299008002584197431326395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88398677336778929908435193 66299008002584197431326395)
  ·
    refine ⟨99448512003876296146989593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66299008002584197431326395 99448512003876296146989593)
    ·
      refine ⟨74586384002907222110242195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99448512003876296146989593 74586384002907222110242195)
      ·
        refine ⟨111879576004360833165363293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74586384002907222110242195 111879576004360833165363293)
        ·
          refine ⟨41954841001635312437011235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111879576004360833165363293 41954841001635312437011235)
          ·
            refine ⟨62932261502452968655516853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41954841001635312437011235 62932261502452968655516853)
            ·
              refine ⟨5899899515854965811454705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62932261502452968655516853 5899899515854965811454705)
              ·
                refine ⟨4424924636891224358591029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5899899515854965811454705 4424924636891224358591029)
                ·
                  refine ⟨414836684708552283617909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4424924636891224358591029 414836684708552283617909)
                  ·
                    rfl

theorem cell22_3635512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 5].length) (baseStart_3635512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635512 prefixEnd_3635512 := by exact prefixLift 3635512
  have htrace : WordTrace (prefixWord ++ tailWord_3635512) baseStart_3635512 baseEnd_3635512 := by
    simpa [prefixWord, tailWord_3635512, baseEnd_3635512] using wordTrace_append hprefix tailTrace_3635512
  have hstable : (prefixWord ++ tailWord_3635512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635512).length < 2 ^ (prefixWord ++ tailWord_3635512).sum := by decide
  have hdescent : baseEnd_3635512 < baseStart_3635512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635559 : List Nat := [1, 1, 5, 1, 3, 1, 2, 3, 1, 4]
def baseStart_3635559 : Nat := 118140960795 + 3635559 * 2 ^ 59
def prefixEnd_3635559 : Nat := 4983230072969 + 3 ^ 40 * 3635559 * 2
def baseEnd_3635559 : Nat := 1244526143186164394928583

theorem tailTrace_3635559 : CollatzResearch.WordTrace tailWord_3635559 prefixEnd_3635559 1244526143186164394928583 := by
  unfold tailWord_3635559
  simp only [CollatzResearch.WordTrace]
  refine ⟨132599730235998121889613731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88399820157332081259742487 132599730235998121889613731)
  ·
    refine ⟨198899595353997182834420597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132599730235998121889613731 198899595353997182834420597)
    ·
      refine ⟨18646837064437235890726931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198899595353997182834420597 18646837064437235890726931)
      ·
        refine ⟨27970255596655853836090397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18646837064437235890726931 27970255596655853836090397)
        ·
          refine ⟨10488845848745945188533899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27970255596655853836090397 10488845848745945188533899)
          ·
            refine ⟨15733268773118917782800849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10488845848745945188533899 15733268773118917782800849)
            ·
              refine ⟨11799951579839188337100637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15733268773118917782800849 11799951579839188337100637)
              ·
                refine ⟨4424981842439695626412739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11799951579839188337100637 4424981842439695626412739)
                ·
                  refine ⟨6637472763659543439619109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4424981842439695626412739 6637472763659543439619109)
                  ·
                    refine ⟨1244526143186164394928583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6637472763659543439619109 1244526143186164394928583)
                    ·
                      rfl

theorem cell22_3635559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_3635559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635559 prefixEnd_3635559 := by exact prefixLift 3635559
  have htrace : WordTrace (prefixWord ++ tailWord_3635559) baseStart_3635559 baseEnd_3635559 := by
    simpa [prefixWord, tailWord_3635559, baseEnd_3635559] using wordTrace_append hprefix tailTrace_3635559
  have hstable : (prefixWord ++ tailWord_3635559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635559).length < 2 ^ (prefixWord ++ tailWord_3635559).sum := by decide
  have hdescent : baseEnd_3635559 < baseStart_3635559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635634 : List Nat := [3, 2, 1, 1, 1, 1, 4, 3, 3, 3]
def baseStart_3635634 : Nat := 118140960795 + 3635634 * 2 ^ 59
def prefixEnd_3635634 : Nat := 4983230072969 + 3 ^ 40 * 3635634 * 2
def baseEnd_3635634 : Nat := 1244551817218889199303353

theorem tailTrace_3635634 : CollatzResearch.WordTrace tailWord_3635634 prefixEnd_3635634 1244551817218889199303353 := by
  unfold tailWord_3635634
  simp only [CollatzResearch.WordTrace]
  refine ⟨33150616427681602424648489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88401643807150939799062637 33150616427681602424648489)
  ·
    refine ⟨24862962320761201818486367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33150616427681602424648489 24862962320761201818486367)
    ·
      refine ⟨37294443481141802727729551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24862962320761201818486367 37294443481141802727729551)
      ·
        refine ⟨55941665221712704091594327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37294443481141802727729551 55941665221712704091594327)
        ·
          refine ⟨83912497832569056137391491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55941665221712704091594327 83912497832569056137391491)
          ·
            refine ⟨125868746748853584206087237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83912497832569056137391491 125868746748853584206087237)
            ·
              refine ⟨23600390015410047038641357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125868746748853584206087237 23600390015410047038641357)
              ·
                refine ⟨8850146255778767639490509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23600390015410047038641357 8850146255778767639490509)
                ·
                  refine ⟨3318804845917037864808941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8850146255778767639490509 3318804845917037864808941)
                  ·
                    refine ⟨1244551817218889199303353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3318804845917037864808941 1244551817218889199303353)
                    ·
                      rfl

theorem cell22_3635634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_3635634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635634 prefixEnd_3635634 := by exact prefixLift 3635634
  have htrace : WordTrace (prefixWord ++ tailWord_3635634) baseStart_3635634 baseEnd_3635634 := by
    simpa [prefixWord, tailWord_3635634, baseEnd_3635634] using wordTrace_append hprefix tailTrace_3635634
  have hstable : (prefixWord ++ tailWord_3635634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635634).length < 2 ^ (prefixWord ++ tailWord_3635634).sum := by decide
  have hdescent : baseEnd_3635634 < baseStart_3635634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635662 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 3, 7]
def baseStart_3635662 : Nat := 118140960795 + 3635662 * 2 ^ 59
def prefixEnd_3635662 : Nat := 4983230072969 + 3 ^ 40 * 3635662 * 2
def baseEnd_3635662 : Nat := 1244561402191106459603267

theorem tailTrace_3635662 : CollatzResearch.WordTrace tailWord_3635662 prefixEnd_3635662 1244561402191106459603267 := by
  unfold tailWord_3635662
  simp only [CollatzResearch.WordTrace]
  refine ⟨16575435869328121310076655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88402324636416646987075493 16575435869328121310076655)
  ·
    refine ⟨24863153803992181965114983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16575435869328121310076655 24863153803992181965114983)
    ·
      refine ⟨37294730705988272947672475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24863153803992181965114983 37294730705988272947672475)
      ·
        refine ⟨55942096058982409421508713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37294730705988272947672475 55942096058982409421508713)
        ·
          refine ⟨41956572044236807066131535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55942096058982409421508713 41956572044236807066131535)
          ·
            refine ⟨62934858066355210599197303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41956572044236807066131535 62934858066355210599197303)
            ·
              refine ⟨94402287099532815898795955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62934858066355210599197303 94402287099532815898795955)
              ·
                refine ⟨141603430649299223848193933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94402287099532815898795955 141603430649299223848193933)
                ·
                  refine ⟨53101286493487208943072725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141603430649299223848193933 53101286493487208943072725)
                  ·
                    refine ⟨1244561402191106459603267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53101286493487208943072725 1244561402191106459603267)
                    ·
                      rfl

theorem cell22_3635662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_3635662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635662 prefixEnd_3635662 := by exact prefixLift 3635662
  have htrace : WordTrace (prefixWord ++ tailWord_3635662) baseStart_3635662 baseEnd_3635662 := by
    simpa [prefixWord, tailWord_3635662, baseEnd_3635662] using wordTrace_append hprefix tailTrace_3635662
  have hstable : (prefixWord ++ tailWord_3635662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635662).length < 2 ^ (prefixWord ++ tailWord_3635662).sum := by decide
  have hdescent : baseEnd_3635662 < baseStart_3635662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635668 : List Nat := [2, 4, 1, 2, 2, 1, 1, 5, 1, 3]
def baseStart_3635668 : Nat := 118140960795 + 3635668 * 2 ^ 59
def prefixEnd_3635668 : Nat := 4983230072969 + 3 ^ 40 * 3635668 * 2
def baseEnd_3635668 : Nat := 1244563456113724443953249

theorem tailTrace_3635668 : CollatzResearch.WordTrace tailWord_3635668 prefixEnd_3635668 1244563456113724443953249 := by
  unfold tailWord_3635668
  simp only [CollatzResearch.WordTrace]
  refine ⟨66301852896301616752665829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88402470528402155670221105 66301852896301616752665829)
  ·
    refine ⟨12431597418056553141124843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66301852896301616752665829 12431597418056553141124843)
    ·
      refine ⟨18647396127084829711687265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12431597418056553141124843 18647396127084829711687265)
      ·
        refine ⟨13985547095313622283765449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18647396127084829711687265 13985547095313622283765449)
        ·
          refine ⟨10489160321485216712824087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13985547095313622283765449 10489160321485216712824087)
          ·
            refine ⟨15733740482227825069236131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10489160321485216712824087 15733740482227825069236131)
            ·
              refine ⟨23600610723341737603854197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15733740482227825069236131 23600610723341737603854197)
              ·
                refine ⟨2212557255313287900361331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23600610723341737603854197 2212557255313287900361331)
                ·
                  refine ⟨3318835882969931850541997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2212557255313287900361331 3318835882969931850541997)
                  ·
                    refine ⟨1244563456113724443953249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3318835882969931850541997 1244563456113724443953249)
                    ·
                      rfl

theorem cell22_3635668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_3635668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635668 prefixEnd_3635668 := by exact prefixLift 3635668
  have htrace : WordTrace (prefixWord ++ tailWord_3635668) baseStart_3635668 baseEnd_3635668 := by
    simpa [prefixWord, tailWord_3635668, baseEnd_3635668] using wordTrace_append hprefix tailTrace_3635668
  have hstable : (prefixWord ++ tailWord_3635668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635668).length < 2 ^ (prefixWord ++ tailWord_3635668).sum := by decide
  have hdescent : baseEnd_3635668 < baseStart_3635668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635698 : List Nat := [3, 2, 1, 4, 2, 1, 3, 1, 5]
def baseStart_3635698 : Nat := 118140960795 + 3635698 * 2 ^ 59
def prefixEnd_3635698 : Nat := 4983230072969 + 3 ^ 40 * 3635698 * 2
def baseEnd_3635698 : Nat := 414857908575604788567719

theorem tailTrace_3635698 : CollatzResearch.WordTrace tailWord_3635698 prefixEnd_3635698 414857908575604788567719 := by
  unfold tailWord_3635698
  simp only [CollatzResearch.WordTrace]
  refine ⟨33151199995623637157230937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88403199988329699085949165 33151199995623637157230937)
  ·
    refine ⟨24863399996717727867923203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33151199995623637157230937 24863399996717727867923203)
    ·
      refine ⟨37295099995076591801884805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24863399996717727867923203 37295099995076591801884805)
      ·
        refine ⟨6992831249076860962853401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37295099995076591801884805 6992831249076860962853401)
        ·
          refine ⟨5244623436807645722140051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6992831249076860962853401 5244623436807645722140051)
          ·
            refine ⟨7866935155211468583210077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5244623436807645722140051 7866935155211468583210077)
            ·
              refine ⟨2950100683204300718703779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7866935155211468583210077 2950100683204300718703779)
              ·
                refine ⟨4425151024806451078055669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2950100683204300718703779 4425151024806451078055669)
                ·
                  refine ⟨414857908575604788567719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4425151024806451078055669 414857908575604788567719)
                  ·
                    rfl

theorem cell22_3635698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_3635698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635698 prefixEnd_3635698 := by exact prefixLift 3635698
  have htrace : WordTrace (prefixWord ++ tailWord_3635698) baseStart_3635698 baseEnd_3635698 := by
    simpa [prefixWord, tailWord_3635698, baseEnd_3635698] using wordTrace_append hprefix tailTrace_3635698
  have hstable : (prefixWord ++ tailWord_3635698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635698).length < 2 ^ (prefixWord ++ tailWord_3635698).sum := by decide
  have hdescent : baseEnd_3635698 < baseStart_3635698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635741 : List Nat := [1, 4, 2, 2, 1, 2, 2, 1, 4, 3]
def baseStart_3635741 : Nat := 118140960795 + 3635741 * 2 ^ 59
def prefixEnd_3635741 : Nat := 4983230072969 + 3 ^ 40 * 3635741 * 2
def baseEnd_3635741 : Nat := 1244588445505576586878025

theorem tailTrace_3635741 : CollatzResearch.WordTrace tailWord_3635741 prefixEnd_3635741 1244588445505576586878025 := by
  unfold tailWord_3635741
  simp only [CollatzResearch.WordTrace]
  refine ⟨132606368321338766972739077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88404245547559177981826051 132606368321338766972739077)
  ·
    refine ⟨24863694060251018807388577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132606368321338766972739077 24863694060251018807388577)
    ·
      refine ⟨18647770545188264105541433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24863694060251018807388577 18647770545188264105541433)
      ·
        refine ⟨13985827908891198079156075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18647770545188264105541433 13985827908891198079156075)
        ·
          refine ⟨20978741863336797118734113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13985827908891198079156075 20978741863336797118734113)
          ·
            refine ⟨15734056397502597839050585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20978741863336797118734113 15734056397502597839050585)
            ·
              refine ⟨11800542298126948379287939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15734056397502597839050585 11800542298126948379287939)
              ·
                refine ⟨17700813447190422568931909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11800542298126948379287939 17700813447190422568931909)
                ·
                  refine ⟨3318902521348204231674733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17700813447190422568931909 3318902521348204231674733)
                  ·
                    refine ⟨1244588445505576586878025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3318902521348204231674733 1244588445505576586878025)
                    ·
                      rfl

theorem cell22_3635741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_3635741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635741 prefixEnd_3635741 := by exact prefixLift 3635741
  have htrace : WordTrace (prefixWord ++ tailWord_3635741) baseStart_3635741 baseEnd_3635741 := by
    simpa [prefixWord, tailWord_3635741, baseEnd_3635741] using wordTrace_append hprefix tailTrace_3635741
  have hstable : (prefixWord ++ tailWord_3635741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635741).length < 2 ^ (prefixWord ++ tailWord_3635741).sum := by decide
  have hdescent : baseEnd_3635741 < baseStart_3635741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635754 : List Nat := [3, 1, 4, 1, 1, 2, 1, 9]
def baseStart_3635754 : Nat := 118140960795 + 3635754 * 2 ^ 59
def prefixEnd_3635754 : Nat := 4983230072969 + 3 ^ 40 * 3635754 * 2
def baseEnd_3635754 : Nat := 138288099519027654033665

theorem tailTrace_3635754 : CollatzResearch.WordTrace tailWord_3635754 prefixEnd_3635754 138288099519027654033665 := by
  unfold tailWord_3635754
  simp only [CollatzResearch.WordTrace]
  refine ⟨33151710617572917548240579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88404561646861113461974877 33151710617572917548240579)
  ·
    refine ⟨49727565926359376322360869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33151710617572917548240579 49727565926359376322360869)
    ·
      refine ⟨9323918611192383060442663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49727565926359376322360869 9323918611192383060442663)
      ·
        refine ⟨13985877916788574590663995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9323918611192383060442663 13985877916788574590663995)
        ·
          refine ⟨20978816875182861885995993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13985877916788574590663995 20978816875182861885995993)
          ·
            refine ⟨15734112656387146414496995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20978816875182861885995993 15734112656387146414496995)
            ·
              refine ⟨23601168984580719621745493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15734112656387146414496995 23601168984580719621745493)
              ·
                refine ⟨138288099519027654033665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23601168984580719621745493 138288099519027654033665)
                ·
                  rfl

theorem cell22_3635754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 9].length) (baseStart_3635754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635754 prefixEnd_3635754 := by exact prefixLift 3635754
  have htrace : WordTrace (prefixWord ++ tailWord_3635754) baseStart_3635754 baseEnd_3635754 := by
    simpa [prefixWord, tailWord_3635754, baseEnd_3635754] using wordTrace_append hprefix tailTrace_3635754
  have hstable : (prefixWord ++ tailWord_3635754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635754).length < 2 ^ (prefixWord ++ tailWord_3635754).sum := by decide
  have hdescent : baseEnd_3635754 < baseStart_3635754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635850 : List Nat := [3, 1, 2, 3, 4, 1, 1, 2, 5]
def baseStart_3635850 : Nat := 118140960795 + 3635850 * 2 ^ 59
def prefixEnd_3635850 : Nat := 4983230072969 + 3 ^ 40 * 3635850 * 2
def baseEnd_3635850 : Nat := 414875252811045545300897

theorem tailTrace_3635850 : CollatzResearch.WordTrace tailWord_3635850 prefixEnd_3635850 414875252811045545300897 := by
  unfold tailWord_3635850
  simp only [CollatzResearch.WordTrace]
  refine ⟨33152585969485969647114251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88406895918629252392304669 33152585969485969647114251)
  ·
    refine ⟨49728878954228954470671377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33152585969485969647114251 49728878954228954470671377)
    ·
      refine ⟨37296659215671715853003533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49728878954228954470671377 37296659215671715853003533)
      ·
        refine ⟨13986247205876893444876325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37296659215671715853003533 13986247205876893444876325)
        ·
          refine ⟨2622421351101917520914311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13986247205876893444876325 2622421351101917520914311)
          ·
            refine ⟨3933632026652876281371467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2622421351101917520914311 3933632026652876281371467)
            ·
              refine ⟨5900448039979314422057201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3933632026652876281371467 5900448039979314422057201)
              ·
                refine ⟨4425336029984485816542901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5900448039979314422057201 4425336029984485816542901)
                ·
                  refine ⟨414875252811045545300897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4425336029984485816542901 414875252811045545300897)
                  ·
                    rfl

theorem cell22_3635850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 5].length) (baseStart_3635850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635850 prefixEnd_3635850 := by exact prefixLift 3635850
  have htrace : WordTrace (prefixWord ++ tailWord_3635850) baseStart_3635850 baseEnd_3635850 := by
    simpa [prefixWord, tailWord_3635850, baseEnd_3635850] using wordTrace_append hprefix tailTrace_3635850
  have hstable : (prefixWord ++ tailWord_3635850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635850).length < 2 ^ (prefixWord ++ tailWord_3635850).sum := by decide
  have hdescent : baseEnd_3635850 < baseStart_3635850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635893 : List Nat := [1, 3, 3, 3, 1, 1, 1, 2, 4, 3]
def baseStart_3635893 : Nat := 118140960795 + 3635893 * 2 ^ 59
def prefixEnd_3635893 : Nat := 4983230072969 + 3 ^ 40 * 3635893 * 2
def baseEnd_3635893 : Nat := 1244640478211898857077559

theorem tailTrace_3635893 : CollatzResearch.WordTrace tailWord_3635893 prefixEnd_3635893 1244640478211898857077559 := by
  unfold tailWord_3635893
  simp only [CollatzResearch.WordTrace]
  refine ⟨132611912216788096932272333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88407941477858731288181555 132611912216788096932272333)
  ·
    refine ⟨49729467081295536349602125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132611912216788096932272333 49729467081295536349602125)
    ·
      refine ⟨18648550155485826131100797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49729467081295536349602125 18648550155485826131100797)
      ·
        refine ⟨6993206308307184799162799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18648550155485826131100797 6993206308307184799162799)
        ·
          refine ⟨10489809462460777198744199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6993206308307184799162799 10489809462460777198744199)
          ·
            refine ⟨15734714193691165798116299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10489809462460777198744199 15734714193691165798116299)
            ·
              refine ⟨23602071290536748697174449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15734714193691165798116299 23602071290536748697174449)
              ·
                refine ⟨17701553467902561522880837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23602071290536748697174449 17701553467902561522880837)
                ·
                  refine ⟨3319041275231730285540157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17701553467902561522880837 3319041275231730285540157)
                  ·
                    refine ⟨1244640478211898857077559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3319041275231730285540157 1244640478211898857077559)
                    ·
                      rfl

theorem cell22_3635893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_3635893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635893 prefixEnd_3635893 := by exact prefixLift 3635893
  have htrace : WordTrace (prefixWord ++ tailWord_3635893) baseStart_3635893 baseEnd_3635893 := by
    simpa [prefixWord, tailWord_3635893, baseEnd_3635893] using wordTrace_append hprefix tailTrace_3635893
  have hstable : (prefixWord ++ tailWord_3635893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635893).length < 2 ^ (prefixWord ++ tailWord_3635893).sum := by decide
  have hdescent : baseEnd_3635893 < baseStart_3635893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635895 : List Nat := [1, 1, 3, 1, 6, 2, 1, 3, 4]
def baseStart_3635895 : Nat := 118140960795 + 3635895 * 2 ^ 59
def prefixEnd_3635895 : Nat := 4983230072969 + 3 ^ 40 * 3635895 * 2
def baseEnd_3635895 : Nat := 414880387617590506175851

theorem tailTrace_3635895 : CollatzResearch.WordTrace tailWord_3635895 prefixEnd_3635895 414880387617590506175851 := by
  unfold tailWord_3635895
  simp only [CollatzResearch.WordTrace]
  refine ⟨132611985162780851273845139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88407990108520567515896759 132611985162780851273845139)
  ·
    refine ⟨198917977744171276910767709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132611985162780851273845139 198917977744171276910767709)
    ·
      refine ⟨74594241654064228841537891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198917977744171276910767709 74594241654064228841537891)
      ·
        refine ⟨111891362481096343262306837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74594241654064228841537891 111891362481096343262306837)
        ·
          refine ⟨5244907616301391090420633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 111891362481096343262306837 5244907616301391090420633)
          ·
            refine ⟨3933680712226043317815475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5244907616301391090420633 3933680712226043317815475)
            ·
              refine ⟨5900521068339064976723213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3933680712226043317815475 5900521068339064976723213)
              ·
                refine ⟨2212695400627149366271205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5900521068339064976723213 2212695400627149366271205)
                ·
                  refine ⟨414880387617590506175851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2212695400627149366271205 414880387617590506175851)
                  ·
                    rfl

theorem cell22_3635895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3, 4].length) (baseStart_3635895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635895 prefixEnd_3635895 := by exact prefixLift 3635895
  have htrace : WordTrace (prefixWord ++ tailWord_3635895) baseStart_3635895 baseEnd_3635895 := by
    simpa [prefixWord, tailWord_3635895, baseEnd_3635895] using wordTrace_append hprefix tailTrace_3635895
  have hstable : (prefixWord ++ tailWord_3635895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635895).length < 2 ^ (prefixWord ++ tailWord_3635895).sum := by decide
  have hdescent : baseEnd_3635895 < baseStart_3635895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635908 : List Nat := [2, 3, 3, 1, 1, 3, 1, 2, 2, 4]
def baseStart_3635908 : Nat := 118140960795 + 3635908 * 2 ^ 59
def prefixEnd_3635908 : Nat := 4983230072969 + 3 ^ 40 * 3635908 * 2
def baseEnd_3635908 : Nat := 1244645613018443817952513

theorem tailTrace_3635908 : CollatzResearch.WordTrace tailWord_3635908 prefixEnd_3635908 1244645613018443817952513 := by
  unfold tailWord_3635908
  simp only [CollatzResearch.WordTrace]
  refine ⟨66306229655866877247034189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88408306207822502996045585 66306229655866877247034189)
  ·
    refine ⟨24864836120950078967637821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66306229655866877247034189 24864836120950078967637821)
    ·
      refine ⟨9324313545356279612864183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24864836120950078967637821 9324313545356279612864183)
      ·
        refine ⟨13986470318034419419296275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9324313545356279612864183 13986470318034419419296275)
        ·
          refine ⟨20979705477051629128944413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13986470318034419419296275 20979705477051629128944413)
          ·
            refine ⟨7867389553894360923354155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20979705477051629128944413 7867389553894360923354155)
            ·
              refine ⟨11801084330841541385031233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7867389553894360923354155 11801084330841541385031233)
              ·
                refine ⟨8850813248131156038773425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11801084330841541385031233 8850813248131156038773425)
                ·
                  refine ⟨6638109936098367029080069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8850813248131156038773425 6638109936098367029080069)
                  ·
                    refine ⟨1244645613018443817952513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6638109936098367029080069 1244645613018443817952513)
                    ·
                      rfl

theorem cell22_3635908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_3635908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635908 prefixEnd_3635908 := by exact prefixLift 3635908
  have htrace : WordTrace (prefixWord ++ tailWord_3635908) baseStart_3635908 baseEnd_3635908 := by
    simpa [prefixWord, tailWord_3635908, baseEnd_3635908] using wordTrace_append hprefix tailTrace_3635908
  have hstable : (prefixWord ++ tailWord_3635908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635908).length < 2 ^ (prefixWord ++ tailWord_3635908).sum := by decide
  have hdescent : baseEnd_3635908 < baseStart_3635908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635996 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 8]
def baseStart_3635996 : Nat := 118140960795 + 3635996 * 2 ^ 59
def prefixEnd_3635996 : Nat := 4983230072969 + 3 ^ 40 * 3635996 * 2
def baseEnd_3635996 : Nat := 414891912405613640584081

theorem tailTrace_3635996 : CollatzResearch.WordTrace tailWord_3635996 prefixEnd_3635996 414891912405613640584081 := by
  unfold tailWord_3635996
  simp only [CollatzResearch.WordTrace]
  refine ⟨66307834467707472761635921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88410445956943297015514561 66307834467707472761635921)
  ·
    refine ⟨49730875850780604571226941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66307834467707472761635921 49730875850780604571226941)
    ·
      refine ⟨18649078444042726714210103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49730875850780604571226941 18649078444042726714210103)
      ·
        refine ⟨27973617666064090071315155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18649078444042726714210103 27973617666064090071315155)
        ·
          refine ⟨41960426499096135106972733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27973617666064090071315155 41960426499096135106972733)
          ·
            refine ⟨15735159937161050665114775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41960426499096135106972733 15735159937161050665114775)
            ·
              refine ⟨23602739905741575997672163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15735159937161050665114775 23602739905741575997672163)
              ·
                refine ⟨35404109858612363996508245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23602739905741575997672163 35404109858612363996508245)
                ·
                  refine ⟨414891912405613640584081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35404109858612363996508245 414891912405613640584081)
                  ·
                    rfl

theorem cell22_3635996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_3635996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3635996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3635996 prefixEnd_3635996 := by exact prefixLift 3635996
  have htrace : WordTrace (prefixWord ++ tailWord_3635996) baseStart_3635996 baseEnd_3635996 := by
    simpa [prefixWord, tailWord_3635996, baseEnd_3635996] using wordTrace_append hprefix tailTrace_3635996
  have hstable : (prefixWord ++ tailWord_3635996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635996).length < 2 ^ (prefixWord ++ tailWord_3635996).sum := by decide
  have hdescent : baseEnd_3635996 < baseStart_3635996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636030 : List Nat := [4, 2, 1, 2, 3, 1, 2, 1, 6]
def baseStart_3636030 : Nat := 118140960795 + 3636030 * 2 ^ 59
def prefixEnd_3636030 : Nat := 4983230072969 + 3 ^ 40 * 3636030 * 2
def baseEnd_3636030 : Nat := 414895792037225388800713

theorem tailTrace_3636030 : CollatzResearch.WordTrace tailWord_3636030 prefixEnd_3636030 414895792037225388800713 := by
  unfold tailWord_3636030
  simp only [CollatzResearch.WordTrace]
  refine ⟨16577113627161471166251193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88411272678194512886673029 16577113627161471166251193)
  ·
    refine ⟨12432835220371103374688395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16577113627161471166251193 12432835220371103374688395)
    ·
      refine ⟨18649252830556655062032593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12432835220371103374688395 18649252830556655062032593)
      ·
        refine ⟨13986939622917491296524445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18649252830556655062032593 13986939622917491296524445)
        ·
          refine ⟨5245102358594059236196667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13986939622917491296524445 5245102358594059236196667)
          ·
            refine ⟨7867653537891088854295001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5245102358594059236196667 7867653537891088854295001)
            ·
              refine ⟨5900740153418316640721251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7867653537891088854295001 5900740153418316640721251)
              ·
                refine ⟨8851110230127474961081877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5900740153418316640721251 8851110230127474961081877)
                ·
                  refine ⟨414895792037225388800713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8851110230127474961081877 414895792037225388800713)
                  ·
                    rfl

theorem cell22_3636030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_3636030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3636030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3636030 prefixEnd_3636030 := by exact prefixLift 3636030
  have htrace : WordTrace (prefixWord ++ tailWord_3636030) baseStart_3636030 baseEnd_3636030 := by
    simpa [prefixWord, tailWord_3636030, baseEnd_3636030] using wordTrace_append hprefix tailTrace_3636030
  have hstable : (prefixWord ++ tailWord_3636030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636030).length < 2 ^ (prefixWord ++ tailWord_3636030).sum := by decide
  have hdescent : baseEnd_3636030 < baseStart_3636030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636058 : List Nat := [3, 1, 1, 2, 1, 4, 4, 6]
def baseStart_3636058 : Nat := 118140960795 + 3636058 * 2 ^ 59
def prefixEnd_3636058 : Nat := 4983230072969 + 3 ^ 40 * 3636058 * 2
def baseEnd_3636058 : Nat := 138299662342654825189117

theorem tailTrace_3636058 : CollatzResearch.WordTrace tailWord_3636058 prefixEnd_3636058 138299662342654825189117 := by
  unfold tailWord_3636058
  simp only [CollatzResearch.WordTrace]
  refine ⟨33154482565297582528007207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88411953507460220074685885 33154482565297582528007207)
  ·
    refine ⟨49731723847946373792010811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33154482565297582528007207 49731723847946373792010811)
    ·
      refine ⟨74597585771919560688016217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49731723847946373792010811 74597585771919560688016217)
      ·
        refine ⟨55948189328939670516012163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74597585771919560688016217 55948189328939670516012163)
        ·
          refine ⟨83922283993409505774018245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55948189328939670516012163 83922283993409505774018245)
          ·
            refine ⟨15735428248764282332628421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83922283993409505774018245 15735428248764282332628421)
            ·
              refine ⟨2950392796643302937367829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15735428248764282332628421 2950392796643302937367829)
              ·
                refine ⟨138299662342654825189117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2950392796643302937367829 138299662342654825189117)
                ·
                  rfl

theorem cell22_3636058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 6].length) (baseStart_3636058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3636058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3636058 prefixEnd_3636058 := by exact prefixLift 3636058
  have htrace : WordTrace (prefixWord ++ tailWord_3636058) baseStart_3636058 baseEnd_3636058 := by
    simpa [prefixWord, tailWord_3636058, baseEnd_3636058] using wordTrace_append hprefix tailTrace_3636058
  have hstable : (prefixWord ++ tailWord_3636058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636058).length < 2 ^ (prefixWord ++ tailWord_3636058).sum := by decide
  have hdescent : baseEnd_3636058 < baseStart_3636058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636141 : List Nat := [1, 5, 2, 3, 1, 1, 1, 4, 1, 3]
def baseStart_3636141 : Nat := 118140960795 + 3636141 * 2 ^ 59
def prefixEnd_3636141 : Nat := 4983230072969 + 3 ^ 40 * 3636141 * 2
def baseEnd_3636141 : Nat := 1244725373680108876876799

theorem tailTrace_3636141 : CollatzResearch.WordTrace tailWord_3636141 prefixEnd_3636141 1244725373680108876876799 := by
  unfold tailWord_3636141
  simp only [CollatzResearch.WordTrace]
  refine ⟨132620957519889635287300277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88413971679926423524866851 132620957519889635287300277)
  ·
    refine ⟨12433214767489653308184401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132620957519889635287300277 12433214767489653308184401)
    ·
      refine ⟨9324911075617239981138301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12433214767489653308184401 9324911075617239981138301)
      ·
        refine ⟨3496841653356464992926863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9324911075617239981138301 3496841653356464992926863)
        ·
          refine ⟨5245262480034697489390295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3496841653356464992926863 5245262480034697489390295)
          ·
            refine ⟨7867893720052046234085443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5245262480034697489390295 7867893720052046234085443)
            ·
              refine ⟨11801840580078069351128165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7867893720052046234085443 11801840580078069351128165)
              ·
                refine ⟨2212845108764638003336531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11801840580078069351128165 2212845108764638003336531)
                ·
                  refine ⟨3319267663146957005004797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2212845108764638003336531 3319267663146957005004797)
                  ·
                    refine ⟨1244725373680108876876799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3319267663146957005004797 1244725373680108876876799)
                    ·
                      rfl

theorem cell22_3636141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_3636141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3636141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3636141 prefixEnd_3636141 := by exact prefixLift 3636141
  have htrace : WordTrace (prefixWord ++ tailWord_3636141) baseStart_3636141 baseEnd_3636141 := by
    simpa [prefixWord, tailWord_3636141, baseEnd_3636141] using wordTrace_append hprefix tailTrace_3636141
  have hstable : (prefixWord ++ tailWord_3636141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636141).length < 2 ^ (prefixWord ++ tailWord_3636141).sum := by decide
  have hdescent : baseEnd_3636141 < baseStart_3636141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636180 : List Nat := [2, 4, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_3636180 : Nat := 118140960795 + 3636180 * 2 ^ 59
def prefixEnd_3636180 : Nat := 4983230072969 + 3 ^ 40 * 3636180 * 2
def baseEnd_3636180 : Nat := 1244738724177125775151679

theorem tailTrace_3636180 : CollatzResearch.WordTrace tailWord_3636180 prefixEnd_3636180 1244738724177125775151679 := by
  unfold tailWord_3636180
  simp only [CollatzResearch.WordTrace]
  refine ⟨66311189983374172473984997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88414919977832229965313329 66311189983374172473984997)
  ·
    refine ⟨12433348121882657338872187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66311189983374172473984997 12433348121882657338872187)
    ·
      refine ⟨18650022182823986008308281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12433348121882657338872187 18650022182823986008308281)
      ·
        refine ⟨13987516637117989506231211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18650022182823986008308281 13987516637117989506231211)
        ·
          refine ⟨20981274955676984259346817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13987516637117989506231211 20981274955676984259346817)
          ·
            refine ⟨15735956216757738194510113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20981274955676984259346817 15735956216757738194510113)
            ·
              refine ⟨11801967162568303645882585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15735956216757738194510113 11801967162568303645882585)
              ·
                refine ⟨8851475371926227734411939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11801967162568303645882585 8851475371926227734411939)
                ·
                  refine ⟨13277213057889341601617909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8851475371926227734411939 13277213057889341601617909)
                  ·
                    refine ⟨1244738724177125775151679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13277213057889341601617909 1244738724177125775151679)
                    ·
                      rfl

theorem cell22_3636180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_3636180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3636180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3636180 prefixEnd_3636180 := by exact prefixLift 3636180
  have htrace : WordTrace (prefixWord ++ tailWord_3636180) baseStart_3636180 baseEnd_3636180 := by
    simpa [prefixWord, tailWord_3636180, baseEnd_3636180] using wordTrace_append hprefix tailTrace_3636180
  have hstable : (prefixWord ++ tailWord_3636180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636180).length < 2 ^ (prefixWord ++ tailWord_3636180).sum := by decide
  have hdescent : baseEnd_3636180 < baseStart_3636180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636270 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 1, 7]
def baseStart_3636270 : Nat := 118140960795 + 3636270 * 2 ^ 59
def prefixEnd_3636270 : Nat := 4983230072969 + 3 ^ 40 * 3636270 * 2
def baseEnd_3636270 : Nat := 1244769533016395540401403

theorem tailTrace_3636270 : CollatzResearch.WordTrace tailWord_3636270 prefixEnd_3636270 1244769533016395540401403 := by
  unfold tailWord_3636270
  simp only [CollatzResearch.WordTrace]
  refine ⟨16578207817052786289843283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88417108357614860212497509 16578207817052786289843283)
  ·
    refine ⟨24867311725579179434764925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16578207817052786289843283 24867311725579179434764925)
    ·
      refine ⟨9325241897092192288036847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24867311725579179434764925 9325241897092192288036847)
      ·
        refine ⟨13987862845638288432055271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9325241897092192288036847 13987862845638288432055271)
        ·
          refine ⟨20981794268457432648082907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13987862845638288432055271 20981794268457432648082907)
          ·
            refine ⟨31472691402686148972124361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20981794268457432648082907 31472691402686148972124361)
            ·
              refine ⟨23604518552014611729093271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31472691402686148972124361 23604518552014611729093271)
              ·
                refine ⟨35406777828021917593639907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23604518552014611729093271 35406777828021917593639907)
                ·
                  refine ⟨53110166742032876390459861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35406777828021917593639907 53110166742032876390459861)
                  ·
                    refine ⟨1244769533016395540401403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53110166742032876390459861 1244769533016395540401403)
                    ·
                      rfl

theorem cell22_3636270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_3636270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3636270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3636270 prefixEnd_3636270 := by exact prefixLift 3636270
  have htrace : WordTrace (prefixWord ++ tailWord_3636270) baseStart_3636270 baseEnd_3636270 := by
    simpa [prefixWord, tailWord_3636270, baseEnd_3636270] using wordTrace_append hprefix tailTrace_3636270
  have hstable : (prefixWord ++ tailWord_3636270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636270).length < 2 ^ (prefixWord ++ tailWord_3636270).sum := by decide
  have hdescent : baseEnd_3636270 < baseStart_3636270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636332 : List Nat := [2, 2, 1, 1, 3, 2, 1, 5, 2, 3]
def baseStart_3636332 : Nat := 118140960795 + 3636332 * 2 ^ 59
def prefixEnd_3636332 : Nat := 4983230072969 + 3 ^ 40 * 3636332 * 2
def baseEnd_3636332 : Nat := 1244790756883448045351213

theorem tailTrace_3636332 : CollatzResearch.WordTrace tailWord_3636332 prefixEnd_3636332 1244790756883448045351213 := by
  unfold tailWord_3636332
  simp only [CollatzResearch.WordTrace]
  refine ⟨66313961931098837453751625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88418615908131783271668833 66313961931098837453751625)
  ·
    refine ⟨49735471448324128090313719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66313961931098837453751625 49735471448324128090313719)
    ·
      refine ⟨74603207172486192135470579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49735471448324128090313719 74603207172486192135470579)
      ·
        refine ⟨111904810758729288203205869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74603207172486192135470579 111904810758729288203205869)
        ·
          refine ⟨41964304034523483076202201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111904810758729288203205869 41964304034523483076202201)
          ·
            refine ⟨31473228025892612307151651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41964304034523483076202201 31473228025892612307151651)
            ·
              refine ⟨47209842038838918460727477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31473228025892612307151651 47209842038838918460727477)
              ·
                refine ⟨4425922691141148605693201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47209842038838918460727477 4425922691141148605693201)
                ·
                  refine ⟨3319442018355861454269901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4425922691141148605693201 3319442018355861454269901)
                  ·
                    refine ⟨1244790756883448045351213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3319442018355861454269901 1244790756883448045351213)
                    ·
                      rfl

theorem cell22_3636332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 3].length) (baseStart_3636332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3636332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3636332 prefixEnd_3636332 := by exact prefixLift 3636332
  have htrace : WordTrace (prefixWord ++ tailWord_3636332) baseStart_3636332 baseEnd_3636332 := by
    simpa [prefixWord, tailWord_3636332, baseEnd_3636332] using wordTrace_append hprefix tailTrace_3636332
  have hstable : (prefixWord ++ tailWord_3636332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636332).length < 2 ^ (prefixWord ++ tailWord_3636332).sum := by decide
  have hdescent : baseEnd_3636332 < baseStart_3636332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636366 : List Nat := [4, 1, 1, 3, 2, 3, 1, 2, 2, 3]
def baseStart_3636366 : Nat := 118140960795 + 3636366 * 2 ^ 59
def prefixEnd_3636366 : Nat := 4983230072969 + 3 ^ 40 * 3636366 * 2
def baseEnd_3636366 : Nat := 1244802395778283290001109

theorem tailTrace_3636366 : CollatzResearch.WordTrace tailWord_3636366 prefixEnd_3636366 1244802395778283290001109 := by
  unfold tailWord_3636366
  simp only [CollatzResearch.WordTrace]
  refine ⟨16578645493009312339280119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88419442629382999142827301 16578645493009312339280119)
  ·
    refine ⟨24867968239513968508920179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16578645493009312339280119 24867968239513968508920179)
    ·
      refine ⟨37301952359270952763380269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24867968239513968508920179 37301952359270952763380269)
      ·
        refine ⟨13988232134726607286267601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37301952359270952763380269 13988232134726607286267601)
        ·
          refine ⟨10491174101044955464700701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13988232134726607286267601 10491174101044955464700701)
          ·
            refine ⟨3934190287891858299262763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10491174101044955464700701 3934190287891858299262763)
            ·
              refine ⟨5901285431837787448894145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3934190287891858299262763 5901285431837787448894145)
              ·
                refine ⟨4425964073878340586670609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5901285431837787448894145 4425964073878340586670609)
                ·
                  refine ⟨3319473055408755440002957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4425964073878340586670609 3319473055408755440002957)
                  ·
                    refine ⟨1244802395778283290001109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3319473055408755440002957 1244802395778283290001109)
                    ·
                      rfl

theorem cell22_3636366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_3636366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3636366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3636366 prefixEnd_3636366 := by exact prefixLift 3636366
  have htrace : WordTrace (prefixWord ++ tailWord_3636366) baseStart_3636366 baseEnd_3636366 := by
    simpa [prefixWord, tailWord_3636366, baseEnd_3636366] using wordTrace_append hprefix tailTrace_3636366
  have hstable : (prefixWord ++ tailWord_3636366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636366).length < 2 ^ (prefixWord ++ tailWord_3636366).sum := by decide
  have hdescent : baseEnd_3636366 < baseStart_3636366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636467 : List Nat := [1, 1, 1, 2, 2, 6, 1, 2, 1, 5]
def baseStart_3636467 : Nat := 118140960795 + 3636467 * 2 ^ 59
def prefixEnd_3636467 : Nat := 4983230072969 + 3 ^ 40 * 3636467 * 2
def baseEnd_3636467 : Nat := 1244836970142352693225799

theorem tailTrace_3636467 : CollatzResearch.WordTrace tailWord_3636467 prefixEnd_3636467 1244836970142352693225799 := by
  unfold tailWord_3636467
  simp only [CollatzResearch.WordTrace]
  refine ⟨132632847716708592963667655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88421898477805728642445103 132632847716708592963667655)
  ·
    refine ⟨198949271575062889445501483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132632847716708592963667655 198949271575062889445501483)
    ·
      refine ⟨298423907362594334168252225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198949271575062889445501483 298423907362594334168252225)
      ·
        refine ⟨223817930521945750626189169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298423907362594334168252225 223817930521945750626189169)
        ·
          refine ⟨167863447891459312969641877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223817930521945750626189169 167863447891459312969641877)
          ·
            refine ⟨7868599119912155295451963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 167863447891459312969641877 7868599119912155295451963)
            ·
              refine ⟨11802898679868232943177945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7868599119912155295451963 11802898679868232943177945)
              ·
                refine ⟨8852174009901174707383459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11802898679868232943177945 8852174009901174707383459)
                ·
                  refine ⟨13278261014851762061075189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8852174009901174707383459 13278261014851762061075189)
                  ·
                    refine ⟨1244836970142352693225799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13278261014851762061075189 1244836970142352693225799)
                    ·
                      rfl

theorem cell22_3636467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 5].length) (baseStart_3636467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3636467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3636467 prefixEnd_3636467 := by exact prefixLift 3636467
  have htrace : WordTrace (prefixWord ++ tailWord_3636467) baseStart_3636467 baseEnd_3636467 := by
    simpa [prefixWord, tailWord_3636467, baseEnd_3636467] using wordTrace_append hprefix tailTrace_3636467
  have hstable : (prefixWord ++ tailWord_3636467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636467).length < 2 ^ (prefixWord ++ tailWord_3636467).sum := by decide
  have hdescent : baseEnd_3636467 < baseStart_3636467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636495 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 4, 7]
def baseStart_3636495 : Nat := 118140960795 + 3636495 * 2 ^ 59
def prefixEnd_3636495 : Nat := 4983230072969 + 3 ^ 40 * 3636495 * 2
def baseEnd_3636495 : Nat := 1244846555114569953525713

theorem tailTrace_3636495 : CollatzResearch.WordTrace tailWord_3636495 prefixEnd_3636495 1244846555114569953525713 := by
  unfold tailWord_3636495
  simp only [CollatzResearch.WordTrace]
  refine ⟨132633868960607153745686939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88422579307071435830457959 132633868960607153745686939)
  ·
    refine ⟨198950803440910730618530409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132633868960607153745686939 198950803440910730618530409)
    ·
      refine ⟨149213102580683047963897807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198950803440910730618530409 149213102580683047963897807)
      ·
        refine ⟨223819653871024571945846711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149213102580683047963897807 223819653871024571945846711)
        ·
          refine ⟨335729480806536857918770067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223819653871024571945846711 335729480806536857918770067)
          ·
            refine ⟨503594221209805286878155101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335729480806536857918770067 503594221209805286878155101)
            ·
              refine ⟨188847832953676982579308163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 503594221209805286878155101 188847832953676982579308163)
              ·
                refine ⟨283271749430515473868962245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188847832953676982579308163 283271749430515473868962245)
                ·
                  refine ⟨53113453018221651350430421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 283271749430515473868962245 53113453018221651350430421)
                  ·
                    refine ⟨1244846555114569953525713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53113453018221651350430421 1244846555114569953525713)
                    ·
                      rfl

theorem cell22_3636495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_3636495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3636495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3636495 prefixEnd_3636495 := by exact prefixLift 3636495
  have htrace : WordTrace (prefixWord ++ tailWord_3636495) baseStart_3636495 baseEnd_3636495 := by
    simpa [prefixWord, tailWord_3636495, baseEnd_3636495] using wordTrace_append hprefix tailTrace_3636495
  have hstable : (prefixWord ++ tailWord_3636495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636495).length < 2 ^ (prefixWord ++ tailWord_3636495).sum := by decide
  have hdescent : baseEnd_3636495 < baseStart_3636495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636602 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 3, 5]
def baseStart_3636602 : Nat := 118140960795 + 3636602 * 2 ^ 59
def prefixEnd_3636602 : Nat := 4983230072969 + 3 ^ 40 * 3636602 * 2
def baseEnd_3636602 : Nat := 1244883183401257341100385

theorem tailTrace_3636602 : CollatzResearch.WordTrace tailWord_3636602 prefixEnd_3636602 1244883183401257341100385 := by
  unfold tailWord_3636602
  simp only [CollatzResearch.WordTrace]
  refine ⟨33159442892804877754958015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88425181047479674013221373 33159442892804877754958015)
  ·
    refine ⟨49739164339207316632437023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33159442892804877754958015 49739164339207316632437023)
    ·
      refine ⟨74608746508810974948655535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49739164339207316632437023 74608746508810974948655535)
      ·
        refine ⟨111913119763216462422983303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74608746508810974948655535 111913119763216462422983303)
        ·
          refine ⟨167869679644824693634474955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111913119763216462422983303 167869679644824693634474955)
          ·
            refine ⟨251804519467237040451712433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167869679644824693634474955 251804519467237040451712433)
            ·
              refine ⟨188853389600427780338784325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251804519467237040451712433 188853389600427780338784325)
              ·
                refine ⟨35410010550080208813522061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188853389600427780338784325 35410010550080208813522061)
                ·
                  refine ⟨13278753956280078305070773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35410010550080208813522061 13278753956280078305070773)
                  ·
                    refine ⟨1244883183401257341100385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13278753956280078305070773 1244883183401257341100385)
                    ·
                      rfl

theorem cell22_3636602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_3636602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3636602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3636602 prefixEnd_3636602 := by exact prefixLift 3636602
  have htrace : WordTrace (prefixWord ++ tailWord_3636602) baseStart_3636602 baseEnd_3636602 := by
    simpa [prefixWord, tailWord_3636602, baseEnd_3636602] using wordTrace_append hprefix tailTrace_3636602
  have hstable : (prefixWord ++ tailWord_3636602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636602).length < 2 ^ (prefixWord ++ tailWord_3636602).sum := by decide
  have hdescent : baseEnd_3636602 < baseStart_3636602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636610 : List Nat := [3, 4, 2, 1, 1, 3, 2, 1, 5]
def baseStart_3636610 : Nat := 118140960795 + 3636610 * 2 ^ 59
def prefixEnd_3636610 : Nat := 4983230072969 + 3 ^ 40 * 3636610 * 2
def baseEnd_3636610 : Nat := 414961973988249328966787

theorem tailTrace_3636610 : CollatzResearch.WordTrace tailWord_3636610 prefixEnd_3636610 414961973988249328966787 := by
  unfold tailWord_3636610
  simp only [CollatzResearch.WordTrace]
  refine ⟨33159515838797632096530821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88425375570127018924082189 33159515838797632096530821)
  ·
    refine ⟨6217409219774556018099529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33159515838797632096530821 6217409219774556018099529)
    ·
      refine ⟨4663056914830917013574647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6217409219774556018099529 4663056914830917013574647)
      ·
        refine ⟨6994585372246375520361971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4663056914830917013574647 6994585372246375520361971)
        ·
          refine ⟨10491878058369563280542957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6994585372246375520361971 10491878058369563280542957)
          ·
            refine ⟨3934454271888586230203609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10491878058369563280542957 3934454271888586230203609)
            ·
              refine ⟨2950840703916439672652707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3934454271888586230203609 2950840703916439672652707)
              ·
                refine ⟨4426261055874659508979061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2950840703916439672652707 4426261055874659508979061)
                ·
                  refine ⟨414961973988249328966787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4426261055874659508979061 414961973988249328966787)
                  ·
                    rfl

theorem cell22_3636610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_3636610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3636610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3636610 prefixEnd_3636610 := by exact prefixLift 3636610
  have htrace : WordTrace (prefixWord ++ tailWord_3636610) baseStart_3636610 baseEnd_3636610 := by
    simpa [prefixWord, tailWord_3636610, baseEnd_3636610] using wordTrace_append hprefix tailTrace_3636610
  have hstable : (prefixWord ++ tailWord_3636610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636610).length < 2 ^ (prefixWord ++ tailWord_3636610).sum := by decide
  have hdescent : baseEnd_3636610 < baseStart_3636610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636653 : List Nat := [1, 5, 2, 2, 1, 1, 1, 4, 2, 3]
def baseStart_3636653 : Nat := 118140960795 + 3636653 * 2 ^ 59
def prefixEnd_3636653 : Nat := 4983230072969 + 3 ^ 40 * 3636653 * 2
def baseEnd_3636653 : Nat := 1244900641743510208075229

theorem tailTrace_3636653 : CollatzResearch.WordTrace tailWord_3636653 prefixEnd_3636653 1244900641743510208075229 := by
  unfold tailWord_3636653
  simp only [CollatzResearch.WordTrace]
  refine ⟨132639631694034746729938613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88426421129356497819959075 132639631694034746729938613)
  ·
    refine ⟨12434965471315757505931745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132639631694034746729938613 12434965471315757505931745)
    ·
      refine ⟨9326224103486818129448809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12434965471315757505931745 9326224103486818129448809)
      ·
        refine ⟨6994668077615113597086607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9326224103486818129448809 6994668077615113597086607)
        ·
          refine ⟨10492002116422670395629911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6994668077615113597086607 10492002116422670395629911)
          ·
            refine ⟨15738003174634005593444867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10492002116422670395629911 15738003174634005593444867)
            ·
              refine ⟨23607004761951008390167301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15738003174634005593444867 23607004761951008390167301)
              ·
                refine ⟨4426313392865814073156369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23607004761951008390167301 4426313392865814073156369)
                ·
                  refine ⟨3319735044649360554867277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4426313392865814073156369 3319735044649360554867277)
                  ·
                    refine ⟨1244900641743510208075229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3319735044649360554867277 1244900641743510208075229)
                    ·
                      rfl

theorem cell22_3636653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_3636653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3636653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3636653 prefixEnd_3636653 := by exact prefixLift 3636653
  have htrace : WordTrace (prefixWord ++ tailWord_3636653) baseStart_3636653 baseEnd_3636653 := by
    simpa [prefixWord, tailWord_3636653, baseEnd_3636653] using wordTrace_append hprefix tailTrace_3636653
  have hstable : (prefixWord ++ tailWord_3636653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636653).length < 2 ^ (prefixWord ++ tailWord_3636653).sum := by decide
  have hdescent : baseEnd_3636653 < baseStart_3636653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636698 : List Nat := [3, 1, 1, 2, 3, 2, 1, 5, 1, 3]
def baseStart_3636698 : Nat := 118140960795 + 3636698 * 2 ^ 59
def prefixEnd_3636698 : Nat := 4983230072969 + 3 ^ 40 * 3636698 * 2
def baseEnd_3636698 : Nat := 1244916046163145090700091

theorem tailTrace_3636698 : CollatzResearch.WordTrace tailWord_3636698 prefixEnd_3636698 1244916046163145090700091 := by
  unfold tailWord_3636698
  simp only [CollatzResearch.WordTrace]
  refine ⟨33160318244717929853831687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88427515319247812943551165 33160318244717929853831687)
  ·
    refine ⟨49740477367076894780747531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33160318244717929853831687 49740477367076894780747531)
    ·
      refine ⟨74610716050615342171121297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49740477367076894780747531 74610716050615342171121297)
      ·
        refine ⟨55958037037961506628340973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74610716050615342171121297 55958037037961506628340973)
        ·
          refine ⟨20984263889235564985627865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55958037037961506628340973 20984263889235564985627865)
          ·
            refine ⟨15738197916926673739220899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20984263889235564985627865 15738197916926673739220899)
            ·
              refine ⟨23607296875390010608831349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15738197916926673739220899 23607296875390010608831349)
              ·
                refine ⟨2213184082067813494577939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23607296875390010608831349 2213184082067813494577939)
                ·
                  refine ⟨3319776123101720241866909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2213184082067813494577939 3319776123101720241866909)
                  ·
                    refine ⟨1244916046163145090700091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3319776123101720241866909 1244916046163145090700091)
                    ·
                      rfl

theorem cell22_3636698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5, 1, 3].length) (baseStart_3636698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3636698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3636698 prefixEnd_3636698 := by exact prefixLift 3636698
  have htrace : WordTrace (prefixWord ++ tailWord_3636698) baseStart_3636698 baseEnd_3636698 := by
    simpa [prefixWord, tailWord_3636698, baseEnd_3636698] using wordTrace_append hprefix tailTrace_3636698
  have hstable : (prefixWord ++ tailWord_3636698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636698).length < 2 ^ (prefixWord ++ tailWord_3636698).sum := by decide
  have hdescent : baseEnd_3636698 < baseStart_3636698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636711 : List Nat := [1, 1, 5, 2, 1, 2, 3, 2, 5]
def baseStart_3636711 : Nat := 118140960795 + 3636711 * 2 ^ 59
def prefixEnd_3636711 : Nat := 4983230072969 + 3 ^ 40 * 3636711 * 2
def baseEnd_3636711 : Nat := 414973498776272463375017

theorem tailTrace_3636711 : CollatzResearch.WordTrace tailWord_3636711 prefixEnd_3636711 414973498776272463375017 := by
  unfold tailWord_3636711
  simp only [CollatzResearch.WordTrace]
  refine ⟨132641747127824622635549987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88427831418549748423699991 132641747127824622635549987)
  ·
    refine ⟨198962620691736933953324981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132641747127824622635549987 198962620691736933953324981)
    ·
      refine ⟨18652745689850337558124217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198962620691736933953324981 18652745689850337558124217)
      ·
        refine ⟨13989559267387753168593163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18652745689850337558124217 13989559267387753168593163)
        ·
          refine ⟨20984338901081629752889745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13989559267387753168593163 20984338901081629752889745)
          ·
            refine ⟨15738254175811222314667309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20984338901081629752889745 15738254175811222314667309)
            ·
              refine ⟨5901845315929208368000241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15738254175811222314667309 5901845315929208368000241)
              ·
                refine ⟨4426383986946906276000181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5901845315929208368000241 4426383986946906276000181)
                ·
                  refine ⟨414973498776272463375017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4426383986946906276000181 414973498776272463375017)
                  ·
                    rfl

theorem cell22_3636711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 5].length) (baseStart_3636711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3636711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3636711 prefixEnd_3636711 := by exact prefixLift 3636711
  have htrace : WordTrace (prefixWord ++ tailWord_3636711) baseStart_3636711 baseEnd_3636711 := by
    simpa [prefixWord, tailWord_3636711, baseEnd_3636711] using wordTrace_append hprefix tailTrace_3636711
  have hstable : (prefixWord ++ tailWord_3636711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636711).length < 2 ^ (prefixWord ++ tailWord_3636711).sum := by decide
  have hdescent : baseEnd_3636711 < baseStart_3636711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636726 : List Nat := [5, 1, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_3636726 : Nat := 118140960795 + 3636726 * 2 ^ 59
def prefixEnd_3636726 : Nat := 4983230072969 + 3 ^ 40 * 3636726 * 2
def baseEnd_3636726 : Nat := 1244925631135362351000005

theorem tailTrace_3636726 : CollatzResearch.WordTrace tailWord_3636726 prefixEnd_3636726 1244925631135362351000005 := by
  unfold tailWord_3636726
  simp only [CollatzResearch.WordTrace]
  refine ⟨8290143388923142512334127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88428196148513520131564021 8290143388923142512334127)
  ·
    refine ⟨12435215083384713768501191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8290143388923142512334127 12435215083384713768501191)
    ·
      refine ⟨18652822625077070652751787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12435215083384713768501191 18652822625077070652751787)
      ·
        refine ⟨27979233937615605979127681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18652822625077070652751787 27979233937615605979127681)
        ·
          refine ⟨20984425453211704484345761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27979233937615605979127681 20984425453211704484345761)
          ·
            refine ⟨15738319089908778363259321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20984425453211704484345761 15738319089908778363259321)
            ·
              refine ⟨11803739317431583772444491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15738319089908778363259321 11803739317431583772444491)
              ·
                refine ⟨17705608976147375658666737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11803739317431583772444491 17705608976147375658666737)
                ·
                  refine ⟨13279206732110531744000053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17705608976147375658666737 13279206732110531744000053)
                  ·
                    refine ⟨1244925631135362351000005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13279206732110531744000053 1244925631135362351000005)
                    ·
                      rfl

theorem cell22_3636726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_3636726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3636726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3636726 prefixEnd_3636726 := by exact prefixLift 3636726
  have htrace : WordTrace (prefixWord ++ tailWord_3636726) baseStart_3636726 baseEnd_3636726 := by
    simpa [prefixWord, tailWord_3636726, baseEnd_3636726] using wordTrace_append hprefix tailTrace_3636726
  have hstable : (prefixWord ++ tailWord_3636726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636726).length < 2 ^ (prefixWord ++ tailWord_3636726).sum := by decide
  have hdescent : baseEnd_3636726 < baseStart_3636726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636766 : List Nat := [4, 3, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_3636766 : Nat := 118140960795 + 3636766 * 2 ^ 59
def prefixEnd_3636766 : Nat := 4983230072969 + 3 ^ 40 * 3636766 * 2
def baseEnd_3636766 : Nat := 1244939323952815579999883

theorem tailTrace_3636766 : CollatzResearch.WordTrace tailWord_3636766 prefixEnd_3636766 1244939323952815579999883 := by
  unfold tailWord_3636766
  simp only [CollatzResearch.WordTrace]
  refine ⟨16580469142828170878600269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88429168761750244685868101 16580469142828170878600269)
  ·
    refine ⟨6217675928560564079475101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16580469142828170878600269 6217675928560564079475101)
    ·
      refine ⟨2331628473210211529803163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6217675928560564079475101 2331628473210211529803163)
      ·
        refine ⟨3497442709815317294704745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2331628473210211529803163 3497442709815317294704745)
        ·
          refine ⟨2623082032361487971028559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3497442709815317294704745 2623082032361487971028559)
          ·
            refine ⟨3934623048542231956542839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2623082032361487971028559 3934623048542231956542839)
            ·
              refine ⟨5901934572813347934814259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3934623048542231956542839 5901934572813347934814259)
              ·
                refine ⟨8852901859220021902221389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5901934572813347934814259 8852901859220021902221389)
                ·
                  refine ⟨3319838197207508213333021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8852901859220021902221389 3319838197207508213333021)
                  ·
                    refine ⟨1244939323952815579999883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3319838197207508213333021 1244939323952815579999883)
                    ·
                      rfl

theorem cell22_3636766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_3636766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3636766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3636766 prefixEnd_3636766 := by exact prefixLift 3636766
  have htrace : WordTrace (prefixWord ++ tailWord_3636766) baseStart_3636766 baseEnd_3636766 := by
    simpa [prefixWord, tailWord_3636766, baseEnd_3636766] using wordTrace_append hprefix tailTrace_3636766
  have hstable : (prefixWord ++ tailWord_3636766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636766).length < 2 ^ (prefixWord ++ tailWord_3636766).sum := by decide
  have hdescent : baseEnd_3636766 < baseStart_3636766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636921 : List Nat := [1, 2, 1, 4, 1, 1, 4, 1, 1, 6]
def baseStart_3636921 : Nat := 118140960795 + 3636921 * 2 ^ 59
def prefixEnd_3636921 : Nat := 4983230072969 + 3 ^ 40 * 3636921 * 2
def baseEnd_3636921 : Nat := 1244992383620446842374407

theorem tailTrace_3636921 : CollatzResearch.WordTrace tailWord_3636921 prefixEnd_3636921 1244992383620446842374407 := by
  unfold tailWord_3636921
  simp only [CollatzResearch.WordTrace]
  refine ⟨132649406457063828500694617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88432937638042552333796411 132649406457063828500694617)
  ·
    refine ⟨99487054842797871375520963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132649406457063828500694617 99487054842797871375520963)
    ·
      refine ⟨149230582264196807063281445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99487054842797871375520963 149230582264196807063281445)
      ·
        refine ⟨27980734174536901324365271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149230582264196807063281445 27980734174536901324365271)
        ·
          refine ⟨41971101261805351986547907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27980734174536901324365271 41971101261805351986547907)
          ·
            refine ⟨62956651892708027979821861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41971101261805351986547907 62956651892708027979821861)
            ·
              refine ⟨11804372229882755246216599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62956651892708027979821861 11804372229882755246216599)
              ·
                refine ⟨17706558344824132869324899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11804372229882755246216599 17706558344824132869324899)
                ·
                  refine ⟨26559837517236199303987349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17706558344824132869324899 26559837517236199303987349)
                  ·
                    refine ⟨1244992383620446842374407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26559837517236199303987349 1244992383620446842374407)
                    ·
                      rfl

theorem cell22_3636921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 6].length) (baseStart_3636921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3636921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3636921 prefixEnd_3636921 := by exact prefixLift 3636921
  have htrace : WordTrace (prefixWord ++ tailWord_3636921) baseStart_3636921 baseEnd_3636921 := by
    simpa [prefixWord, tailWord_3636921, baseEnd_3636921] using wordTrace_append hprefix tailTrace_3636921
  have hstable : (prefixWord ++ tailWord_3636921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636921).length < 2 ^ (prefixWord ++ tailWord_3636921).sum := by decide
  have hdescent : baseEnd_3636921 < baseStart_3636921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637002 : List Nat := [3, 1, 2, 2, 1, 4, 1, 4, 1, 3]
def baseStart_3637002 : Nat := 118140960795 + 3637002 * 2 ^ 59
def prefixEnd_3637002 : Nat := 4983230072969 + 3 ^ 40 * 3637002 * 2
def baseEnd_3637002 : Nat := 1245020111575789631099159

theorem tailTrace_3637002 : CollatzResearch.WordTrace tailWord_3637002 prefixEnd_3637002 1245020111575789631099159 := by
  unfold tailWord_3637002
  simp only [CollatzResearch.WordTrace]
  refine ⟨33163090192442594833598315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88434907179846919556262173 33163090192442594833598315)
  ·
    refine ⟨49744635288663892250397473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33163090192442594833598315 49744635288663892250397473)
    ·
      refine ⟨37308476466497919187798105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49744635288663892250397473 37308476466497919187798105)
      ·
        refine ⟨27981357349873439390848579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37308476466497919187798105 27981357349873439390848579)
        ·
          refine ⟨41972036024810159086272869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27981357349873439390848579 41972036024810159086272869)
          ·
            refine ⟨7869756754651904828676163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41972036024810159086272869 7869756754651904828676163)
            ·
              refine ⟨11804635131977857243014245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7869756754651904828676163 11804635131977857243014245)
              ·
                refine ⟨2213369087245848233065171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11804635131977857243014245 2213369087245848233065171)
                ·
                  refine ⟨3320053630868772349597757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2213369087245848233065171 3320053630868772349597757)
                  ·
                    refine ⟨1245020111575789631099159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3320053630868772349597757 1245020111575789631099159)
                    ·
                      rfl

theorem cell22_3637002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_3637002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637002 prefixEnd_3637002 := by exact prefixLift 3637002
  have htrace : WordTrace (prefixWord ++ tailWord_3637002) baseStart_3637002 baseEnd_3637002 := by
    simpa [prefixWord, tailWord_3637002, baseEnd_3637002] using wordTrace_append hprefix tailTrace_3637002
  have hstable : (prefixWord ++ tailWord_3637002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637002).length < 2 ^ (prefixWord ++ tailWord_3637002).sum := by decide
  have hdescent : baseEnd_3637002 < baseStart_3637002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637013 : List Nat := [1, 3, 2, 1, 2, 4, 1, 1, 2, 5]
def baseStart_3637013 : Nat := 118140960795 + 3637013 * 2 ^ 59
def prefixEnd_3637013 : Nat := 4983230072969 + 3 ^ 40 * 3637013 * 2
def baseEnd_3637013 : Nat := 1245023877100589269074125

theorem tailTrace_3637013 : CollatzResearch.WordTrace tailWord_3637013 prefixEnd_3637013 1245023877100589269074125 := by
  unfold tailWord_3637013
  simp only [CollatzResearch.WordTrace]
  refine ⟨132652761972730528213043693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88435174648487018808695795 132652761972730528213043693)
  ·
    refine ⟨49744785739773948079891385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132652761972730528213043693 49744785739773948079891385)
    ·
      refine ⟨37308589304830461059918539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49744785739773948079891385 37308589304830461059918539)
      ·
        refine ⟨55962883957245691589877809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37308589304830461059918539 55962883957245691589877809)
        ·
          refine ⟨41972162967934268692408357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55962883957245691589877809 41972162967934268692408357)
          ·
            refine ⟨7869780556487675379826567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41972162967934268692408357 7869780556487675379826567)
            ·
              refine ⟨11804670834731513069739851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7869780556487675379826567 11804670834731513069739851)
              ·
                refine ⟨17707006252097269604609777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11804670834731513069739851 17707006252097269604609777)
                ·
                  refine ⟨13280254689072952203457333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17707006252097269604609777 13280254689072952203457333)
                  ·
                    refine ⟨1245023877100589269074125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13280254689072952203457333 1245023877100589269074125)
                    ·
                      rfl

theorem cell22_3637013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_3637013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637013 prefixEnd_3637013 := by exact prefixLift 3637013
  have htrace : WordTrace (prefixWord ++ tailWord_3637013) baseStart_3637013 baseEnd_3637013 := by
    simpa [prefixWord, tailWord_3637013, baseEnd_3637013] using wordTrace_append hprefix tailTrace_3637013
  have hstable : (prefixWord ++ tailWord_3637013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637013).length < 2 ^ (prefixWord ++ tailWord_3637013).sum := by decide
  have hdescent : baseEnd_3637013 < baseStart_3637013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637049 : List Nat := [1, 2, 1, 7, 2, 1, 1, 2, 5]
def baseStart_3637049 : Nat := 118140960795 + 3637049 * 2 ^ 59
def prefixEnd_3637049 : Nat := 4983230072969 + 3 ^ 40 * 3637049 * 2
def baseEnd_3637049 : Nat := 415012066878765725058005

theorem tailTrace_3637049 : CollatzResearch.WordTrace tailWord_3637049 prefixEnd_3637049 415012066878765725058005 := by
  unfold tailWord_3637049
  simp only [CollatzResearch.WordTrace]
  refine ⟨132654075000600106361354201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88436050000400070907569467 132654075000600106361354201)
  ·
    refine ⟨99490556250450079771015651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132654075000600106361354201 99490556250450079771015651)
    ·
      refine ⟨149235834375675119656523477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99490556250450079771015651 149235834375675119656523477)
      ·
        refine ⟨3497714868179885616949769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 149235834375675119656523477 3497714868179885616949769)
        ·
          refine ⟨2623286151134914212712327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3497714868179885616949769 2623286151134914212712327)
          ·
            refine ⟨3934929226702371319068491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2623286151134914212712327 3934929226702371319068491)
            ·
              refine ⟨5902393840053556978602737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3934929226702371319068491 5902393840053556978602737)
              ·
                refine ⟨4426795380040167733952053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5902393840053556978602737 4426795380040167733952053)
                ·
                  refine ⟨415012066878765725058005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4426795380040167733952053 415012066878765725058005)
                  ·
                    rfl

theorem cell22_3637049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 5].length) (baseStart_3637049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637049 prefixEnd_3637049 := by exact prefixLift 3637049
  have htrace : WordTrace (prefixWord ++ tailWord_3637049) baseStart_3637049 baseEnd_3637049 := by
    simpa [prefixWord, tailWord_3637049, baseEnd_3637049] using wordTrace_append hprefix tailTrace_3637049
  have hstable : (prefixWord ++ tailWord_3637049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637049).length < 2 ^ (prefixWord ++ tailWord_3637049).sum := by decide
  have hdescent : baseEnd_3637049 < baseStart_3637049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637073 : List Nat := [1, 2, 2, 1, 5, 1, 1, 2, 1, 6]
def baseStart_3637073 : Nat := 118140960795 + 3637073 * 2 ^ 59
def prefixEnd_3637073 : Nat := 4983230072969 + 3 ^ 40 * 3637073 * 2
def baseEnd_3637073 : Nat := 1245044416326769112573941

theorem tailTrace_3637073 : CollatzResearch.WordTrace tailWord_3637073 prefixEnd_3637073 1245044416326769112573941 := by
  unfold tailWord_3637073
  simp only [CollatzResearch.WordTrace]
  refine ⟨132654950352513158460227873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88436633568342105640151915 132654950352513158460227873)
  ·
    refine ⟨99491212764384868845170905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132654950352513158460227873 99491212764384868845170905)
    ·
      refine ⟨74618409573288651633878179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99491212764384868845170905 74618409573288651633878179)
      ·
        refine ⟨111927614359932977450817269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74618409573288651633878179 111927614359932977450817269)
        ·
          refine ⟨10493213846243716636014119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111927614359932977450817269 10493213846243716636014119)
          ·
            refine ⟨15739820769365574954021179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10493213846243716636014119 15739820769365574954021179)
            ·
              refine ⟨23609731154048362431031769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15739820769365574954021179 23609731154048362431031769)
              ·
                refine ⟨17707298365536271823273827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23609731154048362431031769 17707298365536271823273827)
                ·
                  refine ⟨26560947548304407734910741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17707298365536271823273827 26560947548304407734910741)
                  ·
                    refine ⟨1245044416326769112573941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26560947548304407734910741 1245044416326769112573941)
                    ·
                      rfl

theorem cell22_3637073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_3637073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637073 prefixEnd_3637073 := by exact prefixLift 3637073
  have htrace : WordTrace (prefixWord ++ tailWord_3637073) baseStart_3637073 baseEnd_3637073 := by
    simpa [prefixWord, tailWord_3637073, baseEnd_3637073] using wordTrace_append hprefix tailTrace_3637073
  have hstable : (prefixWord ++ tailWord_3637073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637073).length < 2 ^ (prefixWord ++ tailWord_3637073).sum := by decide
  have hdescent : baseEnd_3637073 < baseStart_3637073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637088 : List Nat := [2, 1, 1, 3, 3, 3, 1, 8]
def baseStart_3637088 : Nat := 118140960795 + 3637088 * 2 ^ 59
def prefixEnd_3637088 : Nat := 4983230072969 + 3 ^ 40 * 3637088 * 2
def baseEnd_3637088 : Nat := 138338839014812674827655

theorem tailTrace_3637088 : CollatzResearch.WordTrace tailWord_3637088 prefixEnd_3637088 138338839014812674827655 := by
  unfold tailWord_3637088
  simp only [CollatzResearch.WordTrace]
  refine ⟨66327748723729408011011959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88436998298305877348015945 66327748723729408011011959)
  ·
    refine ⟨99491623085594112016517939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66327748723729408011011959 99491623085594112016517939)
    ·
      refine ⟨149237434628391168024776909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99491623085594112016517939 149237434628391168024776909)
      ·
        refine ⟨55964037985646688009291341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149237434628391168024776909 55964037985646688009291341)
        ·
          refine ⟨20986514244617508003484253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55964037985646688009291341 20986514244617508003484253)
          ·
            refine ⟨7869942841731565501306595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20986514244617508003484253 7869942841731565501306595)
            ·
              refine ⟨11804914262597348251959893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7869942841731565501306595 11804914262597348251959893)
              ·
                refine ⟨138338839014812674827655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11804914262597348251959893 138338839014812674827655)
                ·
                  rfl

theorem cell22_3637088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 8].length) (baseStart_3637088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637088 prefixEnd_3637088 := by exact prefixLift 3637088
  have htrace : WordTrace (prefixWord ++ tailWord_3637088) baseStart_3637088 baseEnd_3637088 := by
    simpa [prefixWord, tailWord_3637088, baseEnd_3637088] using wordTrace_append hprefix tailTrace_3637088
  have hstable : (prefixWord ++ tailWord_3637088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637088).length < 2 ^ (prefixWord ++ tailWord_3637088).sum := by decide
  have hdescent : baseEnd_3637088 < baseStart_3637088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637090 : List Nat := [3, 3, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_3637090 : Nat := 118140960795 + 3637090 * 2 ^ 59
def prefixEnd_3637090 : Nat := 4983230072969 + 3 ^ 40 * 3637090 * 2
def baseEnd_3637090 : Nat := 1245050235774186734898889

theorem tailTrace_3637090 : CollatzResearch.WordTrace tailWord_3637090 prefixEnd_3637090 1245050235774186734898889 := by
  unfold tailWord_3637090
  simp only [CollatzResearch.WordTrace]
  refine ⟨33163892598362892590899181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88437046928967713575731149 33163892598362892590899181)
  ·
    refine ⟨12436459724386084721587193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33163892598362892590899181 12436459724386084721587193)
    ·
      refine ⟨9327344793289563541190395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12436459724386084721587193 9327344793289563541190395)
      ·
        refine ⟨13991017189934345311785593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9327344793289563541190395 13991017189934345311785593)
        ·
          refine ⟨10493262892450758983839195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13991017189934345311785593 10493262892450758983839195)
          ·
            refine ⟨15739894338676138475758793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10493262892450758983839195 15739894338676138475758793)
            ·
              refine ⟨11804920754007103856819095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15739894338676138475758793 11804920754007103856819095)
              ·
                refine ⟨17707381131010655785228643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11804920754007103856819095 17707381131010655785228643)
                ·
                  refine ⟨26561071696515983677842965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17707381131010655785228643 26561071696515983677842965)
                  ·
                    refine ⟨1245050235774186734898889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26561071696515983677842965 1245050235774186734898889)
                    ·
                      rfl

theorem cell22_3637090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_3637090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637090 prefixEnd_3637090 := by exact prefixLift 3637090
  have htrace : WordTrace (prefixWord ++ tailWord_3637090) baseStart_3637090 baseEnd_3637090 := by
    simpa [prefixWord, tailWord_3637090, baseEnd_3637090] using wordTrace_append hprefix tailTrace_3637090
  have hstable : (prefixWord ++ tailWord_3637090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637090).length < 2 ^ (prefixWord ++ tailWord_3637090).sum := by decide
  have hdescent : baseEnd_3637090 < baseStart_3637090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637163 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 7, 4]
def baseStart_3637163 : Nat := 118140960795 + 3637163 * 2 ^ 59
def prefixEnd_3637163 : Nat := 4983230072969 + 3 ^ 40 * 3637163 * 2
def baseEnd_3637163 : Nat := 1245075225166038877823665

theorem tailTrace_3637163 : CollatzResearch.WordTrace tailWord_3637163 prefixEnd_3637163 1245075225166038877823665 := by
  unfold tailWord_3637163
  simp only [CollatzResearch.WordTrace]
  refine ⟨132658232922187103831004143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88438821948124735887336095 132658232922187103831004143)
  ·
    refine ⟨198987349383280655746506215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132658232922187103831004143 198987349383280655746506215)
    ·
      refine ⟨298481024074920983619759323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198987349383280655746506215 298481024074920983619759323)
      ·
        refine ⟨447721536112381475429638985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298481024074920983619759323 447721536112381475429638985)
        ·
          refine ⟨335791152084286106572229239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447721536112381475429638985 335791152084286106572229239)
          ·
            refine ⟨503686728126429159858343859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335791152084286106572229239 503686728126429159858343859)
            ·
              refine ⟨755530092189643739787515789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503686728126429159858343859 755530092189643739787515789)
              ·
                refine ⟨283323784571116402420318421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 755530092189643739787515789 283323784571116402420318421)
                ·
                  refine ⟨6640401200885540681726213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 283323784571116402420318421 6640401200885540681726213)
                  ·
                    refine ⟨1245075225166038877823665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6640401200885540681726213 1245075225166038877823665)
                    ·
                      rfl

theorem cell22_3637163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 4].length) (baseStart_3637163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637163 prefixEnd_3637163 := by exact prefixLift 3637163
  have htrace : WordTrace (prefixWord ++ tailWord_3637163) baseStart_3637163 baseEnd_3637163 := by
    simpa [prefixWord, tailWord_3637163, baseEnd_3637163] using wordTrace_append hprefix tailTrace_3637163
  have hstable : (prefixWord ++ tailWord_3637163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637163).length < 2 ^ (prefixWord ++ tailWord_3637163).sum := by decide
  have hdescent : baseEnd_3637163 < baseStart_3637163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637193 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 5, 5]
def baseStart_3637193 : Nat := 118140960795 + 3637193 * 2 ^ 59
def prefixEnd_3637193 : Nat := 4983230072969 + 3 ^ 40 * 3637193 * 2
def baseEnd_3637193 : Nat := 1245085494779128799573573

theorem tailTrace_3637193 : CollatzResearch.WordTrace tailWord_3637193 prefixEnd_3637193 1245085494779128799573573 := by
  unfold tailWord_3637193
  simp only [CollatzResearch.WordTrace]
  refine ⟨132659327112078418954596233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88439551408052279303064155 132659327112078418954596233)
  ·
    refine ⟨99494495334058814215947175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132659327112078418954596233 99494495334058814215947175)
    ·
      refine ⟨149241743001088221323920763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99494495334058814215947175 149241743001088221323920763)
      ·
        refine ⟨223862614501632331985881145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149241743001088221323920763 223862614501632331985881145)
        ·
          refine ⟨167896960876224248989410859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223862614501632331985881145 167896960876224248989410859)
          ·
            refine ⟨251845441314336373484116289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167896960876224248989410859 251845441314336373484116289)
            ·
              refine ⟨188884080985752280113087217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251845441314336373484116289 188884080985752280113087217)
              ·
                refine ⟨141663060739314210084815413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188884080985752280113087217 141663060739314210084815413)
                ·
                  refine ⟨13280911944310707195451445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141663060739314210084815413 13280911944310707195451445)
                  ·
                    refine ⟨1245085494779128799573573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13280911944310707195451445 1245085494779128799573573)
                    ·
                      rfl

theorem cell22_3637193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 5].length) (baseStart_3637193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637193 prefixEnd_3637193 := by exact prefixLift 3637193
  have htrace : WordTrace (prefixWord ++ tailWord_3637193) baseStart_3637193 baseEnd_3637193 := by
    simpa [prefixWord, tailWord_3637193, baseEnd_3637193] using wordTrace_append hprefix tailTrace_3637193
  have hstable : (prefixWord ++ tailWord_3637193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637193).length < 2 ^ (prefixWord ++ tailWord_3637193).sum := by decide
  have hdescent : baseEnd_3637193 < baseStart_3637193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637229 : List Nat := [1, 5, 1, 4, 1, 1, 2, 1, 6]
def baseStart_3637229 : Nat := 118140960795 + 3637229 * 2 ^ 59
def prefixEnd_3637229 : Nat := 4983230072969 + 3 ^ 40 * 3637229 * 2
def baseEnd_3637229 : Nat := 415032606104945568557821

theorem tailTrace_3637229 : CollatzResearch.WordTrace tailWord_3637229 prefixEnd_3637229 415032606104945568557821 := by
  unfold tailWord_3637229
  simp only [CollatzResearch.WordTrace]
  refine ⟨132660640139947997102906741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88440426759965331401937827 132660640139947997102906741)
  ·
    refine ⟨12436935013120124728397507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132660640139947997102906741 12436935013120124728397507)
    ·
      refine ⟨18655402519680187092596261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12436935013120124728397507 18655402519680187092596261)
      ·
        refine ⟨3497887972440035079861799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18655402519680187092596261 3497887972440035079861799)
        ·
          refine ⟨5246831958660052619792699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3497887972440035079861799 5246831958660052619792699)
          ·
            refine ⟨7870247937990078929689049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5246831958660052619792699 7870247937990078929689049)
            ·
              refine ⟨5902685953492559197266787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7870247937990078929689049 5902685953492559197266787)
              ·
                refine ⟨8854028930238838795900181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5902685953492559197266787 8854028930238838795900181)
                ·
                  refine ⟨415032606104945568557821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8854028930238838795900181 415032606104945568557821)
                  ·
                    rfl

theorem cell22_3637229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_3637229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637229 prefixEnd_3637229 := by exact prefixLift 3637229
  have htrace : WordTrace (prefixWord ++ tailWord_3637229) baseStart_3637229 baseEnd_3637229 := by
    simpa [prefixWord, tailWord_3637229, baseEnd_3637229] using wordTrace_append hprefix tailTrace_3637229
  have hstable : (prefixWord ++ tailWord_3637229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637229).length < 2 ^ (prefixWord ++ tailWord_3637229).sum := by decide
  have hdescent : baseEnd_3637229 < baseStart_3637229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637244 : List Nat := [2, 2, 2, 1, 2, 2, 5, 1, 2, 3]
def baseStart_3637244 : Nat := 118140960795 + 3637244 * 2 ^ 59
def prefixEnd_3637244 : Nat := 4983230072969 + 3 ^ 40 * 3637244 * 2
def baseEnd_3637244 : Nat := 1245102953121381666548417

theorem tailTrace_3637244 : CollatzResearch.WordTrace tailWord_3637244 prefixEnd_3637244 1245102953121381666548417 := by
  unfold tailWord_3637244
  simp only [CollatzResearch.WordTrace]
  refine ⟨66330593617446827332351393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88440791489929103109801857 66330593617446827332351393)
  ·
    refine ⟨49747945213085120499263545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66330593617446827332351393 49747945213085120499263545)
    ·
      refine ⟨37310958909813840374447659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49747945213085120499263545 37310958909813840374447659)
      ·
        refine ⟨55966438364720760561671489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37310958909813840374447659 55966438364720760561671489)
        ·
          refine ⟨41974828773540570421253617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55966438364720760561671489 41974828773540570421253617)
          ·
            refine ⟨31481121580155427815940213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41974828773540570421253617 31481121580155427815940213)
            ·
              refine ⟨2951355148139571357744395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31481121580155427815940213 2951355148139571357744395)
              ·
                refine ⟨4427032722209357036616593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2951355148139571357744395 4427032722209357036616593)
                ·
                  refine ⟨3320274541657017777462445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4427032722209357036616593 3320274541657017777462445)
                  ·
                    refine ⟨1245102953121381666548417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3320274541657017777462445 1245102953121381666548417)
                    ·
                      rfl

theorem cell22_3637244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_3637244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637244 prefixEnd_3637244 := by exact prefixLift 3637244
  have htrace : WordTrace (prefixWord ++ tailWord_3637244) baseStart_3637244 baseEnd_3637244 := by
    simpa [prefixWord, tailWord_3637244, baseEnd_3637244] using wordTrace_append hprefix tailTrace_3637244
  have hstable : (prefixWord ++ tailWord_3637244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637244).length < 2 ^ (prefixWord ++ tailWord_3637244).sum := by decide
  have hdescent : baseEnd_3637244 < baseStart_3637244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637285 : List Nat := [1, 3, 1, 2, 2, 3, 2, 1, 7]
def baseStart_3637285 : Nat := 118140960795 + 3637285 * 2 ^ 59
def prefixEnd_3637285 : Nat := 4983230072969 + 3 ^ 40 * 3637285 * 2
def baseEnd_3637285 : Nat := 415038996086423742091097

theorem tailTrace_3637285 : CollatzResearch.WordTrace tailWord_3637285 prefixEnd_3637285 415038996086423742091097 := by
  unfold tailWord_3637285
  simp only [CollatzResearch.WordTrace]
  refine ⟨132662682627745118666945309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88441788418496745777963539 132662682627745118666945309)
  ·
    refine ⟨49748505985404419500104491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132662682627745118666945309 49748505985404419500104491)
    ·
      refine ⟨74622758978106629250156737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49748505985404419500104491 74622758978106629250156737)
      ·
        refine ⟨55967069233579971937617553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74622758978106629250156737 55967069233579971937617553)
        ·
          refine ⟨41975301925184978953213165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55967069233579971937617553 41975301925184978953213165)
          ·
            refine ⟨15740738221944367107454937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41975301925184978953213165 15740738221944367107454937)
            ·
              refine ⟨11805553666458275330591203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15740738221944367107454937 11805553666458275330591203)
              ·
                refine ⟨17708330499687412995886805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11805553666458275330591203 17708330499687412995886805)
                ·
                  refine ⟨415038996086423742091097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17708330499687412995886805 415038996086423742091097)
                  ·
                    rfl

theorem cell22_3637285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 7].length) (baseStart_3637285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637285 prefixEnd_3637285 := by exact prefixLift 3637285
  have htrace : WordTrace (prefixWord ++ tailWord_3637285) baseStart_3637285 baseEnd_3637285 := by
    simpa [prefixWord, tailWord_3637285, baseEnd_3637285] using wordTrace_append hprefix tailTrace_3637285
  have hstable : (prefixWord ++ tailWord_3637285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637285).length < 2 ^ (prefixWord ++ tailWord_3637285).sum := by decide
  have hdescent : baseEnd_3637285 < baseStart_3637285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637345 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 5, 5]
def baseStart_3637345 : Nat := 118140960795 + 3637345 * 2 ^ 59
def prefixEnd_3637345 : Nat := 4983230072969 + 3 ^ 40 * 3637345 * 2
def baseEnd_3637345 : Nat := 1245137527485451069773107

theorem tailTrace_3637345 : CollatzResearch.WordTrace tailWord_3637345 prefixEnd_3637345 1245137527485451069773107 := by
  unfold tailWord_3637345
  simp only [CollatzResearch.WordTrace]
  refine ⟨132664871007527748914129489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88443247338351832609419659 132664871007527748914129489)
  ·
    refine ⟨99498653255645811685597117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132664871007527748914129489 99498653255645811685597117)
    ·
      refine ⟨37311994970867179382098919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99498653255645811685597117 37311994970867179382098919)
      ·
        refine ⟨55967992456300769073148379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37311994970867179382098919 55967992456300769073148379)
        ·
          refine ⟨83951988684451153609722569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55967992456300769073148379 83951988684451153609722569)
          ·
            refine ⟨62963991513338365207291927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83951988684451153609722569 62963991513338365207291927)
            ·
              refine ⟨94445987270007547810937891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62963991513338365207291927 94445987270007547810937891)
              ·
                refine ⟨141668980905011321716406837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94445987270007547810937891 141668980905011321716406837)
                ·
                  refine ⟨13281466959844811410913141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141668980905011321716406837 13281466959844811410913141)
                  ·
                    refine ⟨1245137527485451069773107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13281466959844811410913141 1245137527485451069773107)
                    ·
                      rfl

theorem cell22_3637345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_3637345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637345 prefixEnd_3637345 := by exact prefixLift 3637345
  have htrace : WordTrace (prefixWord ++ tailWord_3637345) baseStart_3637345 baseEnd_3637345 := by
    simpa [prefixWord, tailWord_3637345, baseEnd_3637345] using wordTrace_append hprefix tailTrace_3637345
  have hstable : (prefixWord ++ tailWord_3637345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637345).length < 2 ^ (prefixWord ++ tailWord_3637345).sum := by decide
  have hdescent : baseEnd_3637345 < baseStart_3637345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637362 : List Nat := [3, 2, 1, 2, 2, 2, 1, 3, 1, 5]
def baseStart_3637362 : Nat := 118140960795 + 3637362 * 2 ^ 59
def prefixEnd_3637362 : Nat := 4983230072969 + 3 ^ 40 * 3637362 * 2
def baseEnd_3637362 : Nat := 1245143346932868692098055

theorem tailTrace_3637362 : CollatzResearch.WordTrace tailWord_3637362 prefixEnd_3637362 1245143346932868692098055 := by
  unfold tailWord_3637362
  simp only [CollatzResearch.WordTrace]
  refine ⟨33166372762116540204374585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88443660698977440544998893 33166372762116540204374585)
  ·
    refine ⟨24874779571587405153280939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33166372762116540204374585 24874779571587405153280939)
    ·
      refine ⟨37312169357381107729921409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24874779571587405153280939 37312169357381107729921409)
      ·
        refine ⟨27984127018035830797441057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37312169357381107729921409 27984127018035830797441057)
        ·
          refine ⟨20988095263526873098080793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27984127018035830797441057 20988095263526873098080793)
          ·
            refine ⟨15741071447645154823560595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20988095263526873098080793 15741071447645154823560595)
            ·
              refine ⟨23611607171467732235340893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15741071447645154823560595 23611607171467732235340893)
              ·
                refine ⟨8854352689300399588252835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23611607171467732235340893 8854352689300399588252835)
                ·
                  refine ⟨13281529033950599382379253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8854352689300399588252835 13281529033950599382379253)
                  ·
                    refine ⟨1245143346932868692098055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13281529033950599382379253 1245143346932868692098055)
                    ·
                      rfl

theorem cell22_3637362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_3637362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637362 prefixEnd_3637362 := by exact prefixLift 3637362
  have htrace : WordTrace (prefixWord ++ tailWord_3637362) baseStart_3637362 baseEnd_3637362 := by
    simpa [prefixWord, tailWord_3637362, baseEnd_3637362] using wordTrace_append hprefix tailTrace_3637362
  have hstable : (prefixWord ++ tailWord_3637362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637362).length < 2 ^ (prefixWord ++ tailWord_3637362).sum := by decide
  have hdescent : baseEnd_3637362 < baseStart_3637362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637482 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 8]
def baseStart_3637482 : Nat := 118140960795 + 3637482 * 2 ^ 59
def prefixEnd_3637482 : Nat := 4983230072969 + 3 ^ 40 * 3637482 * 2
def baseEnd_3637482 : Nat := 415061475128409459699229

theorem tailTrace_3637482 : CollatzResearch.WordTrace tailWord_3637482 prefixEnd_3637482 415061475128409459699229 := by
  unfold tailWord_3637482
  simp only [CollatzResearch.WordTrace]
  refine ⟨33167466952007855327966675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88446578538687614207911133 33167466952007855327966675)
  ·
    refine ⟨49751200428011782991950013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33167466952007855327966675 49751200428011782991950013)
    ·
      refine ⟨18656700160504418621981255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49751200428011782991950013 18656700160504418621981255)
      ·
        refine ⟨27985050240756627932971883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18656700160504418621981255 27985050240756627932971883)
        ·
          refine ⟨41977575361134941899457825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27985050240756627932971883 41977575361134941899457825)
          ·
            refine ⟨31483181520851206424593369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41977575361134941899457825 31483181520851206424593369)
            ·
              refine ⟨23612386140638404818445027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31483181520851206424593369 23612386140638404818445027)
              ·
                refine ⟨35418579210957607227667541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23612386140638404818445027 35418579210957607227667541)
                ·
                  refine ⟨415061475128409459699229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35418579210957607227667541 415061475128409459699229)
                  ·
                    rfl

theorem cell22_3637482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_3637482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637482 prefixEnd_3637482 := by exact prefixLift 3637482
  have htrace : WordTrace (prefixWord ++ tailWord_3637482) baseStart_3637482 baseEnd_3637482 := by
    simpa [prefixWord, tailWord_3637482, baseEnd_3637482] using wordTrace_append hprefix tailTrace_3637482
  have hstable : (prefixWord ++ tailWord_3637482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637482).length < 2 ^ (prefixWord ++ tailWord_3637482).sum := by decide
  have hdescent : baseEnd_3637482 < baseStart_3637482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637514 : List Nat := [3, 1, 2, 2, 1, 1, 2, 3, 4, 3]
def baseStart_3637514 : Nat := 118140960795 + 3637514 * 2 ^ 59
def prefixEnd_3637514 : Nat := 4983230072969 + 3 ^ 40 * 3637514 * 2
def baseEnd_3637514 : Nat := 1245195379639190962297589

theorem tailTrace_3637514 : CollatzResearch.WordTrace tailWord_3637514 prefixEnd_3637514 1245195379639190962297589 := by
  unfold tailWord_3637514
  simp only [CollatzResearch.WordTrace]
  refine ⟨33167758735978872694257899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88447356629276993851354397 33167758735978872694257899)
  ·
    refine ⟨49751638103968309041386849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33167758735978872694257899 49751638103968309041386849)
    ·
      refine ⟨37313728577976231781040137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49751638103968309041386849 37313728577976231781040137)
      ·
        refine ⟨27985296433482173835780103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37313728577976231781040137 27985296433482173835780103)
        ·
          refine ⟨41977944650223260753670155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27985296433482173835780103 41977944650223260753670155)
          ·
            refine ⟨62966916975334891130505233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41977944650223260753670155 62966916975334891130505233)
            ·
              refine ⟨47225187731501168347878925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62966916975334891130505233 47225187731501168347878925)
              ·
                refine ⟨17709445399312938130454597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47225187731501168347878925 17709445399312938130454597)
                ·
                  refine ⟨3320521012371175899460237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17709445399312938130454597 3320521012371175899460237)
                  ·
                    refine ⟨1245195379639190962297589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3320521012371175899460237 1245195379639190962297589)
                    ·
                      rfl

theorem cell22_3637514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_3637514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637514 prefixEnd_3637514 := by exact prefixLift 3637514
  have htrace : WordTrace (prefixWord ++ tailWord_3637514) baseStart_3637514 baseEnd_3637514 := by
    simpa [prefixWord, tailWord_3637514, baseEnd_3637514] using wordTrace_append hprefix tailTrace_3637514
  have hstable : (prefixWord ++ tailWord_3637514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637514).length < 2 ^ (prefixWord ++ tailWord_3637514).sum := by decide
  have hdescent : baseEnd_3637514 < baseStart_3637514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637546 : List Nat := [3, 1, 4, 2, 2, 1, 1, 1, 1, 6]
def baseStart_3637546 : Nat := 118140960795 + 3637546 * 2 ^ 59
def prefixEnd_3637546 : Nat := 4983230072969 + 3 ^ 40 * 3637546 * 2
def baseEnd_3637546 : Nat := 1245206333893153545497491

theorem tailTrace_3637546 : CollatzResearch.WordTrace tailWord_3637546 prefixEnd_3637546 1245206333893153545497491 := by
  unfold tailWord_3637546
  simp only [CollatzResearch.WordTrace]
  refine ⟨33168050519949890060549123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88448134719866373494797661 33168050519949890060549123)
  ·
    refine ⟨49752075779924835090823685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33168050519949890060549123 49752075779924835090823685)
    ·
      refine ⟨9328514208735906579529441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49752075779924835090823685 9328514208735906579529441)
      ·
        refine ⟨6996385656551929934647081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9328514208735906579529441 6996385656551929934647081)
        ·
          refine ⟨5247289242413947450985311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6996385656551929934647081 5247289242413947450985311)
          ·
            refine ⟨7870933863620921176477967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5247289242413947450985311 7870933863620921176477967)
            ·
              refine ⟨11806400795431381764716951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7870933863620921176477967 11806400795431381764716951)
              ·
                refine ⟨17709601193147072647075427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11806400795431381764716951 17709601193147072647075427)
                ·
                  refine ⟨26564401789720608970613141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17709601193147072647075427 26564401789720608970613141)
                  ·
                    refine ⟨1245206333893153545497491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26564401789720608970613141 1245206333893153545497491)
                    ·
                      rfl

theorem cell22_3637546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_3637546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637546 prefixEnd_3637546 := by exact prefixLift 3637546
  have htrace : WordTrace (prefixWord ++ tailWord_3637546) baseStart_3637546 baseEnd_3637546 := by
    simpa [prefixWord, tailWord_3637546, baseEnd_3637546] using wordTrace_append hprefix tailTrace_3637546
  have hstable : (prefixWord ++ tailWord_3637546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637546).length < 2 ^ (prefixWord ++ tailWord_3637546).sum := by decide
  have hdescent : baseEnd_3637546 < baseStart_3637546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637550 : List Nat := [4, 1, 3, 3, 1, 1, 2, 3, 4]
def baseStart_3637550 : Nat := 118140960795 + 3637550 * 2 ^ 59
def prefixEnd_3637550 : Nat := 4983230072969 + 3 ^ 40 * 3637550 * 2
def baseEnd_3637550 : Nat := 415069234391632956132493

theorem tailTrace_3637550 : CollatzResearch.WordTrace tailWord_3637550 prefixEnd_3637550 415069234391632956132493 := by
  unfold tailWord_3637550
  simp only [CollatzResearch.WordTrace]
  refine ⟨16584043496473133615667763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88448231981190045950228069 16584043496473133615667763)
  ·
    refine ⟨24876065244709700423501645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16584043496473133615667763 24876065244709700423501645)
    ·
      refine ⟨9328524466766137658813117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24876065244709700423501645 9328524466766137658813117)
      ·
        refine ⟨3498196675037301622054919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9328524466766137658813117 3498196675037301622054919)
        ·
          refine ⟨5247295012555952433082379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3498196675037301622054919 5247295012555952433082379)
          ·
            refine ⟨7870942518833928649623569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5247295012555952433082379 7870942518833928649623569)
            ·
              refine ⟨5903206889125446487217677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7870942518833928649623569 5903206889125446487217677)
              ·
                refine ⟨2213702583422042432706629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5903206889125446487217677 2213702583422042432706629)
                ·
                  refine ⟨415069234391632956132493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2213702583422042432706629 415069234391632956132493)
                  ·
                    rfl

theorem cell22_3637550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_3637550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637550 prefixEnd_3637550 := by exact prefixLift 3637550
  have htrace : WordTrace (prefixWord ++ tailWord_3637550) baseStart_3637550 baseEnd_3637550 := by
    simpa [prefixWord, tailWord_3637550, baseEnd_3637550] using wordTrace_append hprefix tailTrace_3637550
  have hstable : (prefixWord ++ tailWord_3637550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637550).length < 2 ^ (prefixWord ++ tailWord_3637550).sum := by decide
  have hdescent : baseEnd_3637550 < baseStart_3637550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637587 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 1, 7]
def baseStart_3637587 : Nat := 118140960795 + 3637587 * 2 ^ 59
def prefixEnd_3637587 : Nat := 4983230072969 + 3 ^ 40 * 3637587 * 2
def baseEnd_3637587 : Nat := 1245220369031043105222365

theorem tailTrace_3637587 : CollatzResearch.WordTrace tailWord_3637587 prefixEnd_3637587 1245220369031043105222365 := by
  unfold tailWord_3637587
  simp only [CollatzResearch.WordTrace]
  refine ⟨132673697472651024244439015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88449131648434016162959343 132673697472651024244439015)
  ·
    refine ⟨199010546208976536366658523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132673697472651024244439015 199010546208976536366658523)
    ·
      refine ⟨298515819313464804549987785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199010546208976536366658523 298515819313464804549987785)
      ·
        refine ⟨223886864485098603412490839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298515819313464804549987785 223886864485098603412490839)
        ·
          refine ⟨335830296727647905118736259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223886864485098603412490839 335830296727647905118736259)
          ·
            refine ⟨503745445091471857678104389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335830296727647905118736259 503745445091471857678104389)
            ·
              refine ⟨94452270954650973314644573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 503745445091471857678104389 94452270954650973314644573)
              ·
                refine ⟨35419601607994114992991715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94452270954650973314644573 35419601607994114992991715)
                ·
                  refine ⟨53129402411991172489487573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35419601607994114992991715 53129402411991172489487573)
                  ·
                    refine ⟨1245220369031043105222365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53129402411991172489487573 1245220369031043105222365)
                    ·
                      rfl

theorem cell22_3637587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 7].length) (baseStart_3637587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637587 prefixEnd_3637587 := by exact prefixLift 3637587
  have htrace : WordTrace (prefixWord ++ tailWord_3637587) baseStart_3637587 baseEnd_3637587 := by
    simpa [prefixWord, tailWord_3637587, baseEnd_3637587] using wordTrace_append hprefix tailTrace_3637587
  have hstable : (prefixWord ++ tailWord_3637587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637587).length < 2 ^ (prefixWord ++ tailWord_3637587).sum := by decide
  have hdescent : baseEnd_3637587 < baseStart_3637587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637610 : List Nat := [3, 1, 3, 3, 1, 1, 3, 3, 1, 3]
def baseStart_3637610 : Nat := 118140960795 + 3637610 * 2 ^ 59
def prefixEnd_3637610 : Nat := 4983230072969 + 3 ^ 40 * 3637610 * 2
def baseEnd_3637610 : Nat := 1245228242401078711897295

theorem tailTrace_3637610 : CollatzResearch.WordTrace tailWord_3637610 prefixEnd_3637610 1245228242401078711897295 := by
  unfold tailWord_3637610
  simp only [CollatzResearch.WordTrace]
  refine ⟨33168634087891924793131571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88449690901045132781684189 33168634087891924793131571)
  ·
    refine ⟨49752951131837887189697357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33168634087891924793131571 49752951131837887189697357)
    ·
      refine ⟨18657356674439207696136509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49752951131837887189697357 18657356674439207696136509)
      ·
        refine ⟨6996508752914702886051191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18657356674439207696136509 6996508752914702886051191)
        ·
          refine ⟨10494763129372054329076787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6996508752914702886051191 10494763129372054329076787)
          ·
            refine ⟨15742144694058081493615181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10494763129372054329076787 15742144694058081493615181)
            ·
              refine ⟨5903304260271780560105693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15742144694058081493615181 5903304260271780560105693)
              ·
                refine ⟨2213739097601917710039635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5903304260271780560105693 2213739097601917710039635)
                ·
                  refine ⟨3320608646402876565059453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2213739097601917710039635 3320608646402876565059453)
                  ·
                    refine ⟨1245228242401078711897295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3320608646402876565059453 1245228242401078711897295)
                    ·
                      rfl

theorem cell22_3637610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_3637610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637610 prefixEnd_3637610 := by exact prefixLift 3637610
  have htrace : WordTrace (prefixWord ++ tailWord_3637610) baseStart_3637610 baseEnd_3637610 := by
    simpa [prefixWord, tailWord_3637610, baseEnd_3637610] using wordTrace_append hprefix tailTrace_3637610
  have hstable : (prefixWord ++ tailWord_3637610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637610).length < 2 ^ (prefixWord ++ tailWord_3637610).sum := by decide
  have hdescent : baseEnd_3637610 < baseStart_3637610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637666 : List Nat := [3, 3, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_3637666 : Nat := 118140960795 + 3637666 * 2 ^ 59
def prefixEnd_3637666 : Nat := 4983230072969 + 3 ^ 40 * 3637666 * 2
def baseEnd_3637666 : Nat := 1245247412345513232497123

theorem tailTrace_3637666 : CollatzResearch.WordTrace tailWord_3637666 prefixEnd_3637666 1245247412345513232497123 := by
  unfold tailWord_3637666
  simp only [CollatzResearch.WordTrace]
  refine ⟨33169144709841205184141213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88451052559576547157709901 33169144709841205184141213)
  ·
    refine ⟨12438429266190451944052955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33169144709841205184141213 12438429266190451944052955)
    ·
      refine ⟨18657643899285677916079433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12438429266190451944052955 18657643899285677916079433)
      ·
        refine ⟨13993232924464258437059575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18657643899285677916079433 13993232924464258437059575)
        ·
          refine ⟨20989849386696387655589363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13993232924464258437059575 20989849386696387655589363)
          ·
            refine ⟨31484774080044581483384045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20989849386696387655589363 31484774080044581483384045)
            ·
              refine ⟨11806790280016718056269017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31484774080044581483384045 11806790280016718056269017)
              ·
                refine ⟨8855092710012538542201763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11806790280016718056269017 8855092710012538542201763)
                ·
                  refine ⟨13282639065018807813302645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8855092710012538542201763 13282639065018807813302645)
                  ·
                    refine ⟨1245247412345513232497123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13282639065018807813302645 1245247412345513232497123)
                    ·
                      rfl

theorem cell22_3637666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_3637666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637666 prefixEnd_3637666 := by exact prefixLift 3637666
  have htrace : WordTrace (prefixWord ++ tailWord_3637666) baseStart_3637666 baseEnd_3637666 := by
    simpa [prefixWord, tailWord_3637666, baseEnd_3637666] using wordTrace_append hprefix tailTrace_3637666
  have hstable : (prefixWord ++ tailWord_3637666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637666).length < 2 ^ (prefixWord ++ tailWord_3637666).sum := by decide
  have hdescent : baseEnd_3637666 < baseStart_3637666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637681 : List Nat := [1, 2, 2, 4, 1, 2, 2, 2, 2, 4]
def baseStart_3637681 : Nat := 118140960795 + 3637681 * 2 ^ 59
def prefixEnd_3637681 : Nat := 4983230072969 + 3 ^ 40 * 3637681 * 2
def baseEnd_3637681 : Nat := 1245252547152058193372077

theorem tailTrace_3637681 : CollatzResearch.WordTrace tailWord_3637681 prefixEnd_3637681 1245252547152058193372077 := by
  unfold tailWord_3637681
  simp only [CollatzResearch.WordTrace]
  refine ⟨132677125934310478298360897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88451417289540318865573931 132677125934310478298360897)
  ·
    refine ⟨99507844450732858723770673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132677125934310478298360897 99507844450732858723770673)
    ·
      refine ⟨74630883338049644042828005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99507844450732858723770673 74630883338049644042828005)
      ·
        refine ⟨13993290625884308258030251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74630883338049644042828005 13993290625884308258030251)
        ·
          refine ⟨20989935938826462387045377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13993290625884308258030251 20989935938826462387045377)
          ·
            refine ⟨15742451954119846790284033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20989935938826462387045377 15742451954119846790284033)
            ·
              refine ⟨11806838965589885092713025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15742451954119846790284033 11806838965589885092713025)
              ·
                refine ⟨8855129224192413819534769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11806838965589885092713025 8855129224192413819534769)
                ·
                  refine ⟨6641346918144310364651077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8855129224192413819534769 6641346918144310364651077)
                  ·
                    refine ⟨1245252547152058193372077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6641346918144310364651077 1245252547152058193372077)
                    ·
                      rfl

theorem cell22_3637681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_3637681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637681 prefixEnd_3637681 := by exact prefixLift 3637681
  have htrace : WordTrace (prefixWord ++ tailWord_3637681) baseStart_3637681 baseEnd_3637681 := by
    simpa [prefixWord, tailWord_3637681, baseEnd_3637681] using wordTrace_append hprefix tailTrace_3637681
  have hstable : (prefixWord ++ tailWord_3637681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637681).length < 2 ^ (prefixWord ++ tailWord_3637681).sum := by decide
  have hdescent : baseEnd_3637681 < baseStart_3637681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637739 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 4, 5]
def baseStart_3637739 : Nat := 118140960795 + 3637739 * 2 ^ 59
def prefixEnd_3637739 : Nat := 4983230072969 + 3 ^ 40 * 3637739 * 2
def baseEnd_3637739 : Nat := 1245272401737365375421899

theorem tailTrace_3637739 : CollatzResearch.WordTrace tailWord_3637739 prefixEnd_3637739 1245272401737365375421899 := by
  unfold tailWord_3637739
  simp only [CollatzResearch.WordTrace]
  refine ⟨132679241368100354203972271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88452827578733569469314847 132679241368100354203972271)
  ·
    refine ⟨199018862052150531305958407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132679241368100354203972271 199018862052150531305958407)
    ·
      refine ⟨298528293078225796958937611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199018862052150531305958407 298528293078225796958937611)
      ·
        refine ⟨447792439617338695438406417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298528293078225796958937611 447792439617338695438406417)
        ·
          refine ⟨335844329713004021578804813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447792439617338695438406417 335844329713004021578804813)
          ·
            refine ⟨125941623642376508092051805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335844329713004021578804813 125941623642376508092051805)
            ·
              refine ⟨47228108865891190534519427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125941623642376508092051805 47228108865891190534519427)
              ·
                refine ⟨70842163298836785801779141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47228108865891190534519427 70842163298836785801779141)
                ·
                  refine ⟨13282905618531897337833589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70842163298836785801779141 13282905618531897337833589)
                  ·
                    refine ⟨1245272401737365375421899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13282905618531897337833589 1245272401737365375421899)
                    ·
                      rfl

theorem cell22_3637739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 5].length) (baseStart_3637739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637739 prefixEnd_3637739 := by exact prefixLift 3637739
  have htrace : WordTrace (prefixWord ++ tailWord_3637739) baseStart_3637739 baseEnd_3637739 := by
    simpa [prefixWord, tailWord_3637739, baseEnd_3637739] using wordTrace_append hprefix tailTrace_3637739
  have hstable : (prefixWord ++ tailWord_3637739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637739).length < 2 ^ (prefixWord ++ tailWord_3637739).sum := by decide
  have hdescent : baseEnd_3637739 < baseStart_3637739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637754 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 2, 8]
def baseStart_3637754 : Nat := 118140960795 + 3637754 * 2 ^ 59
def prefixEnd_3637754 : Nat := 4983230072969 + 3 ^ 40 * 3637754 * 2
def baseEnd_3637754 : Nat := 1245277536543910336296853

theorem tailTrace_3637754 : CollatzResearch.WordTrace tailWord_3637754 prefixEnd_3637754 1245277536543910336296853 := by
  unfold tailWord_3637754
  simp only [CollatzResearch.WordTrace]
  refine ⟨33169947115761502941442079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88453192308697341177178877 33169947115761502941442079)
  ·
    refine ⟨49754920673642254412163119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33169947115761502941442079 49754920673642254412163119)
    ·
      refine ⟨74632381010463381618244679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49754920673642254412163119 74632381010463381618244679)
      ·
        refine ⟨111948571515695072427367019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74632381010463381618244679 111948571515695072427367019)
        ·
          refine ⟨167922857273542608641050529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111948571515695072427367019 167922857273542608641050529)
          ·
            refine ⟨125942142955156956480787897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167922857273542608641050529 125942142955156956480787897)
            ·
              refine ⟨94456607216367717360590923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125942142955156956480787897 94456607216367717360590923)
              ·
                refine ⟨141684910824551576040886385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94456607216367717360590923 141684910824551576040886385)
                ·
                  refine ⟨106263683118413682030664789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141684910824551576040886385 106263683118413682030664789)
                  ·
                    refine ⟨1245277536543910336296853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106263683118413682030664789 1245277536543910336296853)
                    ·
                      rfl

theorem cell22_3637754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_3637754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637754 prefixEnd_3637754 := by exact prefixLift 3637754
  have htrace : WordTrace (prefixWord ++ tailWord_3637754) baseStart_3637754 baseEnd_3637754 := by
    simpa [prefixWord, tailWord_3637754, baseEnd_3637754] using wordTrace_append hprefix tailTrace_3637754
  have hstable : (prefixWord ++ tailWord_3637754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637754).length < 2 ^ (prefixWord ++ tailWord_3637754).sum := by decide
  have hdescent : baseEnd_3637754 < baseStart_3637754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637769 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 8]
def baseStart_3637769 : Nat := 118140960795 + 3637769 * 2 ^ 59
def prefixEnd_3637769 : Nat := 4983230072969 + 3 ^ 40 * 3637769 * 2
def baseEnd_3637769 : Nat := 415094223783485099057269

theorem tailTrace_3637769 : CollatzResearch.WordTrace tailWord_3637769 prefixEnd_3637769 415094223783485099057269 := by
  unfold tailWord_3637769
  simp only [CollatzResearch.WordTrace]
  refine ⟨132680335557991669327564361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88453557038661112885042907 132680335557991669327564361)
  ·
    refine ⟨99510251668493751995673271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132680335557991669327564361 99510251668493751995673271)
    ·
      refine ⟨149265377502740627993509907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99510251668493751995673271 149265377502740627993509907)
      ·
        refine ⟨223898066254110941990264861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149265377502740627993509907 223898066254110941990264861)
        ·
          refine ⟨83961774845291603246349323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223898066254110941990264861 83961774845291603246349323)
          ·
            refine ⟨125942662267937404869523985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83961774845291603246349323 125942662267937404869523985)
            ·
              refine ⟨94456996700953053652142989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125942662267937404869523985 94456996700953053652142989)
              ·
                refine ⟨35421373762857395119553621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94456996700953053652142989 35421373762857395119553621)
                ·
                  refine ⟨415094223783485099057269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35421373762857395119553621 415094223783485099057269)
                  ·
                    rfl

theorem cell22_3637769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 8].length) (baseStart_3637769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637769 prefixEnd_3637769 := by exact prefixLift 3637769
  have htrace : WordTrace (prefixWord ++ tailWord_3637769) baseStart_3637769 baseEnd_3637769 := by
    simpa [prefixWord, tailWord_3637769, baseEnd_3637769] using wordTrace_append hprefix tailTrace_3637769
  have hstable : (prefixWord ++ tailWord_3637769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637769).length < 2 ^ (prefixWord ++ tailWord_3637769).sum := by decide
  have hdescent : baseEnd_3637769 < baseStart_3637769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637788 : List Nat := [2, 2, 3, 1, 2, 2, 2, 3, 1, 4]
def baseStart_3637788 : Nat := 118140960795 + 3637788 * 2 ^ 59
def prefixEnd_3637788 : Nat := 4983230072969 + 3 ^ 40 * 3637788 * 2
def baseEnd_3637788 : Nat := 1245289175438745580946749

theorem tailTrace_3637788 : CollatzResearch.WordTrace tailWord_3637788 prefixEnd_3637788 1245289175438745580946749 := by
  unfold tailWord_3637788
  simp only [CollatzResearch.WordTrace]
  refine ⟨66340514272461417786253009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88454019029948557048337345 66340514272461417786253009)
  ·
    refine ⟨49755385704346063339689757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66340514272461417786253009 49755385704346063339689757)
    ·
      refine ⟨18658269639129773752383659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49755385704346063339689757 18658269639129773752383659)
      ·
        refine ⟨27987404458694660628575489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18658269639129773752383659 27987404458694660628575489)
        ·
          refine ⟨20990553344020995471431617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27987404458694660628575489 20990553344020995471431617)
          ·
            refine ⟨15742915008015746603573713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20990553344020995471431617 15742915008015746603573713)
            ·
              refine ⟨11807186256011809952680285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15742915008015746603573713 11807186256011809952680285)
              ·
                refine ⟨4427694846004428732255107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11807186256011809952680285 4427694846004428732255107)
                ·
                  refine ⟨6641542269006643098382661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4427694846004428732255107 6641542269006643098382661)
                  ·
                    refine ⟨1245289175438745580946749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6641542269006643098382661 1245289175438745580946749)
                    ·
                      rfl

theorem cell22_3637788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_3637788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637788 prefixEnd_3637788 := by exact prefixLift 3637788
  have htrace : WordTrace (prefixWord ++ tailWord_3637788) baseStart_3637788 baseEnd_3637788 := by
    simpa [prefixWord, tailWord_3637788, baseEnd_3637788] using wordTrace_append hprefix tailTrace_3637788
  have hstable : (prefixWord ++ tailWord_3637788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637788).length < 2 ^ (prefixWord ++ tailWord_3637788).sum := by decide
  have hdescent : baseEnd_3637788 < baseStart_3637788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637816 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 4, 4]
def baseStart_3637816 : Nat := 118140960795 + 3637816 * 2 ^ 59
def prefixEnd_3637816 : Nat := 4983230072969 + 3 ^ 40 * 3637816 * 2
def baseEnd_3637816 : Nat := 1245298760410962841246663

theorem tailTrace_3637816 : CollatzResearch.WordTrace tailWord_3637816 prefixEnd_3637816 1245298760410962841246663 := by
  unfold tailWord_3637816
  simp only [CollatzResearch.WordTrace]
  refine ⟨66341024894410698177262651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88454699859214264236350201 66341024894410698177262651)
  ·
    refine ⟨99511537341616047265893977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66341024894410698177262651 99511537341616047265893977)
    ·
      refine ⟨74633653006212035449420483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99511537341616047265893977 74633653006212035449420483)
      ·
        refine ⟨111950479509318053174130725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74633653006212035449420483 111950479509318053174130725)
        ·
          refine ⟨20990714907997134970149511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111950479509318053174130725 20990714907997134970149511)
          ·
            refine ⟨31486072361995702455224267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20990714907997134970149511 31486072361995702455224267)
            ·
              refine ⟨47229108542993553682836401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31486072361995702455224267 47229108542993553682836401)
              ·
                refine ⟨35421831407245165262127301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47229108542993553682836401 35421831407245165262127301)
                ·
                  refine ⟨6641593388858468486648869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35421831407245165262127301 6641593388858468486648869)
                  ·
                    refine ⟨1245298760410962841246663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6641593388858468486648869 1245298760410962841246663)
                    ·
                      rfl

theorem cell22_3637816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_3637816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637816 prefixEnd_3637816 := by exact prefixLift 3637816
  have htrace : WordTrace (prefixWord ++ tailWord_3637816) baseStart_3637816 baseEnd_3637816 := by
    simpa [prefixWord, tailWord_3637816, baseEnd_3637816] using wordTrace_append hprefix tailTrace_3637816
  have hstable : (prefixWord ++ tailWord_3637816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637816).length < 2 ^ (prefixWord ++ tailWord_3637816).sum := by decide
  have hdescent : baseEnd_3637816 < baseStart_3637816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637831 : List Nat := [1, 1, 4, 1, 4, 1, 2, 8]
def baseStart_3637831 : Nat := 118140960795 + 3637831 * 2 ^ 59
def prefixEnd_3637831 : Nat := 4983230072969 + 3 ^ 40 * 3637831 * 2
def baseEnd_3637831 : Nat := 138367099468611978013513

theorem tailTrace_3637831 : CollatzResearch.WordTrace tailWord_3637831 prefixEnd_3637831 138367099468611978013513 := by
  unfold tailWord_3637831
  simp only [CollatzResearch.WordTrace]
  refine ⟨132682596883767053916321347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88455064589178035944214231 132682596883767053916321347)
  ·
    refine ⟨199023895325650580874482021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132682596883767053916321347 199023895325650580874482021)
    ·
      refine ⟨37316980373559483913965379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199023895325650580874482021 37316980373559483913965379)
      ·
        refine ⟨55975470560339225870948069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37316980373559483913965379 55975470560339225870948069)
        ·
          refine ⟨10495400730063604850802763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55975470560339225870948069 10495400730063604850802763)
          ·
            refine ⟨15743101095095407276204145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10495400730063604850802763 15743101095095407276204145)
            ·
              refine ⟨11807325821321555457153109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15743101095095407276204145 11807325821321555457153109)
              ·
                refine ⟨138367099468611978013513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11807325821321555457153109 138367099468611978013513)
                ·
                  rfl

theorem cell22_3637831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 8].length) (baseStart_3637831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637831 prefixEnd_3637831 := by exact prefixLift 3637831
  have htrace : WordTrace (prefixWord ++ tailWord_3637831) baseStart_3637831 baseEnd_3637831 := by
    simpa [prefixWord, tailWord_3637831, baseEnd_3637831] using wordTrace_append hprefix tailTrace_3637831
  have hstable : (prefixWord ++ tailWord_3637831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637831).length < 2 ^ (prefixWord ++ tailWord_3637831).sum := by decide
  have hdescent : baseEnd_3637831 < baseStart_3637831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637852 : List Nat := [2, 2, 4, 1, 3, 1, 2, 2, 2, 3]
def baseStart_3637852 : Nat := 118140960795 + 3637852 * 2 ^ 59
def prefixEnd_3637852 : Nat := 4983230072969 + 3 ^ 40 * 3637852 * 2
def baseEnd_3637852 : Nat := 1245311083946670747346553

theorem tailTrace_3637852 : CollatzResearch.WordTrace tailWord_3637852 prefixEnd_3637852 1245311083946670747346553 := by
  unfold tailWord_3637852
  simp only [CollatzResearch.WordTrace]
  refine ⟨66341681408345487251417905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88455575211127316335223873 66341681408345487251417905)
  ·
    refine ⟨49756261056259115438563429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66341681408345487251417905 49756261056259115438563429)
    ·
      refine ⟨9329298948048584144730643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49756261056259115438563429 9329298948048584144730643)
      ·
        refine ⟨13993948422072876217095965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9329298948048584144730643 13993948422072876217095965)
        ·
          refine ⟨5247730658277328581410987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13993948422072876217095965 5247730658277328581410987)
          ·
            refine ⟨7871595987415992872116481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5247730658277328581410987 7871595987415992872116481)
            ·
              refine ⟨5903696990561994654087361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7871595987415992872116481 5903696990561994654087361)
              ·
                refine ⟨4427772742921495990565521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5903696990561994654087361 4427772742921495990565521)
                ·
                  refine ⟨3320829557191121992924141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4427772742921495990565521 3320829557191121992924141)
                  ·
                    refine ⟨1245311083946670747346553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3320829557191121992924141 1245311083946670747346553)
                    ·
                      rfl

theorem cell22_3637852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_3637852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637852 prefixEnd_3637852 := by exact prefixLift 3637852
  have htrace : WordTrace (prefixWord ++ tailWord_3637852) baseStart_3637852 baseEnd_3637852 := by
    simpa [prefixWord, tailWord_3637852, baseEnd_3637852] using wordTrace_append hprefix tailTrace_3637852
  have hstable : (prefixWord ++ tailWord_3637852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637852).length < 2 ^ (prefixWord ++ tailWord_3637852).sum := by decide
  have hdescent : baseEnd_3637852 < baseStart_3637852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637863 : List Nat := [1, 1, 5, 1, 1, 1, 1, 5, 3, 3]
def baseStart_3637863 : Nat := 118140960795 + 3637863 * 2 ^ 59
def prefixEnd_3637863 : Nat := 4983230072969 + 3 ^ 40 * 3637863 * 2
def baseEnd_3637863 : Nat := 1245314849471470385321519

theorem tailTrace_3637863 : CollatzResearch.WordTrace tailWord_3637863 prefixEnd_3637863 1245314849471470385321519 := by
  unfold tailWord_3637863
  simp only [CollatzResearch.WordTrace]
  refine ⟨132683764019651123381486243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88455842679767415587657495 132683764019651123381486243)
  ·
    refine ⟨199025646029476685072229365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132683764019651123381486243 199025646029476685072229365)
    ·
      refine ⟨18658654315263439225521503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 199025646029476685072229365 18658654315263439225521503)
      ·
        refine ⟨27987981472895158838282255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18658654315263439225521503 27987981472895158838282255)
        ·
          refine ⟨41981972209342738257423383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27987981472895158838282255 41981972209342738257423383)
          ·
            refine ⟨62972958314014107386135075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41981972209342738257423383 62972958314014107386135075)
            ·
              refine ⟨94459437471021161079202613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62972958314014107386135075 94459437471021161079202613)
              ·
                refine ⟨8855572262908233851175245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94459437471021161079202613 8855572262908233851175245)
                ·
                  refine ⟨3320839598590587694190717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8855572262908233851175245 3320839598590587694190717)
                  ·
                    refine ⟨1245314849471470385321519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3320839598590587694190717 1245314849471470385321519)
                    ·
                      rfl

theorem cell22_3637863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_3637863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637863 prefixEnd_3637863 := by exact prefixLift 3637863
  have htrace : WordTrace (prefixWord ++ tailWord_3637863) baseStart_3637863 baseEnd_3637863 := by
    simpa [prefixWord, tailWord_3637863, baseEnd_3637863] using wordTrace_append hprefix tailTrace_3637863
  have hstable : (prefixWord ++ tailWord_3637863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637863).length < 2 ^ (prefixWord ++ tailWord_3637863).sum := by decide
  have hdescent : baseEnd_3637863 < baseStart_3637863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637972 : List Nat := [2, 4, 1, 3, 2, 2, 1, 1, 6]
def baseStart_3637972 : Nat := 118140960795 + 3637972 * 2 ^ 59
def prefixEnd_3637972 : Nat := 4983230072969 + 3 ^ 40 * 3637972 * 2
def baseEnd_3637972 : Nat := 415117387466343478115395

theorem tailTrace_3637972 : CollatzResearch.WordTrace tailWord_3637972 prefixEnd_3637972 415117387466343478115395 := by
  unfold tailWord_3637972
  simp only [CollatzResearch.WordTrace]
  refine ⟨66343869788128117498602085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88458493050837489998136113 66343869788128117498602085)
  ·
    refine ⟨12439475585274022030987891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66343869788128117498602085 12439475585274022030987891)
    ·
      refine ⟨18659213377911033046481837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12439475585274022030987891 18659213377911033046481837)
      ·
        refine ⟨6997205016716637392430689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18659213377911033046481837 6997205016716637392430689)
        ·
          refine ⟨5247903762537478044323017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6997205016716637392430689 5247903762537478044323017)
          ·
            refine ⟨3935927821903108533242263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5247903762537478044323017 3935927821903108533242263)
            ·
              refine ⟨5903891732854662799863395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3935927821903108533242263 5903891732854662799863395)
              ·
                refine ⟨8855837599281994199795093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5903891732854662799863395 8855837599281994199795093)
                ·
                  refine ⟨415117387466343478115395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8855837599281994199795093 415117387466343478115395)
                  ·
                    rfl

theorem cell22_3637972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_3637972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637972 prefixEnd_3637972 := by exact prefixLift 3637972
  have htrace : WordTrace (prefixWord ++ tailWord_3637972) baseStart_3637972 baseEnd_3637972 := by
    simpa [prefixWord, tailWord_3637972, baseEnd_3637972] using wordTrace_append hprefix tailTrace_3637972
  have hstable : (prefixWord ++ tailWord_3637972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637972).length < 2 ^ (prefixWord ++ tailWord_3637972).sum := by decide
  have hdescent : baseEnd_3637972 < baseStart_3637972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637983 : List Nat := [1, 1, 2, 3, 2, 4, 2, 7]
def baseStart_3637983 : Nat := 118140960795 + 3637983 * 2 ^ 59
def prefixEnd_3637983 : Nat := 4983230072969 + 3 ^ 40 * 3637983 * 2
def baseEnd_3637983 : Nat := 138372880880425563591239

theorem tailTrace_3637983 : CollatzResearch.WordTrace tailWord_3637983 prefixEnd_3637983 138372880880425563591239 := by
  unfold tailWord_3637983
  simp only [CollatzResearch.WordTrace]
  refine ⟨132688140779216383875854603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88458760519477589250569735 132688140779216383875854603)
  ·
    refine ⟨199032211168824575813781905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132688140779216383875854603 199032211168824575813781905)
    ·
      refine ⟨149274158376618431860336429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199032211168824575813781905 149274158376618431860336429)
      ·
        refine ⟨55977809391231911947626161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149274158376618431860336429 55977809391231911947626161)
        ·
          refine ⟨41983357043423933960719621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55977809391231911947626161 41983357043423933960719621)
          ·
            refine ⟨7871879445641987617634929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41983357043423933960719621 7871879445641987617634929)
            ·
              refine ⟨5903909584231490713226197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7871879445641987617634929 5903909584231490713226197)
              ·
                refine ⟨138372880880425563591239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5903909584231490713226197 138372880880425563591239)
                ·
                  rfl

theorem cell22_3637983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 7].length) (baseStart_3637983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637983 prefixEnd_3637983 := by exact prefixLift 3637983
  have htrace : WordTrace (prefixWord ++ tailWord_3637983) baseStart_3637983 baseEnd_3637983 := by
    simpa [prefixWord, tailWord_3637983, baseEnd_3637983] using wordTrace_append hprefix tailTrace_3637983
  have hstable : (prefixWord ++ tailWord_3637983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637983).length < 2 ^ (prefixWord ++ tailWord_3637983).sum := by decide
  have hdescent : baseEnd_3637983 < baseStart_3637983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637987 : List Nat := [1, 1, 1, 7, 1, 2, 1, 3, 2, 3]
def baseStart_3637987 : Nat := 118140960795 + 3637987 * 2 ^ 59
def prefixEnd_3637987 : Nat := 4983230072969 + 3 ^ 40 * 3637987 * 2
def baseEnd_3637987 : Nat := 1245357297205575395221139

theorem tailTrace_3637987 : CollatzResearch.WordTrace tailWord_3637987 prefixEnd_3637987 1245357297205575395221139 := by
  unfold tailWord_3637987
  simp only [CollatzResearch.WordTrace]
  refine ⟨132688286671201892559000215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88458857780801261706000143 132688286671201892559000215)
  ·
    refine ⟨199032430006802838838500323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132688286671201892559000215 199032430006802838838500323)
    ·
      refine ⟨298548645010204258257750485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199032430006802838838500323 298548645010204258257750485)
      ·
        refine ⟨6997233867426662302916027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 298548645010204258257750485 6997233867426662302916027)
        ·
          refine ⟨10495850801139993454374041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6997233867426662302916027 10495850801139993454374041)
          ·
            refine ⟨7871888100854995090780531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10495850801139993454374041 7871888100854995090780531)
            ·
              refine ⟨11807832151282492636170797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7871888100854995090780531 11807832151282492636170797)
              ·
                refine ⟨4427937056730934738564049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11807832151282492636170797 4427937056730934738564049)
                ·
                  refine ⟨3320952792548201053923037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4427937056730934738564049 3320952792548201053923037)
                  ·
                    refine ⟨1245357297205575395221139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3320952792548201053923037 1245357297205575395221139)
                    ·
                      rfl

theorem cell22_3637987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2, 3].length) (baseStart_3637987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3637987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3637987 prefixEnd_3637987 := by exact prefixLift 3637987
  have htrace : WordTrace (prefixWord ++ tailWord_3637987) baseStart_3637987 baseEnd_3637987 := by
    simpa [prefixWord, tailWord_3637987, baseEnd_3637987] using wordTrace_append hprefix tailTrace_3637987
  have hstable : (prefixWord ++ tailWord_3637987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637987).length < 2 ^ (prefixWord ++ tailWord_3637987).sum := by decide
  have hdescent : baseEnd_3637987 < baseStart_3637987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638004 : List Nat := [2, 6, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_3638004 : Nat := 118140960795 + 3638004 * 2 ^ 59
def prefixEnd_3638004 : Nat := 4983230072969 + 3 ^ 40 * 3638004 * 2
def baseEnd_3638004 : Nat := 1245363116652993017546087

theorem tailTrace_3638004 : CollatzResearch.WordTrace tailWord_3638004 prefixEnd_3638004 1245363116652993017546087 := by
  unfold tailWord_3638004
  simp only [CollatzResearch.WordTrace]
  refine ⟨66344453356070152231184533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88459271141426869641579377 66344453356070152231184533)
  ·
    refine ⟨3109896251065788385836775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66344453356070152231184533 3109896251065788385836775)
    ·
      refine ⟨4664844376598682578755163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3109896251065788385836775 4664844376598682578755163)
      ·
        refine ⟨6997266564898023868132745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4664844376598682578755163 6997266564898023868132745)
        ·
          refine ⟨5247949923673517901099559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6997266564898023868132745 5247949923673517901099559)
          ·
            refine ⟨7871924885510276851649339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5247949923673517901099559 7871924885510276851649339)
            ·
              refine ⟨11807887328265415277474009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7871924885510276851649339 11807887328265415277474009)
              ·
                refine ⟨8855915496199061458105507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11807887328265415277474009 8855915496199061458105507)
                ·
                  refine ⟨13283873244298592187158261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8855915496199061458105507 13283873244298592187158261)
                  ·
                    refine ⟨1245363116652993017546087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13283873244298592187158261 1245363116652993017546087)
                    ·
                      rfl

theorem cell22_3638004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_3638004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3638004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3638004 prefixEnd_3638004 := by exact prefixLift 3638004
  have htrace : WordTrace (prefixWord ++ tailWord_3638004) baseStart_3638004 baseEnd_3638004 := by
    simpa [prefixWord, tailWord_3638004, baseEnd_3638004] using wordTrace_append hprefix tailTrace_3638004
  have hstable : (prefixWord ++ tailWord_3638004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638004).length < 2 ^ (prefixWord ++ tailWord_3638004).sum := by decide
  have hdescent : baseEnd_3638004 < baseStart_3638004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638034 : List Nat := [3, 2, 4, 1, 3, 1, 1, 7]
def baseStart_3638034 : Nat := 118140960795 + 3638034 * 2 ^ 59
def prefixEnd_3638034 : Nat := 4983230072969 + 3 ^ 40 * 3638034 * 2
def baseEnd_3638034 : Nat := 138374820696231437699555

theorem tailTrace_3638034 : CollatzResearch.WordTrace tailWord_3638034 prefixEnd_3638034 138374820696231437699555 := by
  unfold tailWord_3638034
  simp only [CollatzResearch.WordTrace]
  refine ⟨33172500225507904896490289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88460000601354413057307437 33172500225507904896490289)
  ·
    refine ⟨24879375169130928672367717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33172500225507904896490289 24879375169130928672367717)
    ·
      refine ⟨4664882844212049126068947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24879375169130928672367717 4664882844212049126068947)
      ·
        refine ⟨6997324266318073689103421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4664882844212049126068947 6997324266318073689103421)
        ·
          refine ⟨2623996599869277633413783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6997324266318073689103421 2623996599869277633413783)
          ·
            refine ⟨3935994899803916450120675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2623996599869277633413783 3935994899803916450120675)
            ·
              refine ⟨5903992349705874675181013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3935994899803916450120675 5903992349705874675181013)
              ·
                refine ⟨138374820696231437699555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5903992349705874675181013 138374820696231437699555)
                ·
                  rfl

theorem cell22_3638034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 7].length) (baseStart_3638034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3638034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3638034 prefixEnd_3638034 := by exact prefixLift 3638034
  have htrace : WordTrace (prefixWord ++ tailWord_3638034) baseStart_3638034 baseEnd_3638034 := by
    simpa [prefixWord, tailWord_3638034, baseEnd_3638034] using wordTrace_append hprefix tailTrace_3638034
  have hstable : (prefixWord ++ tailWord_3638034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638034).length < 2 ^ (prefixWord ++ tailWord_3638034).sum := by decide
  have hdescent : baseEnd_3638034 < baseStart_3638034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638105 : List Nat := [1, 2, 1, 2, 2, 4, 3, 1, 1, 5]
def baseStart_3638105 : Nat := 118140960795 + 3638105 * 2 ^ 59
def prefixEnd_3638105 : Nat := 4983230072969 + 3 ^ 40 * 3638105 * 2
def baseEnd_3638105 : Nat := 1245397691017062420770777

theorem tailTrace_3638105 : CollatzResearch.WordTrace tailWord_3638105 prefixEnd_3638105 1245397691017062420770777 := by
  unfold tailWord_3638105
  simp only [CollatzResearch.WordTrace]
  refine ⟨132692590484774398711795769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88461726989849599141197179 132692590484774398711795769)
  ·
    refine ⟨99519442863580799033846827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132692590484774398711795769 99519442863580799033846827)
    ·
      refine ⟨149279164295371198550770241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99519442863580799033846827 149279164295371198550770241)
      ·
        refine ⟨111959373221528398913077681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149279164295371198550770241 111959373221528398913077681)
        ·
          refine ⟨83969529916146299184808261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111959373221528398913077681 83969529916146299184808261)
          ·
            refine ⟨15744286859277431097151549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83969529916146299184808261 15744286859277431097151549)
            ·
              refine ⟨5904107572229036661431831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15744286859277431097151549 5904107572229036661431831)
              ·
                refine ⟨8856161358343554992147747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5904107572229036661431831 8856161358343554992147747)
                ·
                  refine ⟨13284242037515332488221621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8856161358343554992147747 13284242037515332488221621)
                  ·
                    refine ⟨1245397691017062420770777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13284242037515332488221621 1245397691017062420770777)
                    ·
                      rfl

theorem cell22_3638105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 5].length) (baseStart_3638105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3638105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3638105 prefixEnd_3638105 := by exact prefixLift 3638105
  have htrace : WordTrace (prefixWord ++ tailWord_3638105) baseStart_3638105 baseEnd_3638105 := by
    simpa [prefixWord, tailWord_3638105, baseEnd_3638105] using wordTrace_append hprefix tailTrace_3638105
  have hstable : (prefixWord ++ tailWord_3638105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638105).length < 2 ^ (prefixWord ++ tailWord_3638105).sum := by decide
  have hdescent : baseEnd_3638105 < baseStart_3638105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638120 : List Nat := [2, 1, 4, 2, 1, 2, 2, 1, 1, 6]
def baseStart_3638120 : Nat := 118140960795 + 3638120 * 2 ^ 59
def prefixEnd_3638120 : Nat := 4983230072969 + 3 ^ 40 * 3638120 * 2
def baseEnd_3638120 : Nat := 1245402825823607381645731

theorem tailTrace_3638120 : CollatzResearch.WordTrace tailWord_3638120 prefixEnd_3638120 1245402825823607381645731 := by
  unfold tailWord_3638120
  simp only [CollatzResearch.WordTrace]
  refine ⟨66346568789860028136795907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88462091719813370849061209 66346568789860028136795907)
  ·
    refine ⟨99519853184790042205193861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66346568789860028136795907 99519853184790042205193861)
    ·
      refine ⟨18659972472148132913473849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99519853184790042205193861 18659972472148132913473849)
      ·
        refine ⟨13994979354111099685105387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18659972472148132913473849 13994979354111099685105387)
        ·
          refine ⟨20992469031166649527658081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13994979354111099685105387 20992469031166649527658081)
          ·
            refine ⟨15744351773374987145743561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20992469031166649527658081 15744351773374987145743561)
            ·
              refine ⟨11808263830031240359307671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15744351773374987145743561 11808263830031240359307671)
              ·
                refine ⟨17712395745046860538961507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11808263830031240359307671 17712395745046860538961507)
                ·
                  refine ⟨26568593617570290808442261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17712395745046860538961507 26568593617570290808442261)
                  ·
                    refine ⟨1245402825823607381645731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26568593617570290808442261 1245402825823607381645731)
                    ·
                      rfl

theorem cell22_3638120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_3638120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3638120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3638120 prefixEnd_3638120 := by exact prefixLift 3638120
  have htrace : WordTrace (prefixWord ++ tailWord_3638120) baseStart_3638120 baseEnd_3638120 := by
    simpa [prefixWord, tailWord_3638120, baseEnd_3638120] using wordTrace_append hprefix tailTrace_3638120
  have hstable : (prefixWord ++ tailWord_3638120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638120).length < 2 ^ (prefixWord ++ tailWord_3638120).sum := by decide
  have hdescent : baseEnd_3638120 < baseStart_3638120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638163 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 9]
def baseStart_3638163 : Nat := 118140960795 + 3638163 * 2 ^ 59
def prefixEnd_3638163 : Nat := 4983230072969 + 3 ^ 40 * 3638163 * 2
def baseEnd_3638163 : Nat := 415139181867456534273533

theorem tailTrace_3638163 : CollatzResearch.WordTrace tailWord_3638163 prefixEnd_3638163 415139181867456534273533 := by
  unfold tailWord_3638163
  simp only [CollatzResearch.WordTrace]
  refine ⟨132694705918564274617407143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88463137279042849744938095 132694705918564274617407143)
  ·
    refine ⟨199042058877846411926110715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132694705918564274617407143 199042058877846411926110715)
    ·
      refine ⟨298563088316769617889166073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199042058877846411926110715 298563088316769617889166073)
      ·
        refine ⟨223922316237577213416874555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298563088316769617889166073 223922316237577213416874555)
        ·
          refine ⟨335883474356365820125311833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223922316237577213416874555 335883474356365820125311833)
          ·
            refine ⟨251912605767274365093983875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335883474356365820125311833 251912605767274365093983875)
            ·
              refine ⟨377868908650911547640975813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251912605767274365093983875 377868908650911547640975813)
              ·
                refine ⟨70850420372045915182682965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 377868908650911547640975813 70850420372045915182682965)
                ·
                  refine ⟨415139181867456534273533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70850420372045915182682965 415139181867456534273533)
                  ·
                    rfl

theorem cell22_3638163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 9].length) (baseStart_3638163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3638163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3638163 prefixEnd_3638163 := by exact prefixLift 3638163
  have htrace : WordTrace (prefixWord ++ tailWord_3638163) baseStart_3638163 baseEnd_3638163 := by
    simpa [prefixWord, tailWord_3638163, baseEnd_3638163] using wordTrace_append hprefix tailTrace_3638163
  have hstable : (prefixWord ++ tailWord_3638163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638163).length < 2 ^ (prefixWord ++ tailWord_3638163).sum := by decide
  have hdescent : baseEnd_3638163 < baseStart_3638163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638197 : List Nat := [1, 3, 3, 2, 1, 1, 4, 2, 5]
def baseStart_3638197 : Nat := 118140960795 + 3638197 * 2 ^ 59
def prefixEnd_3638197 : Nat := 4983230072969 + 3 ^ 40 * 3638197 * 2
def baseEnd_3638197 : Nat := 415143061499068282490165

theorem tailTrace_3638197 : CollatzResearch.WordTrace tailWord_3638197 prefixEnd_3638197 415143061499068282490165 := by
  unfold tailWord_3638197
  simp only [CollatzResearch.WordTrace]
  refine ⟨132695946000441098424144845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88463964000294065616096563 132695946000441098424144845)
  ·
    refine ⟨49760979750165411909054317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132695946000441098424144845 49760979750165411909054317)
    ·
      refine ⟨18660367406312029465895369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49760979750165411909054317 18660367406312029465895369)
      ·
        refine ⟨13995275554734022099421527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18660367406312029465895369 13995275554734022099421527)
        ·
          refine ⟨20992913332101033149132291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13995275554734022099421527 20992913332101033149132291)
          ·
            refine ⟨31489369998151549723698437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20992913332101033149132291 31489369998151549723698437)
            ·
              refine ⟨5904256874653415573193457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31489369998151549723698437 5904256874653415573193457)
              ·
                refine ⟨4428192655990061679895093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5904256874653415573193457 4428192655990061679895093)
                ·
                  refine ⟨415143061499068282490165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4428192655990061679895093 415143061499068282490165)
                  ·
                    rfl

theorem cell22_3638197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 5].length) (baseStart_3638197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3638197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3638197 prefixEnd_3638197 := by exact prefixLift 3638197
  have htrace : WordTrace (prefixWord ++ tailWord_3638197) baseStart_3638197 baseEnd_3638197 := by
    simpa [prefixWord, tailWord_3638197, baseEnd_3638197] using wordTrace_append hprefix tailTrace_3638197
  have hstable : (prefixWord ++ tailWord_3638197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638197).length < 2 ^ (prefixWord ++ tailWord_3638197).sum := by decide
  have hdescent : baseEnd_3638197 < baseStart_3638197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638201 : List Nat := [1, 2, 1, 4, 2, 2, 4, 2, 1, 3]
def baseStart_3638201 : Nat := 118140960795 + 3638201 * 2 ^ 59
def prefixEnd_3638201 : Nat := 4983230072969 + 3 ^ 40 * 3638201 * 2
def baseEnd_3638201 : Nat := 1245430553778950170370483

theorem tailTrace_3638201 : CollatzResearch.WordTrace tailWord_3638201 prefixEnd_3638201 1245430553778950170370483 := by
  unfold tailWord_3638201
  simp only [CollatzResearch.WordTrace]
  refine ⟨132696091892426607107290457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88464061261617738071526971 132696091892426607107290457)
  ·
    refine ⟨99522068919319955330467843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132696091892426607107290457 99522068919319955330467843)
    ·
      refine ⟨149283103378979932995701765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99522068919319955330467843 149283103378979932995701765)
      ·
        refine ⟨27990581883558737436694081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149283103378979932995701765 27990581883558737436694081)
        ·
          refine ⟨20992936412669053077520561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27990581883558737436694081 20992936412669053077520561)
          ·
            refine ⟨15744702309501789808140421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20992936412669053077520561 15744702309501789808140421)
            ·
              refine ⟨2952131683031585589026329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15744702309501789808140421 2952131683031585589026329)
              ·
                refine ⟨2214098762273689191769747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2952131683031585589026329 2214098762273689191769747)
                ·
                  refine ⟨3321148143410533787654621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2214098762273689191769747 3321148143410533787654621)
                  ·
                    refine ⟨1245430553778950170370483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3321148143410533787654621 1245430553778950170370483)
                    ·
                      rfl

theorem cell22_3638201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2, 1, 3].length) (baseStart_3638201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3638201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3638201 prefixEnd_3638201 := by exact prefixLift 3638201
  have htrace : WordTrace (prefixWord ++ tailWord_3638201) baseStart_3638201 baseEnd_3638201 := by
    simpa [prefixWord, tailWord_3638201, baseEnd_3638201] using wordTrace_append hprefix tailTrace_3638201
  have hstable : (prefixWord ++ tailWord_3638201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638201).length < 2 ^ (prefixWord ++ tailWord_3638201).sum := by decide
  have hdescent : baseEnd_3638201 < baseStart_3638201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638225 : List Nat := [1, 2, 2, 1, 2, 1, 5, 2, 6]
def baseStart_3638225 : Nat := 118140960795 + 3638225 * 2 ^ 59
def prefixEnd_3638225 : Nat := 4983230072969 + 3 ^ 40 * 3638225 * 2
def baseEnd_3638225 : Nat := 415146256489807369256803

theorem tailTrace_3638225 : CollatzResearch.WordTrace tailWord_3638225 prefixEnd_3638225 415146256489807369256803 := by
  unfold tailWord_3638225
  simp only [CollatzResearch.WordTrace]
  refine ⟨132696967244339659206164129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88464644829559772804109419 132696967244339659206164129)
  ·
    refine ⟨99522725433254744404623097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132696967244339659206164129 99522725433254744404623097)
    ·
      refine ⟨74642044074941058303467323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99522725433254744404623097 74642044074941058303467323)
      ·
        refine ⟨111963066112411587455200985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74642044074941058303467323 111963066112411587455200985)
        ·
          refine ⟨83972299584308690591400739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111963066112411587455200985 83972299584308690591400739)
          ·
            refine ⟨125958449376463035887101109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83972299584308690591400739 125958449376463035887101109)
            ·
              refine ⟨11808604629043409614415729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125958449376463035887101109 11808604629043409614415729)
              ·
                refine ⟨8856453471782557210811797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11808604629043409614415729 8856453471782557210811797)
                ·
                  refine ⟨415146256489807369256803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8856453471782557210811797 415146256489807369256803)
                  ·
                    rfl

theorem cell22_3638225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 6].length) (baseStart_3638225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3638225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3638225 prefixEnd_3638225 := by exact prefixLift 3638225
  have htrace : WordTrace (prefixWord ++ tailWord_3638225) baseStart_3638225 baseEnd_3638225 := by
    simpa [prefixWord, tailWord_3638225, baseEnd_3638225] using wordTrace_append hprefix tailTrace_3638225
  have hstable : (prefixWord ++ tailWord_3638225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638225).length < 2 ^ (prefixWord ++ tailWord_3638225).sum := by decide
  have hdescent : baseEnd_3638225 < baseStart_3638225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638304 : List Nat := [2, 1, 1, 7, 1, 2, 8]
def baseStart_3638304 : Nat := 118140960795 + 3638304 * 2 ^ 59
def prefixEnd_3638304 : Nat := 4983230072969 + 3 ^ 40 * 3638304 * 2
def baseEnd_3638304 : Nat := 46128363436440453149821

theorem tailTrace_3638304 : CollatzResearch.WordTrace tailWord_3638304 prefixEnd_3638304 46128363436440453149821 := by
  unfold tailWord_3638304
  simp only [CollatzResearch.WordTrace]
  refine ⟨66349924305526727849144983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88466565740702303798859977 66349924305526727849144983)
  ·
    refine ⟨99524886458290091773717475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66349924305526727849144983 99524886458290091773717475)
    ·
      refine ⟨149287329687435137660576213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99524886458290091773717475 149287329687435137660576213)
      ·
        refine ⟨3498921789549261038919755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 149287329687435137660576213 3498921789549261038919755)
        ·
          refine ⟨5248382684323891558379633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3498921789549261038919755 5248382684323891558379633)
          ·
            refine ⟨3936287013242918668784725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5248382684323891558379633 3936287013242918668784725)
            ·
              refine ⟨46128363436440453149821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3936287013242918668784725 46128363436440453149821)
              ·
                rfl

theorem cell22_3638304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 8].length) (baseStart_3638304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3638304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3638304 prefixEnd_3638304 := by exact prefixLift 3638304
  have htrace : WordTrace (prefixWord ++ tailWord_3638304) baseStart_3638304 baseEnd_3638304 := by
    simpa [prefixWord, tailWord_3638304, baseEnd_3638304] using wordTrace_append hprefix tailTrace_3638304
  have hstable : (prefixWord ++ tailWord_3638304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638304).length < 2 ^ (prefixWord ++ tailWord_3638304).sum := by decide
  have hdescent : baseEnd_3638304 < baseStart_3638304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638315 : List Nat := [1, 1, 1, 1, 2, 1, 5, 3, 7]
def baseStart_3638315 : Nat := 118140960795 + 3638315 * 2 ^ 59
def prefixEnd_3638315 : Nat := 4983230072969 + 3 ^ 40 * 3638315 * 2
def baseEnd_3638315 : Nat := 415156526102897291006711

theorem tailTrace_3638315 : CollatzResearch.WordTrace tailWord_3638315 prefixEnd_3638315 415156526102897291006711 := by
  unfold tailWord_3638315
  simp only [CollatzResearch.WordTrace]
  refine ⟨132700249814013604576940399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88466833209342403051293599 132700249814013604576940399)
  ·
    refine ⟨199050374721020406865410599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132700249814013604576940399 199050374721020406865410599)
    ·
      refine ⟨298575562081530610298115899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199050374721020406865410599 298575562081530610298115899)
      ·
        refine ⟨447863343122295915447173849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298575562081530610298115899 447863343122295915447173849)
        ·
          refine ⟨335897507341721936585380387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447863343122295915447173849 335897507341721936585380387)
          ·
            refine ⟨503846261012582904878070581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335897507341721936585380387 503846261012582904878070581)
            ·
              refine ⟨47235586969929647332319117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 503846261012582904878070581 47235586969929647332319117)
              ·
                refine ⟨17713345113723617749619669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47235586969929647332319117 17713345113723617749619669)
                ·
                  refine ⟨415156526102897291006711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17713345113723617749619669 415156526102897291006711)
                  ·
                    rfl

theorem cell22_3638315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 7].length) (baseStart_3638315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3638315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3638315 prefixEnd_3638315 := by exact prefixLift 3638315
  have htrace : WordTrace (prefixWord ++ tailWord_3638315) baseStart_3638315 baseEnd_3638315 := by
    simpa [prefixWord, tailWord_3638315, baseEnd_3638315] using wordTrace_append hprefix tailTrace_3638315
  have hstable : (prefixWord ++ tailWord_3638315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638315).length < 2 ^ (prefixWord ++ tailWord_3638315).sum := by decide
  have hdescent : baseEnd_3638315 < baseStart_3638315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638370 : List Nat := [3, 3, 2, 2, 1, 1, 4, 2, 1, 3]
def baseStart_3638370 : Nat := 118140960795 + 3638370 * 2 ^ 59
def prefixEnd_3638370 : Nat := 4983230072969 + 3 ^ 40 * 3638370 * 2
def baseEnd_3638370 : Nat := 1245488405932690062894965

theorem tailTrace_3638370 : CollatzResearch.WordTrace tailWord_3638370 prefixEnd_3638370 1245488405932690062894965 := by
  unfold tailWord_3638370
  simp only [CollatzResearch.WordTrace]
  refine ⟨33175563957203587242548141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88468170552542899313461709 33175563957203587242548141)
  ·
    refine ⟨12440836483951345215955553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33175563957203587242548141 12440836483951345215955553)
    ·
      refine ⟨9330627362963508911966665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12440836483951345215955553 9330627362963508911966665)
      ·
        refine ⟨6997970522222631683974999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9330627362963508911966665 6997970522222631683974999)
        ·
          refine ⟨10496955783333947525962499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6997970522222631683974999 10496955783333947525962499)
          ·
            refine ⟨15745433675000921288943749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10496955783333947525962499 15745433675000921288943749)
            ·
              refine ⟨2952268814062672741676953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15745433675000921288943749 2952268814062672741676953)
              ·
                refine ⟨2214201610547004556257715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2952268814062672741676953 2214201610547004556257715)
                ·
                  refine ⟨3321302415820506834386573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2214201610547004556257715 3321302415820506834386573)
                  ·
                    refine ⟨1245488405932690062894965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3321302415820506834386573 1245488405932690062894965)
                    ·
                      rfl

theorem cell22_3638370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_3638370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3638370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3638370 prefixEnd_3638370 := by exact prefixLift 3638370
  have htrace : WordTrace (prefixWord ++ tailWord_3638370) baseStart_3638370 baseEnd_3638370 := by
    simpa [prefixWord, tailWord_3638370, baseEnd_3638370] using wordTrace_append hprefix tailTrace_3638370
  have hstable : (prefixWord ++ tailWord_3638370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638370).length < 2 ^ (prefixWord ++ tailWord_3638370).sum := by decide
  have hdescent : baseEnd_3638370 < baseStart_3638370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638392 : List Nat := [2, 1, 2, 1, 1, 1, 5, 3, 1, 5]
def baseStart_3638392 : Nat := 118140960795 + 3638392 * 2 ^ 59
def prefixEnd_3638392 : Nat := 4983230072969 + 3 ^ 40 * 3638392 * 2
def baseEnd_3638392 : Nat := 1245495936982289338844897

theorem tailTrace_3638392 : CollatzResearch.WordTrace tailWord_3638392 prefixEnd_3638392 1245495936982289338844897 := by
  unfold tailWord_3638392
  simp only [CollatzResearch.WordTrace]
  refine ⟨66351529117367323363746715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88468705489823097818328953 66351529117367323363746715)
  ·
    refine ⟨99527293676050985045620073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66351529117367323363746715 99527293676050985045620073)
    ·
      refine ⟨74645470257038238784215055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99527293676050985045620073 74645470257038238784215055)
      ·
        refine ⟨111968205385557358176322583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74645470257038238784215055 111968205385557358176322583)
        ·
          refine ⟨167952308078336037264483875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111968205385557358176322583 167952308078336037264483875)
          ·
            refine ⟨251928462117504055896725813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167952308078336037264483875 251928462117504055896725813)
            ·
              refine ⟨23618293323516005240318045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 251928462117504055896725813 23618293323516005240318045)
              ·
                refine ⟨8856859996318501965119267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23618293323516005240318045 8856859996318501965119267)
                ·
                  refine ⟨13285289994477752947678901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8856859996318501965119267 13285289994477752947678901)
                  ·
                    refine ⟨1245495936982289338844897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13285289994477752947678901 1245495936982289338844897)
                    ·
                      rfl

theorem cell22_3638392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_3638392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3638392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3638392 prefixEnd_3638392 := by exact prefixLift 3638392
  have htrace : WordTrace (prefixWord ++ tailWord_3638392) baseStart_3638392 baseEnd_3638392 := by
    simpa [prefixWord, tailWord_3638392, baseEnd_3638392] using wordTrace_append hprefix tailTrace_3638392
  have hstable : (prefixWord ++ tailWord_3638392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638392).length < 2 ^ (prefixWord ++ tailWord_3638392).sum := by decide
  have hdescent : baseEnd_3638392 < baseStart_3638392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638426 : List Nat := [3, 1, 1, 5, 1, 2, 1, 1, 4, 3]
def baseStart_3638426 : Nat := 118140960795 + 3638426 * 2 ^ 59
def prefixEnd_3638426 : Nat := 4983230072969 + 3 ^ 40 * 3638426 * 2
def baseEnd_3638426 : Nat := 1245507575877124583494793

theorem tailTrace_3638426 : CollatzResearch.WordTrace tailWord_3638426 prefixEnd_3638426 1245507575877124583494793 := by
  unfold tailWord_3638426
  simp only [CollatzResearch.WordTrace]
  refine ⟨33176074579152867633557783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88469532211074313689487421 33176074579152867633557783)
  ·
    refine ⟨49764111868729301450336675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33176074579152867633557783 49764111868729301450336675)
    ·
      refine ⟨74646167803093952175505013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49764111868729301450336675 74646167803093952175505013)
      ·
        refine ⟨6998078231540058016453595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74646167803093952175505013 6998078231540058016453595)
        ·
          refine ⟨10497117347310087024680393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6998078231540058016453595 10497117347310087024680393)
          ·
            refine ⟨7872838010482565268510295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10497117347310087024680393 7872838010482565268510295)
            ·
              refine ⟨11809257015723847902765443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7872838010482565268510295 11809257015723847902765443)
              ·
                refine ⟨17713885523585771854148165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11809257015723847902765443 17713885523585771854148165)
                ·
                  refine ⟨3321353535672332222652781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17713885523585771854148165 3321353535672332222652781)
                  ·
                    refine ⟨1245507575877124583494793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3321353535672332222652781 1245507575877124583494793)
                    ·
                      rfl

theorem cell22_3638426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 4, 3].length) (baseStart_3638426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3638426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3638426 prefixEnd_3638426 := by exact prefixLift 3638426
  have htrace : WordTrace (prefixWord ++ tailWord_3638426) baseStart_3638426 baseEnd_3638426 := by
    simpa [prefixWord, tailWord_3638426, baseEnd_3638426] using wordTrace_append hprefix tailTrace_3638426
  have hstable : (prefixWord ++ tailWord_3638426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638426).length < 2 ^ (prefixWord ++ tailWord_3638426).sum := by decide
  have hdescent : baseEnd_3638426 < baseStart_3638426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638488 : List Nat := [2, 1, 2, 2, 5, 2, 1, 1, 3, 3]
def baseStart_3638488 : Nat := 118140960795 + 3638488 * 2 ^ 59
def prefixEnd_3638488 : Nat := 4983230072969 + 3 ^ 40 * 3638488 * 2
def baseEnd_3638488 : Nat := 1245528799744177088444603

theorem tailTrace_3638488 : CollatzResearch.WordTrace tailWord_3638488 prefixEnd_3638488 1245528799744177088444603 := by
  unfold tailWord_3638488
  simp only [CollatzResearch.WordTrace]
  refine ⟨66353279821193427561494059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88471039761591236748658745 66353279821193427561494059)
  ·
    refine ⟨99529919731790141342241089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66353279821193427561494059 99529919731790141342241089)
    ·
      refine ⟨74647439798842606006680817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99529919731790141342241089 74647439798842606006680817)
      ·
        refine ⟨55985579849131954505010613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74647439798842606006680817 55985579849131954505010613)
        ·
          refine ⟨5248648110856120734844745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55985579849131954505010613 5248648110856120734844745)
          ·
            refine ⟨3936486083142090551133559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5248648110856120734844745 3936486083142090551133559)
            ·
              refine ⟨5904729124713135826700339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3936486083142090551133559 5904729124713135826700339)
              ·
                refine ⟨8857093687069703740050509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5904729124713135826700339 8857093687069703740050509)
                ·
                  refine ⟨3321410132651138902518941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8857093687069703740050509 3321410132651138902518941)
                  ·
                    refine ⟨1245528799744177088444603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3321410132651138902518941 1245528799744177088444603)
                    ·
                      rfl

theorem cell22_3638488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 3, 3].length) (baseStart_3638488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3638488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3638488 prefixEnd_3638488 := by exact prefixLift 3638488
  have htrace : WordTrace (prefixWord ++ tailWord_3638488) baseStart_3638488 baseEnd_3638488 := by
    simpa [prefixWord, tailWord_3638488, baseEnd_3638488] using wordTrace_append hprefix tailTrace_3638488
  have hstable : (prefixWord ++ tailWord_3638488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638488).length < 2 ^ (prefixWord ++ tailWord_3638488).sum := by decide
  have hdescent : baseEnd_3638488 < baseStart_3638488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638501 : List Nat := [1, 3, 1, 4, 3, 1, 1, 3, 5]
def baseStart_3638501 : Nat := 118140960795 + 3638501 * 2 ^ 59
def prefixEnd_3638501 : Nat := 4983230072969 + 3 ^ 40 * 3638501 * 2
def baseEnd_3638501 : Nat := 415177749969949795956521

theorem tailTrace_3638501 : CollatzResearch.WordTrace tailWord_3638501 prefixEnd_3638501 415177749969949795956521 := by
  unfold tailWord_3638501
  simp only [CollatzResearch.WordTrace]
  refine ⟨132707033791339758343211357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88471355860893172228807571 132707033791339758343211357)
  ·
    refine ⟨49765137671752409378704259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132707033791339758343211357 49765137671752409378704259)
    ·
      refine ⟨74647706507628614068056389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49765137671752409378704259 74647706507628614068056389)
      ·
        refine ⟨13996444970180365137760573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74647706507628614068056389 13996444970180365137760573)
        ·
          refine ⟨5248666863817636926660215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13996444970180365137760573 5248666863817636926660215)
          ·
            refine ⟨7873000295726455389990323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5248666863817636926660215 7873000295726455389990323)
            ·
              refine ⟨11809500443589683084985485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7873000295726455389990323 11809500443589683084985485)
              ·
                refine ⟨4428562666346131156869557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11809500443589683084985485 4428562666346131156869557)
                ·
                  refine ⟨415177749969949795956521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4428562666346131156869557 415177749969949795956521)
                  ·
                    rfl

theorem cell22_3638501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 5].length) (baseStart_3638501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3638501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3638501 prefixEnd_3638501 := by exact prefixLift 3638501
  have htrace : WordTrace (prefixWord ++ tailWord_3638501) baseStart_3638501 baseEnd_3638501 := by
    simpa [prefixWord, tailWord_3638501, baseEnd_3638501] using wordTrace_append hprefix tailTrace_3638501
  have hstable : (prefixWord ++ tailWord_3638501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638501).length < 2 ^ (prefixWord ++ tailWord_3638501).sum := by decide
  have hdescent : baseEnd_3638501 < baseStart_3638501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638544 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 10, 3]
def baseStart_3638544 : Nat := 118140960795 + 3638544 * 2 ^ 59
def prefixEnd_3638544 : Nat := 4983230072969 + 3 ^ 40 * 3638544 * 2
def baseEnd_3638544 : Nat := 1245547969688611609044431

theorem tailTrace_3638544 : CollatzResearch.WordTrace tailWord_3638544 prefixEnd_3638544 1245547969688611609044431 := by
  unfold tailWord_3638544
  simp only [CollatzResearch.WordTrace]
  refine ⟨66354301065091988343513343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88472401420122651124684457 66354301065091988343513343)
  ·
    refine ⟨99531451597637982515270015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66354301065091988343513343 99531451597637982515270015)
    ·
      refine ⟨149297177396456973772905023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99531451597637982515270015 149297177396456973772905023)
      ·
        refine ⟨223945766094685460659357535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149297177396456973772905023 223945766094685460659357535)
        ·
          refine ⟨335918649142028190989036303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223945766094685460659357535 335918649142028190989036303)
          ·
            refine ⟨503877973713042286483554455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335918649142028190989036303 503877973713042286483554455)
            ·
              refine ⟨755816960569563429725331683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503877973713042286483554455 755816960569563429725331683)
              ·
                refine ⟨1133725440854345144587997525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 755816960569563429725331683 1133725440854345144587997525)
                ·
                  refine ⟨3321461252502964290785149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 1133725440854345144587997525 3321461252502964290785149)
                  ·
                    refine ⟨1245547969688611609044431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3321461252502964290785149 1245547969688611609044431)
                    ·
                      rfl

theorem cell22_3638544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 10, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 10, 3].length) (baseStart_3638544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3638544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3638544 prefixEnd_3638544 := by exact prefixLift 3638544
  have htrace : WordTrace (prefixWord ++ tailWord_3638544) baseStart_3638544 baseEnd_3638544 := by
    simpa [prefixWord, tailWord_3638544, baseEnd_3638544] using wordTrace_append hprefix tailTrace_3638544
  have hstable : (prefixWord ++ tailWord_3638544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638544).length < 2 ^ (prefixWord ++ tailWord_3638544).sum := by decide
  have hdescent : baseEnd_3638544 < baseStart_3638544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638657 : List Nat := [1, 2, 4, 3, 3, 1, 1, 1, 3, 3]
def baseStart_3638657 : Nat := 118140960795 + 3638657 * 2 ^ 59
def prefixEnd_3638657 : Nat := 4983230072969 + 3 ^ 40 * 3638657 * 2
def baseEnd_3638657 : Nat := 1245586651897916980969085

theorem tailTrace_3638657 : CollatzResearch.WordTrace tailWord_3638657 prefixEnd_3638657 1245586651897916980969085 := by
  unfold tailWord_3638657
  simp only [CollatzResearch.WordTrace]
  refine ⟨132712723578774596985890225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88475149052516397990593483 132712723578774596985890225)
  ·
    refine ⟨99534542684080947739417669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132712723578774596985890225 99534542684080947739417669)
    ·
      refine ⟨18662726753265177701140813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99534542684080947739417669 18662726753265177701140813)
      ·
        refine ⟨6998522532474441637927805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18662726753265177701140813 6998522532474441637927805)
        ·
          refine ⟨2624445949677915614222927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6998522532474441637927805 2624445949677915614222927)
          ·
            refine ⟨3936668924516873421334391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2624445949677915614222927 3936668924516873421334391)
            ·
              refine ⟨5905003386775310132001587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3936668924516873421334391 5905003386775310132001587)
              ·
                refine ⟨8857505080162965198002381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5905003386775310132001587 8857505080162965198002381)
                ·
                  refine ⟨3321564405061111949250893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8857505080162965198002381 3321564405061111949250893)
                  ·
                    refine ⟨1245586651897916980969085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3321564405061111949250893 1245586651897916980969085)
                    ·
                      rfl

theorem cell22_3638657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_3638657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3638657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3638657 prefixEnd_3638657 := by exact prefixLift 3638657
  have htrace : WordTrace (prefixWord ++ tailWord_3638657) baseStart_3638657 baseEnd_3638657 := by
    simpa [prefixWord, tailWord_3638657, baseEnd_3638657] using wordTrace_append hprefix tailTrace_3638657
  have hstable : (prefixWord ++ tailWord_3638657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638657).length < 2 ^ (prefixWord ++ tailWord_3638657).sum := by decide
  have hdescent : baseEnd_3638657 < baseStart_3638657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638711 : List Nat := [1, 1, 3, 1, 3, 2, 1, 4, 2, 4]
def baseStart_3638711 : Nat := 118140960795 + 3638711 * 2 ^ 59
def prefixEnd_3638711 : Nat := 4983230072969 + 3 ^ 40 * 3638711 * 2
def baseEnd_3638711 : Nat := 1245605137201478840118919

theorem tailTrace_3638711 : CollatzResearch.WordTrace tailWord_3638711 prefixEnd_3638711 1245605137201478840118919 := by
  unfold tailWord_3638711
  simp only [CollatzResearch.WordTrace]
  refine ⟨132714693120578964208355987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88476462080385976138903991 132714693120578964208355987)
  ·
    refine ⟨199072039680868446312533981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132714693120578964208355987 199072039680868446312533981)
    ·
      refine ⟨74652014880325667367200243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199072039680868446312533981 74652014880325667367200243)
      ·
        refine ⟨111978022320488501050800365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74652014880325667367200243 111978022320488501050800365)
        ·
          refine ⟨41991758370183187894050137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111978022320488501050800365 41991758370183187894050137)
          ·
            refine ⟨31493818777637390920537603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41991758370183187894050137 31493818777637390920537603)
            ·
              refine ⟨47240728166456086380806405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31493818777637390920537603 47240728166456086380806405)
              ·
                refine ⟨8857636531210516196401201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47240728166456086380806405 8857636531210516196401201)
                ·
                  refine ⟨6643227398407887147300901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8857636531210516196401201 6643227398407887147300901)
                  ·
                    refine ⟨1245605137201478840118919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6643227398407887147300901 1245605137201478840118919)
                    ·
                      rfl

theorem cell22_3638711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_3638711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3638711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3638711 prefixEnd_3638711 := by exact prefixLift 3638711
  have htrace : WordTrace (prefixWord ++ tailWord_3638711) baseStart_3638711 baseEnd_3638711 := by
    simpa [prefixWord, tailWord_3638711, baseEnd_3638711] using wordTrace_append hprefix tailTrace_3638711
  have hstable : (prefixWord ++ tailWord_3638711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638711).length < 2 ^ (prefixWord ++ tailWord_3638711).sum := by decide
  have hdescent : baseEnd_3638711 < baseStart_3638711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638771 : List Nat := [1, 1, 1, 2, 2, 2, 2, 6, 5]
def baseStart_3638771 : Nat := 118140960795 + 3638771 * 2 ^ 59
def prefixEnd_3638771 : Nat := 4983230072969 + 3 ^ 40 * 3638771 * 2
def baseEnd_3638771 : Nat := 415208558809219561206245

theorem tailTrace_3638771 : CollatzResearch.WordTrace tailWord_3638771 prefixEnd_3638771 415208558809219561206245 := by
  unfold tailWord_3638771
  simp only [CollatzResearch.WordTrace]
  refine ⟨132716881500361594455540167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88477921000241062970360111 132716881500361594455540167)
  ·
    refine ⟨199075322250542391683310251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132716881500361594455540167 199075322250542391683310251)
    ·
      refine ⟨298612983375813587524965377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199075322250542391683310251 298612983375813587524965377)
      ·
        refine ⟨223959737531860190643724033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298612983375813587524965377 223959737531860190643724033)
        ·
          refine ⟨167969803148895142982793025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223959737531860190643724033 167969803148895142982793025)
          ·
            refine ⟨125977352361671357237094769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167969803148895142982793025 125977352361671357237094769)
            ·
              refine ⟨94483014271253517927821077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125977352361671357237094769 94483014271253517927821077)
              ·
                refine ⟨4428891293965008652866613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94483014271253517927821077 4428891293965008652866613)
                ·
                  refine ⟨415208558809219561206245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4428891293965008652866613 415208558809219561206245)
                  ·
                    rfl

theorem cell22_3638771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 5].length) (baseStart_3638771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3638771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3638771 prefixEnd_3638771 := by exact prefixLift 3638771
  have htrace : WordTrace (prefixWord ++ tailWord_3638771) baseStart_3638771 baseEnd_3638771 := by
    simpa [prefixWord, tailWord_3638771, baseEnd_3638771] using wordTrace_append hprefix tailTrace_3638771
  have hstable : (prefixWord ++ tailWord_3638771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638771).length < 2 ^ (prefixWord ++ tailWord_3638771).sum := by decide
  have hdescent : baseEnd_3638771 < baseStart_3638771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638940 : List Nat := [2, 2, 3, 2, 3, 1, 1, 1, 7]
def baseStart_3638940 : Nat := 118140960795 + 3638940 * 2 ^ 59
def prefixEnd_3638940 : Nat := 4983230072969 + 3 ^ 40 * 3638940 * 2
def baseEnd_3638940 : Nat := 415227842860466192047739

theorem tailTrace_3638940 : CollatzResearch.WordTrace tailWord_3638940 prefixEnd_3638940 415227842860466192047739 := by
  unfold tailWord_3638940
  simp only [CollatzResearch.WordTrace]
  refine ⟨66361522718374668159221137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88482030291166224212294849 66361522718374668159221137)
  ·
    refine ⟨49771142038781001119415853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66361522718374668159221137 49771142038781001119415853)
    ·
      refine ⟨18664178264542875419780945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49771142038781001119415853 18664178264542875419780945)
      ·
        refine ⟨13998133698407156564835709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18664178264542875419780945 13998133698407156564835709)
        ·
          refine ⟨5249300136902683711813391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13998133698407156564835709 5249300136902683711813391)
          ·
            refine ⟨7873950205354025567720087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5249300136902683711813391 7873950205354025567720087)
            ·
              refine ⟨11810925308031038351580131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7873950205354025567720087 11810925308031038351580131)
              ·
                refine ⟨17716387962046557527370197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11810925308031038351580131 17716387962046557527370197)
                ·
                  refine ⟨415227842860466192047739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17716387962046557527370197 415227842860466192047739)
                  ·
                    rfl

theorem cell22_3638940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 7].length) (baseStart_3638940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3638940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3638940 prefixEnd_3638940 := by exact prefixLift 3638940
  have htrace : WordTrace (prefixWord ++ tailWord_3638940) baseStart_3638940 baseEnd_3638940 := by
    simpa [prefixWord, tailWord_3638940, baseEnd_3638940] using wordTrace_append hprefix tailTrace_3638940
  have hstable : (prefixWord ++ tailWord_3638940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638940).length < 2 ^ (prefixWord ++ tailWord_3638940).sum := by decide
  have hdescent : baseEnd_3638940 < baseStart_3638940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638957 : List Nat := [1, 5, 2, 1, 1, 1, 5, 1, 5]
def baseStart_3638957 : Nat := 118140960795 + 3638957 * 2 ^ 59
def prefixEnd_3638957 : Nat := 4983230072969 + 3 ^ 40 * 3638957 * 2
def baseEnd_3638957 : Nat := 415229782676272066156055

theorem tailTrace_3638957 : CollatzResearch.WordTrace tailWord_3638957 prefixEnd_3638957 415229782676272066156055 := by
  unfold tailWord_3638957
  simp only [CollatzResearch.WordTrace]
  refine ⟨132723665477687748221811125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88482443651791832147874083 132723665477687748221811125)
  ·
    refine ⟨12442843638533226395794793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132723665477687748221811125 12442843638533226395794793)
    ·
      refine ⟨9332132728899919796846095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12442843638533226395794793 9332132728899919796846095)
      ·
        refine ⟨13998199093349879695269143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9332132728899919796846095 13998199093349879695269143)
        ·
          refine ⟨20997298640024819542903715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13998199093349879695269143 20997298640024819542903715)
          ·
            refine ⟨31495947960037229314355573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20997298640024819542903715 31495947960037229314355573)
            ·
              refine ⟨2952745121253490248220835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31495947960037229314355573 2952745121253490248220835)
              ·
                refine ⟨4429117681880235372331253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2952745121253490248220835 4429117681880235372331253)
                ·
                  refine ⟨415229782676272066156055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4429117681880235372331253 415229782676272066156055)
                  ·
                    rfl

theorem cell22_3638957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_3638957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3638957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3638957 prefixEnd_3638957 := by exact prefixLift 3638957
  have htrace : WordTrace (prefixWord ++ tailWord_3638957) baseStart_3638957 baseEnd_3638957 := by
    simpa [prefixWord, tailWord_3638957, baseEnd_3638957] using wordTrace_append hprefix tailTrace_3638957
  have hstable : (prefixWord ++ tailWord_3638957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638957).length < 2 ^ (prefixWord ++ tailWord_3638957).sum := by decide
  have hdescent : baseEnd_3638957 < baseStart_3638957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638970 : List Nat := [3, 1, 1, 1, 2, 4, 1, 4, 1, 4]
def baseStart_3638970 : Nat := 118140960795 + 3638970 * 2 ^ 59
def prefixEnd_3638970 : Nat := 4983230072969 + 3 ^ 40 * 3638970 * 2
def baseEnd_3638970 : Nat := 1245693798194488497893125

theorem tailTrace_3638970 : CollatzResearch.WordTrace tailWord_3638970 prefixEnd_3638970 1245693798194488497893125 := by
  unfold tailWord_3638970
  simp only [CollatzResearch.WordTrace]
  refine ⟨33181034906660162860508591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88482759751093767628022909 33181034906660162860508591)
  ·
    refine ⟨49771552359990244290762887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33181034906660162860508591 49771552359990244290762887)
    ·
      refine ⟨74657328539985366436144331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49771552359990244290762887 74657328539985366436144331)
      ·
        refine ⟨111985992809978049654216497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74657328539985366436144331 111985992809978049654216497)
        ·
          refine ⟨83989494607483537240662373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111985992809978049654216497 83989494607483537240662373)
          ·
            refine ⟨15748030238903163232624195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83989494607483537240662373 15748030238903163232624195)
            ·
              refine ⟨23622045358354744848936293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15748030238903163232624195 23622045358354744848936293)
              ·
                refine ⟨4429133504691514659175555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23622045358354744848936293 4429133504691514659175555)
                ·
                  refine ⟨6643700257037271988763333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4429133504691514659175555 6643700257037271988763333)
                  ·
                    refine ⟨1245693798194488497893125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6643700257037271988763333 1245693798194488497893125)
                    ·
                      rfl

theorem cell22_3638970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_3638970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3638970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3638970 prefixEnd_3638970 := by exact prefixLift 3638970
  have htrace : WordTrace (prefixWord ++ tailWord_3638970) baseStart_3638970 baseEnd_3638970 := by
    simpa [prefixWord, tailWord_3638970, baseEnd_3638970] using wordTrace_append hprefix tailTrace_3638970
  have hstable : (prefixWord ++ tailWord_3638970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638970).length < 2 ^ (prefixWord ++ tailWord_3638970).sum := by decide
  have hdescent : baseEnd_3638970 < baseStart_3638970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638983 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 3, 5]
def baseStart_3638983 : Nat := 118140960795 + 3638983 * 2 ^ 59
def prefixEnd_3638983 : Nat := 4983230072969 + 3 ^ 40 * 3638983 * 2
def baseEnd_3638983 : Nat := 1245698248360160797318085

theorem tailTrace_3638983 : CollatzResearch.WordTrace tailWord_3638983 prefixEnd_3638983 1245698248360160797318085 := by
  unfold tailWord_3638983
  simp only [CollatzResearch.WordTrace]
  refine ⟨132724613775593554662257603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88483075850395703108171735 132724613775593554662257603)
  ·
    refine ⟨199086920663390331993386405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132724613775593554662257603 199086920663390331993386405)
    ·
      refine ⟨37328797624385687248759951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199086920663390331993386405 37328797624385687248759951)
      ·
        refine ⟨55993196436578530873139927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37328797624385687248759951 55993196436578530873139927)
        ·
          refine ⟨83989794654867796309709891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55993196436578530873139927 83989794654867796309709891)
          ·
            refine ⟨125984691982301694464564837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83989794654867796309709891 125984691982301694464564837)
            ·
              refine ⟨23622129746681567712105907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125984691982301694464564837 23622129746681567712105907)
              ·
                refine ⟨35433194620022351568158861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23622129746681567712105907 35433194620022351568158861)
                ·
                  refine ⟨13287447982508381838059573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35433194620022351568158861 13287447982508381838059573)
                  ·
                    refine ⟨1245698248360160797318085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13287447982508381838059573 1245698248360160797318085)
                    ·
                      rfl

theorem cell22_3638983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_3638983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3638983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3638983 prefixEnd_3638983 := by exact prefixLift 3638983
  have htrace : WordTrace (prefixWord ++ tailWord_3638983) baseStart_3638983 baseEnd_3638983 := by
    simpa [prefixWord, tailWord_3638983, baseEnd_3638983] using wordTrace_append hprefix tailTrace_3638983
  have hstable : (prefixWord ++ tailWord_3638983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638983).length < 2 ^ (prefixWord ++ tailWord_3638983).sum := by decide
  have hdescent : baseEnd_3638983 < baseStart_3638983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639000 : List Nat := [2, 1, 2, 2, 3, 1, 1, 3, 4, 3]
def baseStart_3639000 : Nat := 118140960795 + 3639000 * 2 ^ 59
def prefixEnd_3639000 : Nat := 4983230072969 + 3 ^ 40 * 3639000 * 2
def baseEnd_3639000 : Nat := 1245704067807578419643033

theorem tailTrace_3639000 : CollatzResearch.WordTrace tailWord_3639000 prefixEnd_3639000 1245704067807578419643033 := by
  unfold tailWord_3639000
  simp only [CollatzResearch.WordTrace]
  refine ⟨66362616908265983282813227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88483489211021311043750969 66362616908265983282813227)
  ·
    refine ⟨99543925362398974924219841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66362616908265983282813227 99543925362398974924219841)
    ·
      refine ⟨74657944021799231193164881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99543925362398974924219841 74657944021799231193164881)
      ·
        refine ⟨55993458016349423394873661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74657944021799231193164881 55993458016349423394873661)
        ·
          refine ⟨20997546756131033773077623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55993458016349423394873661 20997546756131033773077623)
          ·
            refine ⟨31496320134196550659616435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20997546756131033773077623 31496320134196550659616435)
            ·
              refine ⟨47244480201294825989424653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31496320134196550659616435 47244480201294825989424653)
              ·
                refine ⟨17716680075485559746034245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47244480201294825989424653 17716680075485559746034245)
                ·
                  refine ⟨3321877514153542452381421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17716680075485559746034245 3321877514153542452381421)
                  ·
                    refine ⟨1245704067807578419643033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3321877514153542452381421 1245704067807578419643033)
                    ·
                      rfl

theorem cell22_3639000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 4, 3].length) (baseStart_3639000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639000 prefixEnd_3639000 := by exact prefixLift 3639000
  have htrace : WordTrace (prefixWord ++ tailWord_3639000) baseStart_3639000 baseEnd_3639000 := by
    simpa [prefixWord, tailWord_3639000, baseEnd_3639000] using wordTrace_append hprefix tailTrace_3639000
  have hstable : (prefixWord ++ tailWord_3639000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639000).length < 2 ^ (prefixWord ++ tailWord_3639000).sum := by decide
  have hdescent : baseEnd_3639000 < baseStart_3639000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639030 : List Nat := [5, 1, 1, 1, 1, 3, 2, 8]
def baseStart_3639030 : Nat := 118140960795 + 3639030 * 2 ^ 59
def prefixEnd_3639030 : Nat := 4983230072969 + 3 ^ 40 * 3639030 * 2
def baseEnd_3639030 : Nat := 138412704157852037932549

theorem tailTrace_3639030 : CollatzResearch.WordTrace tailWord_3639030 prefixEnd_3639030 138412704157852037932549 := by
  unfold tailWord_3639030
  simp only [CollatzResearch.WordTrace]
  refine ⟨8295395500401455105576159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88484218670948854459479029 8295395500401455105576159)
  ·
    refine ⟨12443093250602182658364239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8295395500401455105576159 12443093250602182658364239)
    ·
      refine ⟨18664639875903273987546359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12443093250602182658364239 18664639875903273987546359)
      ·
        refine ⟨27996959813854910981319539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18664639875903273987546359 27996959813854910981319539)
        ·
          refine ⟨41995439720782366471979309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27996959813854910981319539 41995439720782366471979309)
          ·
            refine ⟨15748289895293387426992241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41995439720782366471979309 15748289895293387426992241)
            ·
              refine ⟨11811217421470040570244181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15748289895293387426992241 11811217421470040570244181)
              ·
                refine ⟨138412704157852037932549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11811217421470040570244181 138412704157852037932549)
                ·
                  rfl

theorem cell22_3639030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_3639030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639030 prefixEnd_3639030 := by exact prefixLift 3639030
  have htrace : WordTrace (prefixWord ++ tailWord_3639030) baseStart_3639030 baseEnd_3639030 := by
    simpa [prefixWord, tailWord_3639030, baseEnd_3639030] using wordTrace_append hprefix tailTrace_3639030
  have hstable : (prefixWord ++ tailWord_3639030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639030).length < 2 ^ (prefixWord ++ tailWord_3639030).sum := by decide
  have hdescent : baseEnd_3639030 < baseStart_3639030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639046 : List Nat := [6, 2, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_3639046 : Nat := 118140960795 + 3639046 * 2 ^ 59
def prefixEnd_3639046 : Nat := 4983230072969 + 3 ^ 40 * 3639046 * 2
def baseEnd_3639046 : Nat := 1245719814547649632992893

theorem tailTrace_3639046 : CollatzResearch.WordTrace tailWord_3639046 prefixEnd_3639046 1245719814547649632992893 := by
  unfold tailWord_3639046
  simp only [CollatzResearch.WordTrace]
  refine ⟨4147715986698916138181281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 88484607716243544281200661 4147715986698916138181281)
  ·
    refine ⟨3110786990024187103635961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4147715986698916138181281 3110786990024187103635961)
    ·
      refine ⟨2333090242518140327726971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3110786990024187103635961 2333090242518140327726971)
      ·
        refine ⟨3499635363777210491590457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2333090242518140327726971 3499635363777210491590457)
        ·
          refine ⟨2624726522832907868692843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3499635363777210491590457 2624726522832907868692843)
          ·
            refine ⟨3937089784249361803039265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2624726522832907868692843 3937089784249361803039265)
            ·
              refine ⟨2952817338187021352279449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3937089784249361803039265 2952817338187021352279449)
              ·
                refine ⟨2214613003640266014209587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2952817338187021352279449 2214613003640266014209587)
                ·
                  refine ⟨3321919505460399021314381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2214613003640266014209587 3321919505460399021314381)
                  ·
                    refine ⟨1245719814547649632992893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3321919505460399021314381 1245719814547649632992893)
                    ·
                      rfl

theorem cell22_3639046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_3639046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639046 prefixEnd_3639046 := by exact prefixLift 3639046
  have htrace : WordTrace (prefixWord ++ tailWord_3639046) baseStart_3639046 baseEnd_3639046 := by
    simpa [prefixWord, tailWord_3639046, baseEnd_3639046] using wordTrace_append hprefix tailTrace_3639046
  have hstable : (prefixWord ++ tailWord_3639046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639046).length < 2 ^ (prefixWord ++ tailWord_3639046).sum := by decide
  have hdescent : baseEnd_3639046 < baseStart_3639046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
