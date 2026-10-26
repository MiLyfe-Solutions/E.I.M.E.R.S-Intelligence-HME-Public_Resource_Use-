import V185TrunkScan23Chunk0131

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_782151 : List Nat := [1, 1, 4, 1, 2, 1, 4, 3, 1, 1, 4]
def baseStart_782151 : Nat := 118140960795 + 782151 * 2 ^ 59
def prefixEnd_782151 : Nat := 4983230072969 + 3 ^ 40 * 782151 * 2
def baseEnd_782151 : Nat := 401619407394874564315459

theorem tailTrace_782151 : CollatzResearch.WordTrace tailWord_782151 prefixEnd_782151 401619407394874564315459 := by
  unfold tailWord_782151
  simp only [CollatzResearch.WordTrace]
  refine ⟨28527390589407982601002307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19018260392938655067334871 28527390589407982601002307)
  ·
    refine ⟨42791085884111973901503461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28527390589407982601002307 42791085884111973901503461)
    ·
      refine ⟨8023328603270995106531899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42791085884111973901503461 8023328603270995106531899)
      ·
        refine ⟨12034992904906492659797849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8023328603270995106531899 12034992904906492659797849)
        ·
          refine ⟨9026244678679869494848387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12034992904906492659797849 9026244678679869494848387)
          ·
            refine ⟨13539367018019804242272581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9026244678679869494848387 13539367018019804242272581)
            ·
              refine ⟨2538631315878713295426109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13539367018019804242272581 2538631315878713295426109)
              ·
                refine ⟨951986743454517485784791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2538631315878713295426109 951986743454517485784791)
                ·
                  refine ⟨1427980115181776228677187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 951986743454517485784791 1427980115181776228677187)
                  ·
                    refine ⟨2141970172772664343015781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1427980115181776228677187 2141970172772664343015781)
                    ·
                      refine ⟨401619407394874564315459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2141970172772664343015781 401619407394874564315459)
                      ·
                        rfl

theorem cell23_782151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_782151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782151 prefixEnd_782151 := by exact prefixLift 782151
  have htrace : WordTrace (prefixWord ++ tailWord_782151) baseStart_782151 baseEnd_782151 := by
    simpa [prefixWord, tailWord_782151, baseEnd_782151] using wordTrace_append hprefix tailTrace_782151
  have hstable : (prefixWord ++ tailWord_782151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782151).length < 2 ^ (prefixWord ++ tailWord_782151).sum := by decide
  have hdescent : baseEnd_782151 < baseStart_782151 := by decide
  rcases family_descends (prefixWord ++ tailWord_782151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782161 : List Nat := [1, 2, 2, 1, 5, 1, 2, 1, 4, 4]
def baseStart_782161 : Nat := 118140960795 + 782161 * 2 ^ 59
def prefixEnd_782161 : Nat := 4983230072969 + 3 ^ 40 * 782161 * 2
def baseEnd_782161 : Nat := 133874847400473175063471

theorem tailTrace_782161 : CollatzResearch.WordTrace tailWord_782161 prefixEnd_782161 133874847400473175063471 := by
  unfold tailWord_782161
  simp only [CollatzResearch.WordTrace]
  refine ⟨28527755319371754308866337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19018503546247836205910891 28527755319371754308866337)
  ·
    refine ⟨21395816489528815731649753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28527755319371754308866337 21395816489528815731649753)
    ·
      refine ⟨16046862367146611798737315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21395816489528815731649753 16046862367146611798737315)
      ·
        refine ⟨24070293550719917698105973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16046862367146611798737315 24070293550719917698105973)
        ·
          refine ⟨2256590020379992284197435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24070293550719917698105973 2256590020379992284197435)
          ·
            refine ⟨3384885030569988426296153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2256590020379992284197435 3384885030569988426296153)
            ·
              refine ⟨2538663772927491319722115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3384885030569988426296153 2538663772927491319722115)
              ·
                refine ⟨3807995659391236979583173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2538663772927491319722115 3807995659391236979583173)
                ·
                  refine ⟨713999186135856933671845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3807995659391236979583173 713999186135856933671845)
                  ·
                    refine ⟨133874847400473175063471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 713999186135856933671845 133874847400473175063471)
                    ·
                      rfl

theorem cell23_782161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4, 4].length) (baseStart_782161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782161 prefixEnd_782161 := by exact prefixLift 782161
  have htrace : WordTrace (prefixWord ++ tailWord_782161) baseStart_782161 baseEnd_782161 := by
    simpa [prefixWord, tailWord_782161, baseEnd_782161] using wordTrace_append hprefix tailTrace_782161
  have hstable : (prefixWord ++ tailWord_782161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782161).length < 2 ^ (prefixWord ++ tailWord_782161).sum := by decide
  have hdescent : baseEnd_782161 < baseStart_782161 := by decide
  rcases family_descends (prefixWord ++ tailWord_782161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782162 : List Nat := [3, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3]
def baseStart_782162 : Nat := 118140960795 + 782162 * 2 ^ 59
def prefixEnd_782162 : Nat := 4983230072969 + 3 ^ 40 * 782162 * 2
def baseEnd_782162 : Nat := 401625055682074021277909

theorem tailTrace_782162 : CollatzResearch.WordTrace tailWord_782162 prefixEnd_782162 401625055682074021277909 := by
  unfold tailWord_782162
  simp only [CollatzResearch.WordTrace]
  refine ⟨7131947948092032869913185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19018527861578754319768493 7131947948092032869913185)
  ·
    refine ⟨5348960961069024652434889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7131947948092032869913185 5348960961069024652434889)
    ·
      refine ⟨4011720720801768489326167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5348960961069024652434889 4011720720801768489326167)
      ·
        refine ⟨6017581081202652733989251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4011720720801768489326167 6017581081202652733989251)
        ·
          refine ⟨9026371621803979100983877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6017581081202652733989251 9026371621803979100983877)
          ·
            refine ⟨1692444679088246081434477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9026371621803979100983877 1692444679088246081434477)
            ·
              refine ⟨634666754658092280537929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1692444679088246081434477 634666754658092280537929)
              ·
                refine ⟨476000065993569210403447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 634666754658092280537929 476000065993569210403447)
                ·
                  refine ⟨714000098990353815605171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 476000065993569210403447 714000098990353815605171)
                  ·
                    refine ⟨1071000148485530723407757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 714000098990353815605171 1071000148485530723407757)
                    ·
                      refine ⟨401625055682074021277909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1071000148485530723407757 401625055682074021277909)
                      ·
                        rfl

theorem cell23_782162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_782162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782162 prefixEnd_782162 := by exact prefixLift 782162
  have htrace : WordTrace (prefixWord ++ tailWord_782162) baseStart_782162 baseEnd_782162 := by
    simpa [prefixWord, tailWord_782162, baseEnd_782162] using wordTrace_append hprefix tailTrace_782162
  have hstable : (prefixWord ++ tailWord_782162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782162).length < 2 ^ (prefixWord ++ tailWord_782162).sum := by decide
  have hdescent : baseEnd_782162 < baseStart_782162 := by decide
  rcases family_descends (prefixWord ++ tailWord_782162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782188 : List Nat := [2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 3]
def baseStart_782188 : Nat := 118140960795 + 782188 * 2 ^ 59
def prefixEnd_782188 : Nat := 4983230072969 + 3 ^ 40 * 782188 * 2
def baseEnd_782188 : Nat := 401638406179090919552789

theorem tailTrace_782188 : CollatzResearch.WordTrace tailWord_782188 prefixEnd_782188 401638406179090919552789 := by
  unfold tailWord_782188
  simp only [CollatzResearch.WordTrace]
  refine ⟨14264370045136968960049609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19019160060182625280066145 14264370045136968960049609)
  ·
    refine ⟨10698277533852726720037207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14264370045136968960049609 10698277533852726720037207)
    ·
      refine ⟨16047416300779090080055811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10698277533852726720037207 16047416300779090080055811)
      ·
        refine ⟨24071124451168635120083717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16047416300779090080055811 24071124451168635120083717)
        ·
          refine ⟨4513335834594119085015697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24071124451168635120083717 4513335834594119085015697)
          ·
            refine ⟨3385001875945589313761773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4513335834594119085015697 3385001875945589313761773)
            ·
              refine ⟨1269375703479595992660665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3385001875945589313761773 1269375703479595992660665)
              ·
                refine ⟨952031777609696994495499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1269375703479595992660665 952031777609696994495499)
                ·
                  refine ⟨1428047666414545491743249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 952031777609696994495499 1428047666414545491743249)
                  ·
                    refine ⟨1071035749810909118807437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1428047666414545491743249 1071035749810909118807437)
                    ·
                      refine ⟨401638406179090919552789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1071035749810909118807437 401638406179090919552789)
                      ·
                        rfl

theorem cell23_782188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 3].length) (baseStart_782188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782188 prefixEnd_782188 := by exact prefixLift 782188
  have htrace : WordTrace (prefixWord ++ tailWord_782188) baseStart_782188 baseEnd_782188 := by
    simpa [prefixWord, tailWord_782188, baseEnd_782188] using wordTrace_append hprefix tailTrace_782188
  have hstable : (prefixWord ++ tailWord_782188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782188).length < 2 ^ (prefixWord ++ tailWord_782188).sum := by decide
  have hdescent : baseEnd_782188 < baseStart_782188 := by decide
  rcases family_descends (prefixWord ++ tailWord_782188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782201 : List Nat := [1, 2, 1, 3, 2, 2, 3, 2, 1, 3, 3]
def baseStart_782201 : Nat := 118140960795 + 782201 * 2 ^ 59
def prefixEnd_782201 : Nat := 4983230072969 + 3 ^ 40 * 782201 * 2
def baseEnd_782201 : Nat := 401645081427599368690229

theorem tailTrace_782201 : CollatzResearch.WordTrace tailWord_782201 prefixEnd_782201 401645081427599368690229 := by
  unfold tailWord_782201
  simp only [CollatzResearch.WordTrace]
  refine ⟨28529214239226841140322457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19019476159484560760214971 28529214239226841140322457)
  ·
    refine ⟨21396910679420130855241843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28529214239226841140322457 21396910679420130855241843)
    ·
      refine ⟨32095366019130196282862765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21396910679420130855241843 32095366019130196282862765)
      ·
        refine ⟨12035762257173823606073537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32095366019130196282862765 12035762257173823606073537)
        ·
          refine ⟨9026821692880367704555153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12035762257173823606073537 9026821692880367704555153)
          ·
            refine ⟨6770116269660275778416365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9026821692880367704555153 6770116269660275778416365)
            ·
              refine ⟨2538793601122603416906137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6770116269660275778416365 2538793601122603416906137)
              ·
                refine ⟨1904095200841952562679603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2538793601122603416906137 1904095200841952562679603)
                ·
                  refine ⟨2856142801262928844019405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1904095200841952562679603 2856142801262928844019405)
                  ·
                    refine ⟨1071053550473598316507277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2856142801262928844019405 1071053550473598316507277)
                    ·
                      refine ⟨401645081427599368690229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1071053550473598316507277 401645081427599368690229)
                      ·
                        rfl

theorem cell23_782201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_782201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782201 prefixEnd_782201 := by exact prefixLift 782201
  have htrace : WordTrace (prefixWord ++ tailWord_782201) baseStart_782201 baseEnd_782201 := by
    simpa [prefixWord, tailWord_782201, baseEnd_782201] using wordTrace_append hprefix tailTrace_782201
  have hstable : (prefixWord ++ tailWord_782201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782201).length < 2 ^ (prefixWord ++ tailWord_782201).sum := by decide
  have hdescent : baseEnd_782201 < baseStart_782201 := by decide
  rcases family_descends (prefixWord ++ tailWord_782201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782224 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 4]
def baseStart_782224 : Nat := 118140960795 + 782224 * 2 ^ 59
def prefixEnd_782224 : Nat := 4983230072969 + 3 ^ 40 * 782224 * 2
def baseEnd_782224 : Nat := 401656891482652778702623

theorem tailTrace_782224 : CollatzResearch.WordTrace tailWord_782224 prefixEnd_782224 401656891482652778702623 := by
  unfold tailWord_782224
  simp only [CollatzResearch.WordTrace]
  refine ⟨14265026559071758034204863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19020035412095677378939817 14265026559071758034204863)
  ·
    refine ⟨21397539838607637051307295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14265026559071758034204863 21397539838607637051307295)
    ·
      refine ⟨32096309757911455576960943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21397539838607637051307295 32096309757911455576960943)
      ·
        refine ⟨48144464636867183365441415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32096309757911455576960943 48144464636867183365441415)
        ·
          refine ⟨72216696955300775048162123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48144464636867183365441415 72216696955300775048162123)
          ·
            refine ⟨108325045432951162572243185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72216696955300775048162123 108325045432951162572243185)
            ·
              refine ⟨81243784074713371929182389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108325045432951162572243185 81243784074713371929182389)
              ·
                refine ⟨7616604757004378618360849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81243784074713371929182389 7616604757004378618360849)
                ·
                  refine ⟨5712453567753283963770637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7616604757004378618360849 5712453567753283963770637)
                  ·
                    refine ⟨2142170087907481486413989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5712453567753283963770637 2142170087907481486413989)
                    ·
                      refine ⟨401656891482652778702623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2142170087907481486413989 401656891482652778702623)
                      ·
                        rfl

theorem cell23_782224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 4].length) (baseStart_782224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782224 prefixEnd_782224 := by exact prefixLift 782224
  have htrace : WordTrace (prefixWord ++ tailWord_782224) baseStart_782224 baseEnd_782224 := by
    simpa [prefixWord, tailWord_782224, baseEnd_782224] using wordTrace_append hprefix tailTrace_782224
  have hstable : (prefixWord ++ tailWord_782224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782224).length < 2 ^ (prefixWord ++ tailWord_782224).sum := by decide
  have hdescent : baseEnd_782224 < baseStart_782224 := by decide
  rcases family_descends (prefixWord ++ tailWord_782224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782264 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 9]
def baseStart_782264 : Nat := 118140960795 + 782264 * 2 ^ 59
def prefixEnd_782264 : Nat := 4983230072969 + 3 ^ 40 * 782264 * 2
def baseEnd_782264 : Nat := 44630825634314735800271

theorem tailTrace_782264 : CollatzResearch.WordTrace tailWord_782264 prefixEnd_782264 44630825634314735800271 := by
  unfold tailWord_782264
  simp only [CollatzResearch.WordTrace]
  refine ⟨14265756018999301449932923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19021008025332401933243897 14265756018999301449932923)
  ·
    refine ⟨21398634028498952174899385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14265756018999301449932923 21398634028498952174899385)
    ·
      refine ⟨16048975521374214131174539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21398634028498952174899385 16048975521374214131174539)
      ·
        refine ⟨24073463282061321196761809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16048975521374214131174539 24073463282061321196761809)
        ·
          refine ⟨18055097461545990897571357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24073463282061321196761809 18055097461545990897571357)
          ·
            refine ⟨6770661548079746586589259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18055097461545990897571357 6770661548079746586589259)
            ·
              refine ⟨10155992322119619879883889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6770661548079746586589259 10155992322119619879883889)
              ·
                refine ⟨7616994241589714909912917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10155992322119619879883889 7616994241589714909912917)
                ·
                  refine ⟨44630825634314735800271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7616994241589714909912917 44630825634314735800271)
                  ·
                    rfl

theorem cell23_782264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 9].length) (baseStart_782264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782264 prefixEnd_782264 := by exact prefixLift 782264
  have htrace : WordTrace (prefixWord ++ tailWord_782264) baseStart_782264 baseEnd_782264 := by
    simpa [prefixWord, tailWord_782264, baseEnd_782264] using wordTrace_append hprefix tailTrace_782264
  have hstable : (prefixWord ++ tailWord_782264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782264).length < 2 ^ (prefixWord ++ tailWord_782264).sum := by decide
  have hdescent : baseEnd_782264 < baseStart_782264 := by decide
  rcases family_descends (prefixWord ++ tailWord_782264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782331 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 4]
def baseStart_782331 : Nat := 118140960795 + 782331 * 2 ^ 59
def prefixEnd_782331 : Nat := 4983230072969 + 3 ^ 40 * 782331 * 2
def baseEnd_782331 : Nat := 401711833912683860064631

theorem tailTrace_782331 : CollatzResearch.WordTrace tailWord_782331 prefixEnd_782331 401711833912683860064631 := by
  unfold tailWord_782331
  simp only [CollatzResearch.WordTrace]
  refine ⟨28533955728755873342554847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19022637152503915561703231 28533955728755873342554847)
  ·
    refine ⟨42800933593133810013832271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28533955728755873342554847 42800933593133810013832271)
    ·
      refine ⟨64201400389700715020748407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42800933593133810013832271 64201400389700715020748407)
      ·
        refine ⟨96302100584551072531122611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64201400389700715020748407 96302100584551072531122611)
        ·
          refine ⟨144453150876826608796683917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96302100584551072531122611 144453150876826608796683917)
          ·
            refine ⟨54169931578809978298756469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144453150876826608796683917 54169931578809978298756469)
            ·
              refine ⟨5078431085513435465508419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54169931578809978298756469 5078431085513435465508419)
              ·
                refine ⟨7617646628270153198262629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5078431085513435465508419 7617646628270153198262629)
                ·
                  refine ⟨1428308742800653724674243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7617646628270153198262629 1428308742800653724674243)
                  ·
                    refine ⟨2142463114200980587011365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1428308742800653724674243 2142463114200980587011365)
                    ·
                      refine ⟨401711833912683860064631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2142463114200980587011365 401711833912683860064631)
                      ·
                        rfl

theorem cell23_782331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 4].length) (baseStart_782331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782331 prefixEnd_782331 := by exact prefixLift 782331
  have htrace : WordTrace (prefixWord ++ tailWord_782331) baseStart_782331 baseEnd_782331 := by
    simpa [prefixWord, tailWord_782331, baseEnd_782331] using wordTrace_append hprefix tailTrace_782331
  have hstable : (prefixWord ++ tailWord_782331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782331).length < 2 ^ (prefixWord ++ tailWord_782331).sum := by decide
  have hdescent : baseEnd_782331 < baseStart_782331 := by decide
  rcases family_descends (prefixWord ++ tailWord_782331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782348 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 1, 6, 2]
def baseStart_782348 : Nat := 118140960795 + 782348 * 2 ^ 59
def prefixEnd_782348 : Nat := 4983230072969 + 3 ^ 40 * 782348 * 2
def baseEnd_782348 : Nat := 401720563083810293552053

theorem tailTrace_782348 : CollatzResearch.WordTrace tailWord_782348 prefixEnd_782348 401720563083810293552053 := by
  unfold tailWord_782348
  simp only [CollatzResearch.WordTrace]
  refine ⟨14267287884847142622961849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19023050513129523497282465 14267287884847142622961849)
  ·
    refine ⟨10700465913635356967221387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14267287884847142622961849 10700465913635356967221387)
    ·
      refine ⟨16050698870453035450832081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10700465913635356967221387 16050698870453035450832081)
      ·
        refine ⟨12038024152839776588124061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16050698870453035450832081 12038024152839776588124061)
        ·
          refine ⟨4514259057314916220546523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12038024152839776588124061 4514259057314916220546523)
          ·
            refine ⟨6771388585972374330819785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4514259057314916220546523 6771388585972374330819785)
            ·
              refine ⟨5078541439479280748114839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6771388585972374330819785 5078541439479280748114839)
              ·
                refine ⟨7617812159218921122172259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5078541439479280748114839 7617812159218921122172259)
                ·
                  refine ⟨11426718238828381683258389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7617812159218921122172259 11426718238828381683258389)
                  ·
                    refine ⟨535627417445080391402737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11426718238828381683258389 535627417445080391402737)
                    ·
                      refine ⟨401720563083810293552053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 535627417445080391402737 401720563083810293552053)
                      ·
                        rfl

theorem cell23_782348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 1, 6, 2].length) (baseStart_782348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782348 prefixEnd_782348 := by exact prefixLift 782348
  have htrace : WordTrace (prefixWord ++ tailWord_782348) baseStart_782348 baseEnd_782348 := by
    simpa [prefixWord, tailWord_782348, baseEnd_782348] using wordTrace_append hprefix tailTrace_782348
  have hstable : (prefixWord ++ tailWord_782348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782348).length < 2 ^ (prefixWord ++ tailWord_782348).sum := by decide
  have hdescent : baseEnd_782348 < baseStart_782348 := by decide
  rcases family_descends (prefixWord ++ tailWord_782348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782365 : List Nat := [1, 4, 2, 2, 2, 2, 2, 1, 2, 1, 4]
def baseStart_782365 : Nat := 118140960795 + 782365 * 2 ^ 59
def prefixEnd_782365 : Nat := 4983230072969 + 3 ^ 40 * 782365 * 2
def baseEnd_782365 : Nat := 401729292254936727039475

theorem tailTrace_782365 : CollatzResearch.WordTrace tailWord_782365 prefixEnd_782365 401729292254936727039475 := by
  unfold tailWord_782365
  simp only [CollatzResearch.WordTrace]
  refine ⟨28535195810632697149292549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19023463873755131432861699 28535195810632697149292549)
  ·
    refine ⟨5350349214493630715492353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28535195810632697149292549 5350349214493630715492353)
    ·
      refine ⟨4012761910870223036619265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5350349214493630715492353 4012761910870223036619265)
      ·
        refine ⟨3009571433152667277464449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4012761910870223036619265 3009571433152667277464449)
        ·
          refine ⟨2257178574864500458098337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3009571433152667277464449 2257178574864500458098337)
          ·
            refine ⟨1692883931148375343573753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2257178574864500458098337 1692883931148375343573753)
            ·
              refine ⟨1269662948361281507680315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1692883931148375343573753 1269662948361281507680315)
              ·
                refine ⟨1904494422541922261520473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269662948361281507680315 1904494422541922261520473)
                ·
                  refine ⟨1428370816906441696140355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1904494422541922261520473 1428370816906441696140355)
                  ·
                    refine ⟨2142556225359662544210533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1428370816906441696140355 2142556225359662544210533)
                    ·
                      refine ⟨401729292254936727039475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2142556225359662544210533 401729292254936727039475)
                      ·
                        rfl

theorem cell23_782365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_782365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782365 prefixEnd_782365 := by exact prefixLift 782365
  have htrace : WordTrace (prefixWord ++ tailWord_782365) baseStart_782365 baseEnd_782365 := by
    simpa [prefixWord, tailWord_782365, baseEnd_782365] using wordTrace_append hprefix tailTrace_782365
  have hstable : (prefixWord ++ tailWord_782365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782365).length < 2 ^ (prefixWord ++ tailWord_782365).sum := by decide
  have hdescent : baseEnd_782365 < baseStart_782365 := by decide
  rcases family_descends (prefixWord ++ tailWord_782365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782392 : List Nat := [2, 1, 2, 1, 6, 1, 1, 4, 1, 4]
def baseStart_782392 : Nat := 118140960795 + 782392 * 2 ^ 59
def prefixEnd_782392 : Nat := 4983230072969 + 3 ^ 40 * 782392 * 2
def baseEnd_782392 : Nat := 133914385410869373800617

theorem tailTrace_782392 : CollatzResearch.WordTrace tailWord_782392 prefixEnd_782392 133914385410869373800617 := by
  unfold tailWord_782392
  simp only [CollatzResearch.WordTrace]
  refine ⟨14268090290767440380262715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19024120387689920507016953 14268090290767440380262715)
  ·
    refine ⟨21402135436151160570394073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14268090290767440380262715 21402135436151160570394073)
    ·
      refine ⟨16051601577113370427795555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21402135436151160570394073 16051601577113370427795555)
      ·
        refine ⟨24077402365670055641693333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16051601577113370427795555 24077402365670055641693333)
        ·
          refine ⟨1128628235890783858204375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24077402365670055641693333 1128628235890783858204375)
          ·
            refine ⟨1692942353836175787306563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1128628235890783858204375 1692942353836175787306563)
            ·
              refine ⟨2539413530754263680959845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1692942353836175787306563 2539413530754263680959845)
              ·
                refine ⟨476140037016424440179971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2539413530754263680959845 476140037016424440179971)
                ·
                  refine ⟨714210055524636660269957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 476140037016424440179971 714210055524636660269957)
                  ·
                    refine ⟨133914385410869373800617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 714210055524636660269957 133914385410869373800617)
                    ·
                      rfl

theorem cell23_782392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4, 1, 4].length) (baseStart_782392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782392 prefixEnd_782392 := by exact prefixLift 782392
  have htrace : WordTrace (prefixWord ++ tailWord_782392) baseStart_782392 baseEnd_782392 := by
    simpa [prefixWord, tailWord_782392, baseEnd_782392] using wordTrace_append hprefix tailTrace_782392
  have hstable : (prefixWord ++ tailWord_782392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782392).length < 2 ^ (prefixWord ++ tailWord_782392).sum := by decide
  have hdescent : baseEnd_782392 < baseStart_782392 := by decide
  rcases family_descends (prefixWord ++ tailWord_782392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782431 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 3, 6]
def baseStart_782431 : Nat := 118140960795 + 782431 * 2 ^ 59
def prefixEnd_782431 : Nat := 4983230072969 + 3 ^ 40 * 782431 * 2
def baseEnd_782431 : Nat := 133921060659377822938057

theorem tailTrace_782431 : CollatzResearch.WordTrace tailWord_782431 prefixEnd_782431 133921060659377822938057 := by
  unfold tailWord_782431
  simp only [CollatzResearch.WordTrace]
  refine ⟨28537603028393590421195147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19025068685595726947463431 28537603028393590421195147)
  ·
    refine ⟨42806404542590385631792721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28537603028393590421195147 42806404542590385631792721)
    ·
      refine ⟨32104803406942789223844541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42806404542590385631792721 32104803406942789223844541)
      ·
        refine ⟨12039301277603545958941703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32104803406942789223844541 12039301277603545958941703)
        ·
          refine ⟨18058951916405318938412555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12039301277603545958941703 18058951916405318938412555)
          ·
            refine ⟨27088427874607978407618833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18058951916405318938412555 27088427874607978407618833)
            ·
              refine ⟨20316320905955983805714125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27088427874607978407618833 20316320905955983805714125)
              ·
                refine ⟨7618620339733493927142797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20316320905955983805714125 7618620339733493927142797)
                ·
                  refine ⟨2856982627400060222678549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7618620339733493927142797 2856982627400060222678549)
                  ·
                    refine ⟨133921060659377822938057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2856982627400060222678549 133921060659377822938057)
                    ·
                      rfl

theorem cell23_782431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 6].length) (baseStart_782431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782431 prefixEnd_782431 := by exact prefixLift 782431
  have htrace : WordTrace (prefixWord ++ tailWord_782431) baseStart_782431 baseEnd_782431 := by
    simpa [prefixWord, tailWord_782431, baseEnd_782431] using wordTrace_append hprefix tailTrace_782431
  have hstable : (prefixWord ++ tailWord_782431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782431).length < 2 ^ (prefixWord ++ tailWord_782431).sum := by decide
  have hdescent : baseEnd_782431 < baseStart_782431 := by decide
  rcases family_descends (prefixWord ++ tailWord_782431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782432 : List Nat := [2, 1, 1, 3, 2, 3, 1, 5, 1, 1, 3]
def baseStart_782432 : Nat := 118140960795 + 782432 * 2 ^ 59
def prefixEnd_782432 : Nat := 4983230072969 + 3 ^ 40 * 782432 * 2
def baseEnd_782432 : Nat := 401763695458787964901667

theorem tailTrace_782432 : CollatzResearch.WordTrace tailWord_782432 prefixEnd_782432 401763695458787964901667 := by
  unfold tailWord_782432
  simp only [CollatzResearch.WordTrace]
  refine ⟨14268819750694983795990775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19025093000926645061321033 14268819750694983795990775)
  ·
    refine ⟨21403229626042475693986163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14268819750694983795990775 21403229626042475693986163)
    ·
      refine ⟨32104844439063713540979245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21403229626042475693986163 32104844439063713540979245)
      ·
        refine ⟨12039316664648892577867217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32104844439063713540979245 12039316664648892577867217)
        ·
          refine ⟨9029487498486669433400413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12039316664648892577867217 9029487498486669433400413)
          ·
            refine ⟨3386057811932501037525155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9029487498486669433400413 3386057811932501037525155)
            ·
              refine ⟨5079086717898751556287733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3386057811932501037525155 5079086717898751556287733)
              ·
                refine ⟨476164379803007958401975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5079086717898751556287733 476164379803007958401975)
                ·
                  refine ⟨714246569704511937602963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 476164379803007958401975 714246569704511937602963)
                  ·
                    refine ⟨1071369854556767906404445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 714246569704511937602963 1071369854556767906404445)
                    ·
                      refine ⟨401763695458787964901667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1071369854556767906404445 401763695458787964901667)
                      ·
                        rfl

theorem cell23_782432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5, 1, 1, 3].length) (baseStart_782432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782432 prefixEnd_782432 := by exact prefixLift 782432
  have htrace : WordTrace (prefixWord ++ tailWord_782432) baseStart_782432 baseEnd_782432 := by
    simpa [prefixWord, tailWord_782432, baseEnd_782432] using wordTrace_append hprefix tailTrace_782432
  have hstable : (prefixWord ++ tailWord_782432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782432).length < 2 ^ (prefixWord ++ tailWord_782432).sum := by decide
  have hdescent : baseEnd_782432 < baseStart_782432 := by decide
  rcases family_descends (prefixWord ++ tailWord_782432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782435 : List Nat := [1, 1, 1, 5, 1, 1, 6, 1, 1, 5]
def baseStart_782435 : Nat := 118140960795 + 782435 * 2 ^ 59
def prefixEnd_782435 : Nat := 4983230072969 + 3 ^ 40 * 782435 * 2
def baseEnd_782435 : Nat := 133921745300250484388051

theorem tailTrace_782435 : CollatzResearch.WordTrace tailWord_782435 prefixEnd_782435 133921745300250484388051 := by
  unfold tailWord_782435
  simp only [CollatzResearch.WordTrace]
  refine ⟨28537748920379099104340759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19025165946919399402893839 28537748920379099104340759)
  ·
    refine ⟨42806623380568648656511139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28537748920379099104340759 42806623380568648656511139)
    ·
      refine ⟨64209935070852972984766709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42806623380568648656511139 64209935070852972984766709)
      ·
        refine ⟨6019681412892466217321879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64209935070852972984766709 6019681412892466217321879)
        ·
          refine ⟨9029522119338699325982819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6019681412892466217321879 9029522119338699325982819)
          ·
            refine ⟨13544283179008048988974229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9029522119338699325982819 13544283179008048988974229)
            ·
              refine ⟨634888274016002296358167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13544283179008048988974229 634888274016002296358167)
              ·
                refine ⟨952332411024003444537251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 634888274016002296358167 952332411024003444537251)
                ·
                  refine ⟨1428498616536005166805877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 952332411024003444537251 1428498616536005166805877)
                  ·
                    refine ⟨133921745300250484388051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1428498616536005166805877 133921745300250484388051)
                    ·
                      rfl

theorem cell23_782435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 1, 5].length) (baseStart_782435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782435 prefixEnd_782435 := by exact prefixLift 782435
  have htrace : WordTrace (prefixWord ++ tailWord_782435) baseStart_782435 baseEnd_782435 := by
    simpa [prefixWord, tailWord_782435, baseEnd_782435] using wordTrace_append hprefix tailTrace_782435
  have hstable : (prefixWord ++ tailWord_782435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782435).length < 2 ^ (prefixWord ++ tailWord_782435).sum := by decide
  have hdescent : baseEnd_782435 < baseStart_782435 := by decide
  rcases family_descends (prefixWord ++ tailWord_782435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782451 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 4]
def baseStart_782451 : Nat := 118140960795 + 782451 * 2 ^ 59
def prefixEnd_782451 : Nat := 4983230072969 + 3 ^ 40 * 782451 * 2
def baseEnd_782451 : Nat := 401773451591223390564079

theorem tailTrace_782451 : CollatzResearch.WordTrace tailWord_782451 prefixEnd_782451 401773451591223390564079 := by
  unfold tailWord_782451
  simp only [CollatzResearch.WordTrace]
  refine ⟨28538332488321133836923207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19025554992214089224615471 28538332488321133836923207)
  ·
    refine ⟨42807498732481700755384811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28538332488321133836923207 42807498732481700755384811)
    ·
      refine ⟨64211248098722551133077217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42807498732481700755384811 64211248098722551133077217)
      ·
        refine ⟨48158436074041913349807913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64211248098722551133077217 48158436074041913349807913)
        ·
          refine ⟨36118827055531435012355935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48158436074041913349807913 36118827055531435012355935)
          ·
            refine ⟨54178240583297152518533903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36118827055531435012355935 54178240583297152518533903)
            ·
              refine ⟨81267360874945728777800855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54178240583297152518533903 81267360874945728777800855)
              ·
                refine ⟨121901041312418593166701283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81267360874945728777800855 121901041312418593166701283)
                ·
                  refine ⟨182851561968627889750051925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121901041312418593166701283 182851561968627889750051925)
                  ·
                    refine ⟨2142791741819858083008421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 182851561968627889750051925 2142791741819858083008421)
                    ·
                      refine ⟨401773451591223390564079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2142791741819858083008421 401773451591223390564079)
                      ·
                        rfl

theorem cell23_782451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 4].length) (baseStart_782451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782451 prefixEnd_782451 := by exact prefixLift 782451
  have htrace : WordTrace (prefixWord ++ tailWord_782451) baseStart_782451 baseEnd_782451 := by
    simpa [prefixWord, tailWord_782451, baseEnd_782451] using wordTrace_append hprefix tailTrace_782451
  have hstable : (prefixWord ++ tailWord_782451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782451).length < 2 ^ (prefixWord ++ tailWord_782451).sum := by decide
  have hdescent : baseEnd_782451 < baseStart_782451 := by decide
  rcases family_descends (prefixWord ++ tailWord_782451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782468 : List Nat := [2, 3, 2, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_782468 : Nat := 118140960795 + 782468 * 2 ^ 59
def prefixEnd_782468 : Nat := 4983230072969 + 3 ^ 40 * 782468 * 2
def baseEnd_782468 : Nat := 401782180762349824051501

theorem tailTrace_782468 : CollatzResearch.WordTrace tailWord_782468 prefixEnd_782468 401782180762349824051501 := by
  unfold tailWord_782468
  simp only [CollatzResearch.WordTrace]
  refine ⟨14269476264629772870146029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19025968352839697160194705 14269476264629772870146029)
  ·
    refine ⟨5351053599236164826304761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14269476264629772870146029 5351053599236164826304761)
    ·
      refine ⟨4013290199427123619728571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5351053599236164826304761 4013290199427123619728571)
      ·
        refine ⟨6019935299140685429592857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4013290199427123619728571 6019935299140685429592857)
        ·
          refine ⟨4514951474355514072194643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6019935299140685429592857 4514951474355514072194643)
          ·
            refine ⟨6772427211533271108291965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4514951474355514072194643 6772427211533271108291965)
            ·
              refine ⟨2539660204324976665609487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6772427211533271108291965 2539660204324976665609487)
              ·
                refine ⟨3809490306487464998414231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2539660204324976665609487 3809490306487464998414231)
                ·
                  refine ⟨5714235459731197497621347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3809490306487464998414231 5714235459731197497621347)
                  ·
                    refine ⟨8571353189596796246432021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5714235459731197497621347 8571353189596796246432021)
                    ·
                      refine ⟨401782180762349824051501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8571353189596796246432021 401782180762349824051501)
                      ·
                        rfl

theorem cell23_782468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_782468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782468 prefixEnd_782468 := by exact prefixLift 782468
  have htrace : WordTrace (prefixWord ++ tailWord_782468) baseStart_782468 baseEnd_782468 := by
    simpa [prefixWord, tailWord_782468, baseEnd_782468] using wordTrace_append hprefix tailTrace_782468
  have hstable : (prefixWord ++ tailWord_782468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782468).length < 2 ^ (prefixWord ++ tailWord_782468).sum := by decide
  have hdescent : baseEnd_782468 < baseStart_782468 := by decide
  rcases family_descends (prefixWord ++ tailWord_782468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782472 : List Nat := [2, 1, 3, 4, 1, 2, 2, 2, 1, 1, 4]
def baseStart_782472 : Nat := 118140960795 + 782472 * 2 ^ 59
def prefixEnd_782472 : Nat := 4983230072969 + 3 ^ 40 * 782472 * 2
def baseEnd_782472 : Nat := 401784234684967808401483

theorem tailTrace_782472 : CollatzResearch.WordTrace tailWord_782472 prefixEnd_782472 401784234684967808401483 := by
  unfold tailWord_782472
  simp only [CollatzResearch.WordTrace]
  refine ⟨14269549210622527211718835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19026065614163369615625113 14269549210622527211718835)
  ·
    refine ⟨21404323815933790817578253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14269549210622527211718835 21404323815933790817578253)
    ·
      refine ⟨8026621430975171556591845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21404323815933790817578253 8026621430975171556591845)
      ·
        refine ⟨1504991518307844666860971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8026621430975171556591845 1504991518307844666860971)
        ·
          refine ⟨2257487277461767000291457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1504991518307844666860971 2257487277461767000291457)
          ·
            refine ⟨1693115458096325250218593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2257487277461767000291457 1693115458096325250218593)
            ·
              refine ⟨1269836593572243937663945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1693115458096325250218593 1269836593572243937663945)
              ·
                refine ⟨952377445179182953247959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1269836593572243937663945 952377445179182953247959)
                ·
                  refine ⟨1428566167768774429871939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 952377445179182953247959 1428566167768774429871939)
                  ·
                    refine ⟨2142849251653161644807909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1428566167768774429871939 2142849251653161644807909)
                    ·
                      refine ⟨401784234684967808401483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2142849251653161644807909 401784234684967808401483)
                      ·
                        rfl

theorem cell23_782472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_782472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782472 prefixEnd_782472 := by exact prefixLift 782472
  have htrace : WordTrace (prefixWord ++ tailWord_782472) baseStart_782472 baseEnd_782472 := by
    simpa [prefixWord, tailWord_782472, baseEnd_782472] using wordTrace_append hprefix tailTrace_782472
  have hstable : (prefixWord ++ tailWord_782472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782472).length < 2 ^ (prefixWord ++ tailWord_782472).sum := by decide
  have hdescent : baseEnd_782472 < baseStart_782472 := by decide
  rcases family_descends (prefixWord ++ tailWord_782472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782481 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 6]
def baseStart_782481 : Nat := 118140960795 + 782481 * 2 ^ 59
def prefixEnd_782481 : Nat := 4983230072969 + 3 ^ 40 * 782481 * 2
def baseEnd_782481 : Nat := 401788856010858273188941

theorem tailTrace_782481 : CollatzResearch.WordTrace tailWord_782481 prefixEnd_782481 401788856010858273188941 := by
  unfold tailWord_782481
  simp only [CollatzResearch.WordTrace]
  refine ⟨28539426678212448960515297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19026284452141632640343531 28539426678212448960515297)
  ·
    refine ⟨21404570008659336720386473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28539426678212448960515297 21404570008659336720386473)
    ·
      refine ⟨16053427506494502540289855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21404570008659336720386473 16053427506494502540289855)
      ·
        refine ⟨24080141259741753810434783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16053427506494502540289855 24080141259741753810434783)
        ·
          refine ⟨36120211889612630715652175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24080141259741753810434783 36120211889612630715652175)
          ·
            refine ⟨54180317834418946073478263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36120211889612630715652175 54180317834418946073478263)
            ·
              refine ⟨81270476751628419110217395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54180317834418946073478263 81270476751628419110217395)
              ·
                refine ⟨121905715127442628665326093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81270476751628419110217395 121905715127442628665326093)
                ·
                  refine ⟨45714643172790985749497285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121905715127442628665326093 45714643172790985749497285)
                  ·
                    refine ⟨8571495594898309828030741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45714643172790985749497285 8571495594898309828030741)
                    ·
                      refine ⟨401788856010858273188941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8571495594898309828030741 401788856010858273188941)
                      ·
                        rfl

theorem cell23_782481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_782481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782481 prefixEnd_782481 := by exact prefixLift 782481
  have htrace : WordTrace (prefixWord ++ tailWord_782481) baseStart_782481 baseEnd_782481 := by
    simpa [prefixWord, tailWord_782481, baseEnd_782481] using wordTrace_append hprefix tailTrace_782481
  have hstable : (prefixWord ++ tailWord_782481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782481).length < 2 ^ (prefixWord ++ tailWord_782481).sum := by decide
  have hdescent : baseEnd_782481 < baseStart_782481 := by decide
  rcases family_descends (prefixWord ++ tailWord_782481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782491 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 4, 7]
def baseStart_782491 : Nat := 118140960795 + 782491 * 2 ^ 59
def prefixEnd_782491 : Nat := 4983230072969 + 3 ^ 40 * 782491 * 2
def baseEnd_782491 : Nat := 133931330272467744687965

theorem tailTrace_782491 : CollatzResearch.WordTrace tailWord_782491 prefixEnd_782491 133931330272467744687965 := by
  unfold tailWord_782491
  simp only [CollatzResearch.WordTrace]
  refine ⟨28539791408176220668379327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19026527605450813778919551 28539791408176220668379327)
  ·
    refine ⟨42809687112264331002568991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28539791408176220668379327 42809687112264331002568991)
    ·
      refine ⟨64214530668396496503853487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42809687112264331002568991 64214530668396496503853487)
      ·
        refine ⟨96321796002594744755780231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64214530668396496503853487 96321796002594744755780231)
        ·
          refine ⟨144482694003892117133670347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96321796002594744755780231 144482694003892117133670347)
          ·
            refine ⟨216724041005838175700505521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144482694003892117133670347 216724041005838175700505521)
            ·
              refine ⟨162543030754378631775379141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216724041005838175700505521 162543030754378631775379141)
              ·
                refine ⟨30476818266445993457883589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162543030754378631775379141 30476818266445993457883589)
                ·
                  refine ⟨5714403424958623773353173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30476818266445993457883589 5714403424958623773353173)
                  ·
                    refine ⟨133931330272467744687965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5714403424958623773353173 133931330272467744687965)
                    ·
                      rfl

theorem cell23_782491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 7].length) (baseStart_782491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782491 prefixEnd_782491 := by exact prefixLift 782491
  have htrace : WordTrace (prefixWord ++ tailWord_782491) baseStart_782491 baseEnd_782491 := by
    simpa [prefixWord, tailWord_782491, baseEnd_782491] using wordTrace_append hprefix tailTrace_782491
  have hstable : (prefixWord ++ tailWord_782491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782491).length < 2 ^ (prefixWord ++ tailWord_782491).sum := by decide
  have hdescent : baseEnd_782491 < baseStart_782491 := by decide
  rcases family_descends (prefixWord ++ tailWord_782491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782515 : List Nat := [1, 1, 1, 2, 3, 2, 1, 4, 3, 3, 2]
def baseStart_782515 : Nat := 118140960795 + 782515 * 2 ^ 59
def prefixEnd_782515 : Nat := 4983230072969 + 3 ^ 40 * 782515 * 2
def baseEnd_782515 : Nat := 401806314353111140163785

theorem tailTrace_782515 : CollatzResearch.WordTrace tailWord_782515 prefixEnd_782515 401806314353111140163785 := by
  unfold tailWord_782515
  simp only [CollatzResearch.WordTrace]
  refine ⟨28540666760089272767252999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19027111173392848511501999 28540666760089272767252999)
  ·
    refine ⟨42811000140133909150879499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28540666760089272767252999 42811000140133909150879499)
    ·
      refine ⟨64216500210200863726319249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42811000140133909150879499 64216500210200863726319249)
      ·
        refine ⟨48162375157650647794739437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64216500210200863726319249 48162375157650647794739437)
        ·
          refine ⟨18060890684118992923027289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48162375157650647794739437 18060890684118992923027289)
          ·
            refine ⟨13545668013089244692270467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18060890684118992923027289 13545668013089244692270467)
            ·
              refine ⟨20318502019633867038405701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13545668013089244692270467 20318502019633867038405701)
              ·
                refine ⟨3809719128681350069701069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20318502019633867038405701 3809719128681350069701069)
                ·
                  refine ⟨1428644673255506276137901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3809719128681350069701069 1428644673255506276137901)
                  ·
                    refine ⟨535741752470814853551713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1428644673255506276137901 535741752470814853551713)
                    ·
                      refine ⟨401806314353111140163785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 535741752470814853551713 401806314353111140163785)
                      ·
                        rfl

theorem cell23_782515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 3, 2].length) (baseStart_782515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782515 prefixEnd_782515 := by exact prefixLift 782515
  have htrace : WordTrace (prefixWord ++ tailWord_782515) baseStart_782515 baseEnd_782515 := by
    simpa [prefixWord, tailWord_782515, baseEnd_782515] using wordTrace_append hprefix tailTrace_782515
  have hstable : (prefixWord ++ tailWord_782515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782515).length < 2 ^ (prefixWord ++ tailWord_782515).sum := by decide
  have hdescent : baseEnd_782515 < baseStart_782515 := by decide
  rcases family_descends (prefixWord ++ tailWord_782515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782526 : List Nat := [4, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3]
def baseStart_782526 : Nat := 118140960795 + 782526 * 2 ^ 59
def prefixEnd_782526 : Nat := 4983230072969 + 3 ^ 40 * 782526 * 2
def baseEnd_782526 : Nat := 401811962640310597126235

theorem tailTrace_782526 : CollatzResearch.WordTrace tailWord_782526 prefixEnd_782526 401811962640310597126235 := by
  unfold tailWord_782526
  simp only [CollatzResearch.WordTrace]
  refine ⟨3567633495381177705737929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19027378642032947763935621 3567633495381177705737929)
  ·
    refine ⟨2675725121535883279303447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3567633495381177705737929 2675725121535883279303447)
    ·
      refine ⟨4013587682303824918955171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2675725121535883279303447 4013587682303824918955171)
      ·
        refine ⟨6020381523455737378432757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4013587682303824918955171 6020381523455737378432757)
        ·
          refine ⟨564410767823975379228071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6020381523455737378432757 564410767823975379228071)
          ·
            refine ⟨846616151735963068842107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564410767823975379228071 846616151735963068842107)
            ·
              refine ⟨1269924227603944603263161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 846616151735963068842107 1269924227603944603263161)
              ·
                refine ⟨952443170702958452447371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1269924227603944603263161 952443170702958452447371)
                ·
                  refine ⟨1428664756054437678671057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 952443170702958452447371 1428664756054437678671057)
                  ·
                    refine ⟨1071498567040828259003293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1428664756054437678671057 1071498567040828259003293)
                    ·
                      refine ⟨401811962640310597126235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1071498567040828259003293 401811962640310597126235)
                      ·
                        rfl

theorem cell23_782526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_782526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782526 prefixEnd_782526 := by exact prefixLift 782526
  have htrace : WordTrace (prefixWord ++ tailWord_782526) baseStart_782526 baseEnd_782526 := by
    simpa [prefixWord, tailWord_782526, baseEnd_782526] using wordTrace_append hprefix tailTrace_782526
  have hstable : (prefixWord ++ tailWord_782526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782526).length < 2 ^ (prefixWord ++ tailWord_782526).sum := by decide
  have hdescent : baseEnd_782526 < baseStart_782526 := by decide
  rcases family_descends (prefixWord ++ tailWord_782526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782545 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 3, 4, 2]
def baseStart_782545 : Nat := 118140960795 + 782545 * 2 ^ 59
def prefixEnd_782545 : Nat := 4983230072969 + 3 ^ 40 * 782545 * 2
def baseEnd_782545 : Nat := 401821718772746022788647

theorem tailTrace_782545 : CollatzResearch.WordTrace tailWord_782545 prefixEnd_782545 401821718772746022788647 := by
  unfold tailWord_782545
  simp only [CollatzResearch.WordTrace]
  refine ⟨28541760949980587890845089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19027840633320391927230059 28541760949980587890845089)
  ·
    refine ⟨21406320712485440918133817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28541760949980587890845089 21406320712485440918133817)
    ·
      refine ⟨16054740534364080688600363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21406320712485440918133817 16054740534364080688600363)
      ·
        refine ⟨24082110801546121032900545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16054740534364080688600363 24082110801546121032900545)
        ·
          refine ⟨18061583101159590774675409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24082110801546121032900545 18061583101159590774675409)
          ·
            refine ⟨13546187325869693081006557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18061583101159590774675409 13546187325869693081006557)
            ·
              refine ⟨5079820247201134905377459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13546187325869693081006557 5079820247201134905377459)
              ·
                refine ⟨7619730370801702358066189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5079820247201134905377459 7619730370801702358066189)
                ·
                  refine ⟨2857398889050638384274821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7619730370801702358066189 2857398889050638384274821)
                  ·
                    refine ⟨535762291696994697051529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2857398889050638384274821 535762291696994697051529)
                    ·
                      refine ⟨401821718772746022788647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 535762291696994697051529 401821718772746022788647)
                      ·
                        rfl

theorem cell23_782545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 4, 2].length) (baseStart_782545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782545 prefixEnd_782545 := by exact prefixLift 782545
  have htrace : WordTrace (prefixWord ++ tailWord_782545) baseStart_782545 baseEnd_782545 := by
    simpa [prefixWord, tailWord_782545, baseEnd_782545] using wordTrace_append hprefix tailTrace_782545
  have hstable : (prefixWord ++ tailWord_782545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782545).length < 2 ^ (prefixWord ++ tailWord_782545).sum := by decide
  have hdescent : baseEnd_782545 < baseStart_782545 := by decide
  rcases family_descends (prefixWord ++ tailWord_782545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782565 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 2, 4, 3]
def baseStart_782565 : Nat := 118140960795 + 782565 * 2 ^ 59
def prefixEnd_782565 : Nat := 4983230072969 + 3 ^ 40 * 782565 * 2
def baseEnd_782565 : Nat := 401831988385835944538555

theorem tailTrace_782565 : CollatzResearch.WordTrace tailWord_782565 prefixEnd_782565 401831988385835944538555 := by
  unfold tailWord_782565
  simp only [CollatzResearch.WordTrace]
  refine ⟨28542490409908131306573149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19028326939938754204382099 28542490409908131306573149)
  ·
    refine ⟨10703433903715549239964931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28542490409908131306573149 10703433903715549239964931)
    ·
      refine ⟨16055150855573323859947397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10703433903715549239964931 16055150855573323859947397)
      ·
        refine ⟨3010340785419998223740137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16055150855573323859947397 3010340785419998223740137)
        ·
          refine ⟨2257755589064998667805103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3010340785419998223740137 2257755589064998667805103)
          ·
            refine ⟨3386633383597498001707655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2257755589064998667805103 3386633383597498001707655)
            ·
              refine ⟨5079950075396247002561483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3386633383597498001707655 5079950075396247002561483)
              ·
                refine ⟨7619925113094370503842225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5079950075396247002561483 7619925113094370503842225)
                ·
                  refine ⟨5714943834820777877881669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7619925113094370503842225 5714943834820777877881669)
                  ·
                    refine ⟨1071551969028895852102813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5714943834820777877881669 1071551969028895852102813)
                    ·
                      refine ⟨401831988385835944538555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1071551969028895852102813 401831988385835944538555)
                      ·
                        rfl

theorem cell23_782565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_782565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782565 prefixEnd_782565 := by exact prefixLift 782565
  have htrace : WordTrace (prefixWord ++ tailWord_782565) baseStart_782565 baseEnd_782565 := by
    simpa [prefixWord, tailWord_782565, baseEnd_782565] using wordTrace_append hprefix tailTrace_782565
  have hstable : (prefixWord ++ tailWord_782565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782565).length < 2 ^ (prefixWord ++ tailWord_782565).sum := by decide
  have hdescent : baseEnd_782565 < baseStart_782565 := by decide
  rcases family_descends (prefixWord ++ tailWord_782565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782575 : List Nat := [1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 4]
def baseStart_782575 : Nat := 118140960795 + 782575 * 2 ^ 59
def prefixEnd_782575 : Nat := 4983230072969 + 3 ^ 40 * 782575 * 2
def baseEnd_782575 : Nat := 401837123192380905413509

theorem tailTrace_782575 : CollatzResearch.WordTrace tailWord_782575 prefixEnd_782575 401837123192380905413509 := by
  unfold tailWord_782575
  simp only [CollatzResearch.WordTrace]
  refine ⟨28542855139871903014437179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19028570093247935342958119 28542855139871903014437179)
  ·
    refine ⟨42814282709807854521655769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28542855139871903014437179 42814282709807854521655769)
    ·
      refine ⟨32110712032355890891241827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42814282709807854521655769 32110712032355890891241827)
      ·
        refine ⟨48166068048533836336862741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32110712032355890891241827 48166068048533836336862741)
        ·
          refine ⟨2257784439775023578290441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48166068048533836336862741 2257784439775023578290441)
          ·
            refine ⟨1693338329831267683717831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2257784439775023578290441 1693338329831267683717831)
            ·
              refine ⟨2540007494746901525576747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1693338329831267683717831 2540007494746901525576747)
              ·
                refine ⟨3810011242120352288365121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2540007494746901525576747 3810011242120352288365121)
                ·
                  refine ⟨2857508431590264216273841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3810011242120352288365121 2857508431590264216273841)
                  ·
                    refine ⟨2143131323692698162205381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2857508431590264216273841 2143131323692698162205381)
                    ·
                      refine ⟨401837123192380905413509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2143131323692698162205381 401837123192380905413509)
                      ·
                        rfl

theorem cell23_782575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 4].length) (baseStart_782575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782575 prefixEnd_782575 := by exact prefixLift 782575
  have htrace : WordTrace (prefixWord ++ tailWord_782575) baseStart_782575 baseEnd_782575 := by
    simpa [prefixWord, tailWord_782575, baseEnd_782575] using wordTrace_append hprefix tailTrace_782575
  have hstable : (prefixWord ++ tailWord_782575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782575).length < 2 ^ (prefixWord ++ tailWord_782575).sum := by decide
  have hdescent : baseEnd_782575 < baseStart_782575 := by decide
  rcases family_descends (prefixWord ++ tailWord_782575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782655 : List Nat := [1, 1, 2, 2, 4, 1, 1, 3, 1, 4, 3]
def baseStart_782655 : Nat := 118140960795 + 782655 * 2 ^ 59
def prefixEnd_782655 : Nat := 4983230072969 + 3 ^ 40 * 782655 * 2
def baseEnd_782655 : Nat := 401878201644740592413141

theorem tailTrace_782655 : CollatzResearch.WordTrace tailWord_782655 prefixEnd_782655 401878201644740592413141 := by
  unfold tailWord_782655
  simp only [CollatzResearch.WordTrace]
  refine ⟨28545772979582076677349419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19030515319721384451566279 28545772979582076677349419)
  ·
    refine ⟨42818659469373115016024129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28545772979582076677349419 42818659469373115016024129)
    ·
      refine ⟨32113994602029836262018097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42818659469373115016024129 32113994602029836262018097)
      ·
        refine ⟨24085495951522377196513573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32113994602029836262018097 24085495951522377196513573)
        ·
          refine ⟨4516030490910445724346295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24085495951522377196513573 4516030490910445724346295)
          ·
            refine ⟨6774045736365668586519443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4516030490910445724346295 6774045736365668586519443)
            ·
              refine ⟨10161068604548502879779165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6774045736365668586519443 10161068604548502879779165)
              ·
                refine ⟨3810400726705688579917187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10161068604548502879779165 3810400726705688579917187)
                ·
                  refine ⟨5715601090058532869875781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3810400726705688579917187 5715601090058532869875781)
                  ·
                    refine ⟨1071675204385974913101709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5715601090058532869875781 1071675204385974913101709)
                    ·
                      refine ⟨401878201644740592413141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1071675204385974913101709 401878201644740592413141)
                      ·
                        rfl

theorem cell23_782655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4, 3].length) (baseStart_782655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782655 prefixEnd_782655 := by exact prefixLift 782655
  have htrace : WordTrace (prefixWord ++ tailWord_782655) baseStart_782655 baseEnd_782655 := by
    simpa [prefixWord, tailWord_782655, baseEnd_782655] using wordTrace_append hprefix tailTrace_782655
  have hstable : (prefixWord ++ tailWord_782655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782655).length < 2 ^ (prefixWord ++ tailWord_782655).sum := by decide
  have hdescent : baseEnd_782655 < baseStart_782655 := by decide
  rcases family_descends (prefixWord ++ tailWord_782655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782672 : List Nat := [2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 3]
def baseStart_782672 : Nat := 118140960795 + 782672 * 2 ^ 59
def prefixEnd_782672 : Nat := 4983230072969 + 3 ^ 40 * 782672 * 2
def baseEnd_782672 : Nat := 401886930815867025900563

theorem tailTrace_782672 : CollatzResearch.WordTrace tailWord_782672 prefixEnd_782672 401886930815867025900563 := by
  unfold tailWord_782672
  simp only [CollatzResearch.WordTrace]
  refine ⟨14273196510260244290359135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19030928680346992387145513 14273196510260244290359135)
  ·
    refine ⟨21409794765390366435538703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14273196510260244290359135 21409794765390366435538703)
    ·
      refine ⟨32114692148085549653308055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21409794765390366435538703 32114692148085549653308055)
      ·
        refine ⟨48172038222128324479962083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32114692148085549653308055 48172038222128324479962083)
        ·
          refine ⟨72258057333192486719943125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48172038222128324479962083 72258057333192486719943125)
          ·
            refine ⟨1693548218746698907498667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 72258057333192486719943125 1693548218746698907498667)
            ·
              refine ⟨2540322328120048361248001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1693548218746698907498667 2540322328120048361248001)
              ·
                refine ⟨1905241746090036270936001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2540322328120048361248001 1905241746090036270936001)
                ·
                  refine ⟨1428931309567527203202001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1905241746090036270936001 1428931309567527203202001)
                  ·
                    refine ⟨1071698482175645402401501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1428931309567527203202001 1071698482175645402401501)
                    ·
                      refine ⟨401886930815867025900563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1071698482175645402401501 401886930815867025900563)
                      ·
                        rfl

theorem cell23_782672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 3].length) (baseStart_782672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782672 prefixEnd_782672 := by exact prefixLift 782672
  have htrace : WordTrace (prefixWord ++ tailWord_782672) baseStart_782672 baseEnd_782672 := by
    simpa [prefixWord, tailWord_782672, baseEnd_782672] using wordTrace_append hprefix tailTrace_782672
  have hstable : (prefixWord ++ tailWord_782672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782672).length < 2 ^ (prefixWord ++ tailWord_782672).sum := by decide
  have hdescent : baseEnd_782672 < baseStart_782672 := by decide
  rcases family_descends (prefixWord ++ tailWord_782672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782729 : List Nat := [1, 2, 1, 1, 6, 1, 2, 2, 2, 3, 2]
def baseStart_782729 : Nat := 118140960795 + 782729 * 2 ^ 59
def prefixEnd_782729 : Nat := 4983230072969 + 3 ^ 40 * 782729 * 2
def baseEnd_782729 : Nat := 401916199213173302887801

theorem tailTrace_782729 : CollatzResearch.WordTrace tailWord_782729 prefixEnd_782729 401916199213173302887801 := by
  unfold tailWord_782729
  simp only [CollatzResearch.WordTrace]
  refine ⟨28548471981313987315543241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19032314654209324877028827 28548471981313987315543241)
  ·
    refine ⟨21411353985985490486657431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28548471981313987315543241 21411353985985490486657431)
    ·
      refine ⟨32117030978978235729986147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21411353985985490486657431 32117030978978235729986147)
      ·
        refine ⟨48175546468467353594979221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32117030978978235729986147 48175546468467353594979221)
        ·
          refine ⟨2258228740709407199764651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48175546468467353594979221 2258228740709407199764651)
          ·
            refine ⟨3387343111064110799646977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2258228740709407199764651 3387343111064110799646977)
            ·
              refine ⟨2540507333298083099735233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3387343111064110799646977 2540507333298083099735233)
              ·
                refine ⟨1905380499973562324801425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2540507333298083099735233 1905380499973562324801425)
                ·
                  refine ⟨1429035374980171743601069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1905380499973562324801425 1429035374980171743601069)
                  ·
                    refine ⟨535888265617564403850401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1429035374980171743601069 535888265617564403850401)
                    ·
                      refine ⟨401916199213173302887801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 535888265617564403850401 401916199213173302887801)
                      ·
                        rfl

theorem cell23_782729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 3, 2].length) (baseStart_782729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782729 prefixEnd_782729 := by exact prefixLift 782729
  have htrace : WordTrace (prefixWord ++ tailWord_782729) baseStart_782729 baseEnd_782729 := by
    simpa [prefixWord, tailWord_782729, baseEnd_782729] using wordTrace_append hprefix tailTrace_782729
  have hstable : (prefixWord ++ tailWord_782729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782729).length < 2 ^ (prefixWord ++ tailWord_782729).sum := by decide
  have hdescent : baseEnd_782729 < baseStart_782729 := by decide
  rcases family_descends (prefixWord ++ tailWord_782729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782730 : List Nat := [3, 1, 2, 5, 1, 2, 2, 2, 1, 4]
def baseStart_782730 : Nat := 118140960795 + 782730 * 2 ^ 59
def prefixEnd_782730 : Nat := 4983230072969 + 3 ^ 40 * 782730 * 2
def baseEnd_782730 : Nat := 133972237564609266325099

theorem tailTrace_782730 : CollatzResearch.WordTrace tailWord_782730 prefixEnd_782730 133972237564609266325099 := by
  unfold tailWord_782730
  simp only [CollatzResearch.WordTrace]
  refine ⟨7137127113577591121582411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19032338969540242990886429 7137127113577591121582411)
  ·
    refine ⟨10705690670366386682373617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7137127113577591121582411 10705690670366386682373617)
    ·
      refine ⟨8029268002774790011780213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10705690670366386682373617 8029268002774790011780213)
      ·
        refine ⟨752743875260136563604395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8029268002774790011780213 752743875260136563604395)
        ·
          refine ⟨1129115812890204845406593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 752743875260136563604395 1129115812890204845406593)
          ·
            refine ⟨846836859667653634054945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1129115812890204845406593 846836859667653634054945)
            ·
              refine ⟨635127644750740225541209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 846836859667653634054945 635127644750740225541209)
              ·
                refine ⟨476345733563055169155907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 635127644750740225541209 476345733563055169155907)
                ·
                  refine ⟨714518600344582753733861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 476345733563055169155907 714518600344582753733861)
                  ·
                    refine ⟨133972237564609266325099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 714518600344582753733861 133972237564609266325099)
                    ·
                      rfl

theorem cell23_782730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_782730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782730 prefixEnd_782730 := by exact prefixLift 782730
  have htrace : WordTrace (prefixWord ++ tailWord_782730) baseStart_782730 baseEnd_782730 := by
    simpa [prefixWord, tailWord_782730, baseEnd_782730] using wordTrace_append hprefix tailTrace_782730
  have hstable : (prefixWord ++ tailWord_782730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782730).length < 2 ^ (prefixWord ++ tailWord_782730).sum := by decide
  have hdescent : baseEnd_782730 < baseStart_782730 := by decide
  rcases family_descends (prefixWord ++ tailWord_782730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782745 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 3, 1, 5]
def baseStart_782745 : Nat := 118140960795 + 782745 * 2 ^ 59
def prefixEnd_782745 : Nat := 4983230072969 + 3 ^ 40 * 782745 * 2
def baseEnd_782745 : Nat := 401924414903645240287727

theorem tailTrace_782745 : CollatzResearch.WordTrace tailWord_782745 prefixEnd_782745 401924414903645240287727 := by
  unfold tailWord_782745
  simp only [CollatzResearch.WordTrace]
  refine ⟨28549055549256022048125689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19032703699504014698750459 28549055549256022048125689)
  ·
    refine ⟨21411791661942016536094267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28549055549256022048125689 21411791661942016536094267)
    ·
      refine ⟨32117687492913024804141401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21411791661942016536094267 32117687492913024804141401)
      ·
        refine ⟨24088265619684768603106051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32117687492913024804141401 24088265619684768603106051)
        ·
          refine ⟨36132398429527152904659077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24088265619684768603106051 36132398429527152904659077)
          ·
            refine ⟨6774824705536341169623577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36132398429527152904659077 6774824705536341169623577)
            ·
              refine ⟨5081118529152255877217683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6774824705536341169623577 5081118529152255877217683)
              ·
                refine ⟨7621677793728383815826525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5081118529152255877217683 7621677793728383815826525)
                ·
                  refine ⟨2858129172648143930934947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7621677793728383815826525 2858129172648143930934947)
                  ·
                    refine ⟨4287193758972215896402421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2858129172648143930934947 4287193758972215896402421)
                    ·
                      refine ⟨401924414903645240287727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4287193758972215896402421 401924414903645240287727)
                      ·
                        rfl

theorem cell23_782745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_782745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782745 prefixEnd_782745 := by exact prefixLift 782745
  have htrace : WordTrace (prefixWord ++ tailWord_782745) baseStart_782745 baseEnd_782745 := by
    simpa [prefixWord, tailWord_782745, baseEnd_782745] using wordTrace_append hprefix tailTrace_782745
  have hstable : (prefixWord ++ tailWord_782745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782745).length < 2 ^ (prefixWord ++ tailWord_782745).sum := by decide
  have hdescent : baseEnd_782745 < baseStart_782745 := by decide
  rcases family_descends (prefixWord ++ tailWord_782745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782752 : List Nat := [2, 1, 1, 4, 1, 4, 2, 1, 1, 6]
def baseStart_782752 : Nat := 118140960795 + 782752 * 2 ^ 59
def prefixEnd_782752 : Nat := 4983230072969 + 3 ^ 40 * 782752 * 2
def baseEnd_782752 : Nat := 133976003089408904300065

theorem tailTrace_782752 : CollatzResearch.WordTrace tailWord_782752 prefixEnd_782752 133976003089408904300065 := by
  unfold tailWord_782752
  simp only [CollatzResearch.WordTrace]
  refine ⟨14274655430115331121815255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19032873906820441495753673 14274655430115331121815255)
  ·
    refine ⟨21411983145172996682722883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14274655430115331121815255 21411983145172996682722883)
    ·
      refine ⟨32117974717759495024084325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21411983145172996682722883 32117974717759495024084325)
      ·
        refine ⟨6022120259579905317015811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32117974717759495024084325 6022120259579905317015811)
        ·
          refine ⟨9033180389369857975523717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6022120259579905317015811 9033180389369857975523717)
          ·
            refine ⟨1693721323006848370410697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9033180389369857975523717 1693721323006848370410697)
            ·
              refine ⟨1270290992255136277808023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1693721323006848370410697 1270290992255136277808023)
              ·
                refine ⟨1905436488382704416712035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1270290992255136277808023 1905436488382704416712035)
                ·
                  refine ⟨2858154732574056625068053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1905436488382704416712035 2858154732574056625068053)
                  ·
                    refine ⟨133976003089408904300065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2858154732574056625068053 133976003089408904300065)
                    ·
                      rfl

theorem cell23_782752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 1, 6].length) (baseStart_782752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782752 prefixEnd_782752 := by exact prefixLift 782752
  have htrace : WordTrace (prefixWord ++ tailWord_782752) baseStart_782752 baseEnd_782752 := by
    simpa [prefixWord, tailWord_782752, baseEnd_782752] using wordTrace_append hprefix tailTrace_782752
  have hstable : (prefixWord ++ tailWord_782752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782752).length < 2 ^ (prefixWord ++ tailWord_782752).sum := by decide
  have hdescent : baseEnd_782752 < baseStart_782752 := by decide
  rcases family_descends (prefixWord ++ tailWord_782752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782773 : List Nat := [1, 3, 3, 2, 4, 1, 2, 1, 1, 5]
def baseStart_782773 : Nat := 118140960795 + 782773 * 2 ^ 59
def prefixEnd_782773 : Nat := 4983230072969 + 3 ^ 40 * 782773 * 2
def baseEnd_782773 : Nat := 133979597453990376912533

theorem tailTrace_782773 : CollatzResearch.WordTrace tailWord_782773 prefixEnd_782773 133979597453990376912533 := by
  unfold tailWord_782773
  simp only [CollatzResearch.WordTrace]
  refine ⟨28550076793154582830144973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19033384528769721886763315 28550076793154582830144973)
  ·
    refine ⟨10706278797432968561304365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28550076793154582830144973 10706278797432968561304365)
    ·
      refine ⟨4014854549037363210489137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10706278797432968561304365 4014854549037363210489137)
      ·
        refine ⟨3011140911778022407866853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4014854549037363210489137 3011140911778022407866853)
        ·
          refine ⟨564588920958379201475035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3011140911778022407866853 564588920958379201475035)
          ·
            refine ⟨846883381437568802212553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564588920958379201475035 846883381437568802212553)
            ·
              refine ⟨635162536078176601659415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 846883381437568802212553 635162536078176601659415)
              ·
                refine ⟨952743804117264902489123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635162536078176601659415 952743804117264902489123)
                ·
                  refine ⟨1429115706175897353733685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 952743804117264902489123 1429115706175897353733685)
                  ·
                    refine ⟨133979597453990376912533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1429115706175897353733685 133979597453990376912533)
                    ·
                      rfl

theorem cell23_782773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_782773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782773 prefixEnd_782773 := by exact prefixLift 782773
  have htrace : WordTrace (prefixWord ++ tailWord_782773) baseStart_782773 baseEnd_782773 := by
    simpa [prefixWord, tailWord_782773, baseEnd_782773] using wordTrace_append hprefix tailTrace_782773
  have hstable : (prefixWord ++ tailWord_782773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782773).length < 2 ^ (prefixWord ++ tailWord_782773).sum := by decide
  have hdescent : baseEnd_782773 < baseStart_782773 := by decide
  rcases family_descends (prefixWord ++ tailWord_782773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782825 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 4, 6]
def baseStart_782825 : Nat := 118140960795 + 782825 * 2 ^ 59
def prefixEnd_782825 : Nat := 4983230072969 + 3 ^ 40 * 782825 * 2
def baseEnd_782825 : Nat := 133988497785334975762453

theorem tailTrace_782825 : CollatzResearch.WordTrace tailWord_782825 prefixEnd_782825 133988497785334975762453 := by
  unfold tailWord_782825
  simp only [CollatzResearch.WordTrace]
  refine ⟨28551973388966195711037929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19034648925977463807358619 28551973388966195711037929)
  ·
    refine ⟨21413980041724646783278447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28551973388966195711037929 21413980041724646783278447)
    ·
      refine ⟨32120970062586970174917671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21413980041724646783278447 32120970062586970174917671)
      ·
        refine ⟨48181455093880455262376507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32120970062586970174917671 48181455093880455262376507)
        ·
          refine ⟨72272182640820682893564761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48181455093880455262376507 72272182640820682893564761)
          ·
            refine ⟨54204136980615512170173571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72272182640820682893564761 54204136980615512170173571)
            ·
              refine ⟨81306205470923268255260357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54204136980615512170173571 81306205470923268255260357)
              ·
                refine ⟨15244913525798112797861317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81306205470923268255260357 15244913525798112797861317)
                ·
                  refine ⟨2858421286087146149598997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15244913525798112797861317 2858421286087146149598997)
                  ·
                    refine ⟨133988497785334975762453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2858421286087146149598997 133988497785334975762453)
                    ·
                      rfl

theorem cell23_782825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 6].length) (baseStart_782825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782825 prefixEnd_782825 := by exact prefixLift 782825
  have htrace : WordTrace (prefixWord ++ tailWord_782825) baseStart_782825 baseEnd_782825 := by
    simpa [prefixWord, tailWord_782825, baseEnd_782825] using wordTrace_append hprefix tailTrace_782825
  have hstable : (prefixWord ++ tailWord_782825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782825).length < 2 ^ (prefixWord ++ tailWord_782825).sum := by decide
  have hdescent : baseEnd_782825 < baseStart_782825 := by decide
  rcases family_descends (prefixWord ++ tailWord_782825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782875 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 8]
def baseStart_782875 : Nat := 118140960795 + 782875 * 2 ^ 59
def prefixEnd_782875 : Nat := 4983230072969 + 3 ^ 40 * 782875 * 2
def baseEnd_782875 : Nat := 401991167388729731662129

theorem tailTrace_782875 : CollatzResearch.WordTrace tailWord_782875 prefixEnd_782875 401991167388729731662129 := by
  unfold tailWord_782875
  simp only [CollatzResearch.WordTrace]
  refine ⟨28553797038785054250358079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19035864692523369500238719 28553797038785054250358079)
  ·
    refine ⟨42830695558177581375537119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28553797038785054250358079 42830695558177581375537119)
    ·
      refine ⟨64246043337266372063305679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42830695558177581375537119 64246043337266372063305679)
      ·
        refine ⟨96369065005899558094958519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64246043337266372063305679 96369065005899558094958519)
        ·
          refine ⟨144553597508849337142437779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96369065005899558094958519 144553597508849337142437779)
          ·
            refine ⟨216830396263274005713656669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144553597508849337142437779 216830396263274005713656669)
            ·
              refine ⟨81311398598727752142621251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216830396263274005713656669 81311398598727752142621251)
              ·
                refine ⟨121967097898091628213931877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81311398598727752142621251 121967097898091628213931877)
                ·
                  refine ⟨22868830855892180290112227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121967097898091628213931877 22868830855892180290112227)
                  ·
                    refine ⟨34303246283838270435168341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22868830855892180290112227 34303246283838270435168341)
                    ·
                      refine ⟨401991167388729731662129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 34303246283838270435168341 401991167388729731662129)
                      ·
                        rfl

theorem cell23_782875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 8].length) (baseStart_782875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782875 prefixEnd_782875 := by exact prefixLift 782875
  have htrace : WordTrace (prefixWord ++ tailWord_782875) baseStart_782875 baseEnd_782875 := by
    simpa [prefixWord, tailWord_782875, baseEnd_782875] using wordTrace_append hprefix tailTrace_782875
  have hstable : (prefixWord ++ tailWord_782875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782875).length < 2 ^ (prefixWord ++ tailWord_782875).sum := by decide
  have hdescent : baseEnd_782875 < baseStart_782875 := by decide
  rcases family_descends (prefixWord ++ tailWord_782875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782887 : List Nat := [1, 1, 7, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_782887 : Nat := 118140960795 + 782887 * 2 ^ 59
def prefixEnd_782887 : Nat := 4983230072969 + 3 ^ 40 * 782887 * 2
def baseEnd_782887 : Nat := 401997329156583684712075

theorem tailTrace_782887 : CollatzResearch.WordTrace tailWord_782887 prefixEnd_782887 401997329156583684712075 := by
  unfold tailWord_782887
  simp only [CollatzResearch.WordTrace]
  refine ⟨28554234714741580299794915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19036156476494386866529943 28554234714741580299794915)
  ·
    refine ⟨42831352072112370449692373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28554234714741580299794915 42831352072112370449692373)
    ·
      refine ⟨1003859814190133682414665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 42831352072112370449692373 1003859814190133682414665)
      ·
        refine ⟨752894860642600261810999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1003859814190133682414665 752894860642600261810999)
        ·
          refine ⟨1129342290963900392716499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 752894860642600261810999 1129342290963900392716499)
          ·
            refine ⟨1694013436445850589074749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1129342290963900392716499 1694013436445850589074749)
            ·
              refine ⟨635255038667193970903031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1694013436445850589074749 635255038667193970903031)
              ·
                refine ⟨952882558000790956354547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635255038667193970903031 952882558000790956354547)
                ·
                  refine ⟨1429323837001186434531821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 952882558000790956354547 1429323837001186434531821)
                  ·
                    refine ⟨535996438875444912949433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1429323837001186434531821 535996438875444912949433)
                    ·
                      refine ⟨401997329156583684712075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 535996438875444912949433 401997329156583684712075)
                      ·
                        rfl

theorem cell23_782887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_782887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782887 prefixEnd_782887 := by exact prefixLift 782887
  have htrace : WordTrace (prefixWord ++ tailWord_782887) baseStart_782887 baseEnd_782887 := by
    simpa [prefixWord, tailWord_782887, baseEnd_782887] using wordTrace_append hprefix tailTrace_782887
  have hstable : (prefixWord ++ tailWord_782887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782887).length < 2 ^ (prefixWord ++ tailWord_782887).sum := by decide
  have hdescent : baseEnd_782887 < baseStart_782887 := by decide
  rcases family_descends (prefixWord ++ tailWord_782887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782906 : List Nat := [3, 1, 1, 1, 3, 3, 4, 2, 5]
def baseStart_782906 : Nat := 118140960795 + 782906 * 2 ^ 59
def prefixEnd_782906 : Nat := 4983230072969 + 3 ^ 40 * 782906 * 2
def baseEnd_782906 : Nat := 44667453921002123374943

theorem tailTrace_782906 : CollatzResearch.WordTrace tailWord_782906 prefixEnd_782906 44667453921002123374943 := by
  unfold tailWord_782906
  simp only [CollatzResearch.WordTrace]
  refine ⟨7138731925418186636184143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19036618467781831029824381 7138731925418186636184143)
  ·
    refine ⟨10708097888127279954276215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7138731925418186636184143 10708097888127279954276215)
    ·
      refine ⟨16062146832190919931414323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10708097888127279954276215 16062146832190919931414323)
      ·
        refine ⟨24093220248286379897121485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16062146832190919931414323 24093220248286379897121485)
        ·
          refine ⟨9034957593107392461420557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24093220248286379897121485 9034957593107392461420557)
          ·
            refine ⟨3388109097415272173032709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9034957593107392461420557 3388109097415272173032709)
            ·
              refine ⟨635270455765363532443633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3388109097415272173032709 635270455765363532443633)
              ·
                refine ⟨476452841824022649332725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 635270455765363532443633 476452841824022649332725)
                ·
                  refine ⟨44667453921002123374943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 476452841824022649332725 44667453921002123374943)
                  ·
                    rfl

theorem cell23_782906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2, 5].length) (baseStart_782906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782906 prefixEnd_782906 := by exact prefixLift 782906
  have htrace : WordTrace (prefixWord ++ tailWord_782906) baseStart_782906 baseEnd_782906 := by
    simpa [prefixWord, tailWord_782906, baseEnd_782906] using wordTrace_append hprefix tailTrace_782906
  have hstable : (prefixWord ++ tailWord_782906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782906).length < 2 ^ (prefixWord ++ tailWord_782906).sum := by decide
  have hdescent : baseEnd_782906 < baseStart_782906 := by decide
  rcases family_descends (prefixWord ++ tailWord_782906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782912 : List Nat := [2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 5]
def baseStart_782912 : Nat := 118140960795 + 782912 * 2 ^ 59
def prefixEnd_782912 : Nat := 4983230072969 + 3 ^ 40 * 782912 * 2
def baseEnd_782912 : Nat := 402010166172946086899459

theorem tailTrace_782912 : CollatzResearch.WordTrace tailWord_782912 prefixEnd_782912 402010166172946086899459 := by
  unfold tailWord_782912
  simp only [CollatzResearch.WordTrace]
  refine ⟨14277573269825504784727495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19036764359767339712969993 14277573269825504784727495)
  ·
    refine ⟨21416359904738257177091243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14277573269825504784727495 21416359904738257177091243)
    ·
      refine ⟨32124539857107385765636865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21416359904738257177091243 32124539857107385765636865)
      ·
        refine ⟨24093404892830539324227649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32124539857107385765636865 24093404892830539324227649)
        ·
          refine ⟨18070053669622904493170737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24093404892830539324227649 18070053669622904493170737)
          ·
            refine ⟨13552540252217178369878053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18070053669622904493170737 13552540252217178369878053)
            ·
              refine ⟨2541101297290720944352135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13552540252217178369878053 2541101297290720944352135)
              ·
                refine ⟨3811651945936081416528203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2541101297290720944352135 3811651945936081416528203)
                ·
                  refine ⟨5717477918904122124792305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3811651945936081416528203 5717477918904122124792305)
                  ·
                    refine ⟨4288108439178091593594229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5717477918904122124792305 4288108439178091593594229)
                    ·
                      refine ⟨402010166172946086899459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4288108439178091593594229 402010166172946086899459)
                      ·
                        rfl

theorem cell23_782912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_782912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782912 prefixEnd_782912 := by exact prefixLift 782912
  have htrace : WordTrace (prefixWord ++ tailWord_782912) baseStart_782912 baseEnd_782912 := by
    simpa [prefixWord, tailWord_782912, baseEnd_782912] using wordTrace_append hprefix tailTrace_782912
  have hstable : (prefixWord ++ tailWord_782912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782912).length < 2 ^ (prefixWord ++ tailWord_782912).sum := by decide
  have hdescent : baseEnd_782912 < baseStart_782912 := by decide
  rcases family_descends (prefixWord ++ tailWord_782912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782959 : List Nat := [1, 1, 2, 1, 3, 2, 2, 4, 2, 2, 3]
def baseStart_782959 : Nat := 118140960795 + 782959 * 2 ^ 59
def prefixEnd_782959 : Nat := 4983230072969 + 3 ^ 40 * 782959 * 2
def baseEnd_782959 : Nat := 402034299763707403011743

theorem tailTrace_782959 : CollatzResearch.WordTrace tailWord_782959 prefixEnd_782959 402034299763707403011743 := by
  unfold tailWord_782959
  simp only [CollatzResearch.WordTrace]
  refine ⟨28556860770480736596415931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19037907180320491064277287 28556860770480736596415931)
  ·
    refine ⟨42835291155721104894623897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28556860770480736596415931 42835291155721104894623897)
    ·
      refine ⟨32126468366790828670967923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42835291155721104894623897 32126468366790828670967923)
      ·
        refine ⟨48189702550186243006451885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32126468366790828670967923 48189702550186243006451885)
        ·
          refine ⟨18071138456319841127419457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48189702550186243006451885 18071138456319841127419457)
          ·
            refine ⟨13553353842239880845564593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18071138456319841127419457 13553353842239880845564593)
            ·
              refine ⟨10165015381679910634173445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13553353842239880845564593 10165015381679910634173445)
              ·
                refine ⟨1905940384064983243907521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10165015381679910634173445 1905940384064983243907521)
                ·
                  refine ⟨1429455288048737432930641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1905940384064983243907521 1429455288048737432930641)
                  ·
                    refine ⟨1072091466036553074697981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1429455288048737432930641 1072091466036553074697981)
                    ·
                      refine ⟨402034299763707403011743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1072091466036553074697981 402034299763707403011743)
                      ·
                        rfl

theorem cell23_782959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2, 3].length) (baseStart_782959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782959 prefixEnd_782959 := by exact prefixLift 782959
  have htrace : WordTrace (prefixWord ++ tailWord_782959) baseStart_782959 baseEnd_782959 := by
    simpa [prefixWord, tailWord_782959, baseEnd_782959] using wordTrace_append hprefix tailTrace_782959
  have hstable : (prefixWord ++ tailWord_782959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782959).length < 2 ^ (prefixWord ++ tailWord_782959).sum := by decide
  have hdescent : baseEnd_782959 < baseStart_782959 := by decide
  rcases family_descends (prefixWord ++ tailWord_782959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783023 : List Nat := [1, 1, 2, 1, 2, 7, 1, 1, 3, 1, 3]
def baseStart_783023 : Nat := 118140960795 + 783023 * 2 ^ 59
def prefixEnd_783023 : Nat := 4983230072969 + 3 ^ 40 * 783023 * 2
def baseEnd_783023 : Nat := 402067162525595152611449

theorem tailTrace_783023 : CollatzResearch.WordTrace tailWord_783023 prefixEnd_783023 402067162525595152611449 := by
  unfold tailWord_783023
  simp only [CollatzResearch.WordTrace]
  refine ⟨28559195042248875526745723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19039463361499250351163815 28559195042248875526745723)
  ·
    refine ⟨42838792563373313290118585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28559195042248875526745723 42838792563373313290118585)
    ·
      refine ⟨32129094422529984967588939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42838792563373313290118585 32129094422529984967588939)
      ·
        refine ⟨48193641633794977451383409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32129094422529984967588939 48193641633794977451383409)
        ·
          refine ⟨36145231225346233088537557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48193641633794977451383409 36145231225346233088537557)
          ·
            refine ⟨847153856844052338012599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 36145231225346233088537557 847153856844052338012599)
            ·
              refine ⟨1270730785266078507018899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 847153856844052338012599 1270730785266078507018899)
              ·
                refine ⟨1906096177899117760528349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1270730785266078507018899 1906096177899117760528349)
                ·
                  refine ⟨714786066712169160198131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1906096177899117760528349 714786066712169160198131)
                  ·
                    refine ⟨1072179100068253740297197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 714786066712169160198131 1072179100068253740297197)
                    ·
                      refine ⟨402067162525595152611449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1072179100068253740297197 402067162525595152611449)
                      ·
                        rfl

theorem cell23_783023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3, 1, 3].length) (baseStart_783023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783023 prefixEnd_783023 := by exact prefixLift 783023
  have htrace : WordTrace (prefixWord ++ tailWord_783023) baseStart_783023 baseEnd_783023 := by
    simpa [prefixWord, tailWord_783023, baseEnd_783023] using wordTrace_append hprefix tailTrace_783023
  have hstable : (prefixWord ++ tailWord_783023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783023).length < 2 ^ (prefixWord ++ tailWord_783023).sum := by decide
  have hdescent : baseEnd_783023 < baseStart_783023 := by decide
  rcases family_descends (prefixWord ++ tailWord_783023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783060 : List Nat := [2, 4, 1, 3, 2, 1, 3, 1, 1, 5]
def baseStart_783060 : Nat := 118140960795 + 783060 * 2 ^ 59
def prefixEnd_783060 : Nat := 4983230072969 + 3 ^ 40 * 783060 * 2
def baseEnd_783060 : Nat := 134028720436603835949593

theorem tailTrace_783060 : CollatzResearch.WordTrace tailWord_783060 prefixEnd_783060 134028720436603835949593 := by
  unfold tailWord_783060
  simp only [CollatzResearch.WordTrace]
  refine ⟨14280272271557415422921317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19040363028743220563895089 14280272271557415422921317)
  ·
    refine ⟨2677551050917015391797747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14280272271557415422921317 2677551050917015391797747)
    ·
      refine ⟨4016326576375523087696621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2677551050917015391797747 4016326576375523087696621)
      ·
        refine ⟨1506122466140821157886233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4016326576375523087696621 1506122466140821157886233)
        ·
          refine ⟨1129591849605615868414675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1506122466140821157886233 1129591849605615868414675)
          ·
            refine ⟨1694387774408423802622013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1129591849605615868414675 1694387774408423802622013)
            ·
              refine ⟨635395415403158925983255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1694387774408423802622013 635395415403158925983255)
              ·
                refine ⟨953093123104738388974883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635395415403158925983255 953093123104738388974883)
                ·
                  refine ⟨1429639684657107583462325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 953093123104738388974883 1429639684657107583462325)
                  ·
                    refine ⟨134028720436603835949593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1429639684657107583462325 134028720436603835949593)
                    ·
                      rfl

theorem cell23_783060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_783060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783060 prefixEnd_783060 := by exact prefixLift 783060
  have htrace : WordTrace (prefixWord ++ tailWord_783060) baseStart_783060 baseEnd_783060 := by
    simpa [prefixWord, tailWord_783060, baseEnd_783060] using wordTrace_append hprefix tailTrace_783060
  have hstable : (prefixWord ++ tailWord_783060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783060).length < 2 ^ (prefixWord ++ tailWord_783060).sum := by decide
  have hdescent : baseEnd_783060 < baseStart_783060 := by decide
  rcases family_descends (prefixWord ++ tailWord_783060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783063 : List Nat := [1, 1, 3, 2, 1, 5, 3, 1, 1, 1, 4]
def baseStart_783063 : Nat := 118140960795 + 783063 * 2 ^ 59
def prefixEnd_783063 : Nat := 4983230072969 + 3 ^ 40 * 783063 * 2
def baseEnd_783063 : Nat := 402087701751774996111265

theorem tailTrace_783063 : CollatzResearch.WordTrace tailWord_783063 prefixEnd_783063 402087701751774996111265 := by
  unfold tailWord_783063
  simp only [CollatzResearch.WordTrace]
  refine ⟨28560653962103962358201843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19040435974735974905467895 28560653962103962358201843)
  ·
    refine ⟨42840980943155943537302765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28560653962103962358201843 42840980943155943537302765)
    ·
      refine ⟨16065367853683478826488537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42840980943155943537302765 16065367853683478826488537)
      ·
        refine ⟨12049025890262609119866403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16065367853683478826488537 12049025890262609119866403)
        ·
          refine ⟨18073538835393913679799605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12049025890262609119866403 18073538835393913679799605)
          ·
            refine ⟨1694394265818179407481213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18073538835393913679799605 1694394265818179407481213)
            ·
              refine ⟨635397849681817277805455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1694394265818179407481213 635397849681817277805455)
              ·
                refine ⟨953096774522725916708183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635397849681817277805455 953096774522725916708183)
                ·
                  refine ⟨1429645161784088875062275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 953096774522725916708183 1429645161784088875062275)
                  ·
                    refine ⟨2144467742676133312593413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1429645161784088875062275 2144467742676133312593413)
                    ·
                      refine ⟨402087701751774996111265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2144467742676133312593413 402087701751774996111265)
                      ·
                        rfl

theorem cell23_783063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 1, 1, 4].length) (baseStart_783063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783063 prefixEnd_783063 := by exact prefixLift 783063
  have htrace : WordTrace (prefixWord ++ tailWord_783063) baseStart_783063 baseEnd_783063 := by
    simpa [prefixWord, tailWord_783063, baseEnd_783063] using wordTrace_append hprefix tailTrace_783063
  have hstable : (prefixWord ++ tailWord_783063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783063).length < 2 ^ (prefixWord ++ tailWord_783063).sum := by decide
  have hdescent : baseEnd_783063 < baseStart_783063 := by decide
  rcases family_descends (prefixWord ++ tailWord_783063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783073 : List Nat := [1, 2, 3, 1, 4, 2, 2, 2, 2, 4]
def baseStart_783073 : Nat := 118140960795 + 783073 * 2 ^ 59
def prefixEnd_783073 : Nat := 4983230072969 + 3 ^ 40 * 783073 * 2
def baseEnd_783073 : Nat := 134030945519439985662073

theorem tailTrace_783073 : CollatzResearch.WordTrace tailWord_783073 prefixEnd_783073 134030945519439985662073 := by
  unfold tailWord_783073
  simp only [CollatzResearch.WordTrace]
  refine ⟨28561018692067734066065873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19040679128045156044043915 28561018692067734066065873)
  ·
    refine ⟨21420764019050800549549405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28561018692067734066065873 21420764019050800549549405)
    ·
      refine ⟨8032786507144050206081027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21420764019050800549549405 8032786507144050206081027)
      ·
        refine ⟨12049179760716075309121541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8032786507144050206081027 12049179760716075309121541)
        ·
          refine ⟨2259221205134264120460289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12049179760716075309121541 2259221205134264120460289)
          ·
            refine ⟨1694415903850698090345217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2259221205134264120460289 1694415903850698090345217)
            ·
              refine ⟨1270811927888023567758913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1694415903850698090345217 1270811927888023567758913)
              ·
                refine ⟨953108945916017675819185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1270811927888023567758913 953108945916017675819185)
                ·
                  refine ⟨714831709437013256864389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 953108945916017675819185 714831709437013256864389)
                  ·
                    refine ⟨134030945519439985662073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 714831709437013256864389 134030945519439985662073)
                    ·
                      rfl

theorem cell23_783073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_783073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783073 prefixEnd_783073 := by exact prefixLift 783073
  have htrace : WordTrace (prefixWord ++ tailWord_783073) baseStart_783073 baseEnd_783073 := by
    simpa [prefixWord, tailWord_783073, baseEnd_783073] using wordTrace_append hprefix tailTrace_783073
  have hstable : (prefixWord ++ tailWord_783073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783073).length < 2 ^ (prefixWord ++ tailWord_783073).sum := by decide
  have hdescent : baseEnd_783073 < baseStart_783073 := by decide
  rcases family_descends (prefixWord ++ tailWord_783073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783086 : List Nat := [4, 1, 2, 1, 1, 5, 1, 8]
def baseStart_783086 : Nat := 118140960795 + 783086 * 2 ^ 59
def prefixEnd_783086 : Nat := 4983230072969 + 3 ^ 40 * 783086 * 2
def baseEnd_783086 : Nat := 14892574511364015041617

theorem tailTrace_783086 : CollatzResearch.WordTrace tailWord_783086 prefixEnd_783086 14892574511364015041617 := by
  unfold tailWord_783086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3570186605127579660786139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19040995227347091524192741 3570186605127579660786139)
  ·
    refine ⟨5355279907691369491179209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3570186605127579660786139 5355279907691369491179209)
    ·
      refine ⟨4016459930768527118384407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5355279907691369491179209 4016459930768527118384407)
      ·
        refine ⟨6024689896152790677576611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4016459930768527118384407 6024689896152790677576611)
        ·
          refine ⟨9037034844229186016364917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6024689896152790677576611 9037034844229186016364917)
          ·
            refine ⟨847222016646486189034211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9037034844229186016364917 847222016646486189034211)
            ·
              refine ⟨1270833024969729283551317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 847222016646486189034211 1270833024969729283551317)
              ·
                refine ⟨14892574511364015041617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1270833024969729283551317 14892574511364015041617)
                ·
                  rfl

theorem cell23_783086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 8].length) (baseStart_783086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783086 prefixEnd_783086 := by exact prefixLift 783086
  have htrace : WordTrace (prefixWord ++ tailWord_783086) baseStart_783086 baseEnd_783086 := by
    simpa [prefixWord, tailWord_783086, baseEnd_783086] using wordTrace_append hprefix tailTrace_783086
  have hstable : (prefixWord ++ tailWord_783086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783086).length < 2 ^ (prefixWord ++ tailWord_783086).sum := by decide
  have hdescent : baseEnd_783086 < baseStart_783086 := by decide
  rcases family_descends (prefixWord ++ tailWord_783086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783096 : List Nat := [2, 1, 2, 1, 1, 2, 6, 1, 1, 3, 3]
def baseStart_783096 : Nat := 118140960795 + 783096 * 2 ^ 59
def prefixEnd_783096 : Nat := 4983230072969 + 3 ^ 40 * 783096 * 2
def baseEnd_783096 : Nat := 402104646613373366998613

theorem tailTrace_783096 : CollatzResearch.WordTrace tailWord_783096 prefixEnd_783096 402104646613373366998613 := by
  unfold tailWord_783096
  simp only [CollatzResearch.WordTrace]
  refine ⟨14280928785492204497076571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19041238380656272662768761 14280928785492204497076571)
  ·
    refine ⟨21421393178238306745614857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14280928785492204497076571 21421393178238306745614857)
    ·
      refine ⟨16066044883678730059211143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21421393178238306745614857 16066044883678730059211143)
      ·
        refine ⟨24099067325518095088816715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16066044883678730059211143 24099067325518095088816715)
        ·
          refine ⟨36148600988277142633225073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24099067325518095088816715 36148600988277142633225073)
          ·
            refine ⟨27111450741207856974918805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36148600988277142633225073 27111450741207856974918805)
            ·
              refine ⟨1270849253494118295699319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27111450741207856974918805 1270849253494118295699319)
              ·
                refine ⟨1906273880241177443548979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1270849253494118295699319 1906273880241177443548979)
                ·
                  refine ⟨2859410820361766165323469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1906273880241177443548979 2859410820361766165323469)
                  ·
                    refine ⟨1072279057635662311996301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2859410820361766165323469 1072279057635662311996301)
                    ·
                      refine ⟨402104646613373366998613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1072279057635662311996301 402104646613373366998613)
                      ·
                        rfl

theorem cell23_783096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 1, 3, 3].length) (baseStart_783096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783096 prefixEnd_783096 := by exact prefixLift 783096
  have htrace : WordTrace (prefixWord ++ tailWord_783096) baseStart_783096 baseEnd_783096 := by
    simpa [prefixWord, tailWord_783096, baseEnd_783096] using wordTrace_append hprefix tailTrace_783096
  have hstable : (prefixWord ++ tailWord_783096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783096).length < 2 ^ (prefixWord ++ tailWord_783096).sum := by decide
  have hdescent : baseEnd_783096 < baseStart_783096 := by decide
  rcases family_descends (prefixWord ++ tailWord_783096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783123 : List Nat := [1, 1, 1, 2, 1, 3, 5, 3, 1, 3, 2]
def baseStart_783123 : Nat := 118140960795 + 783123 * 2 ^ 59
def prefixEnd_783123 : Nat := 4983230072969 + 3 ^ 40 * 783123 * 2
def baseEnd_783123 : Nat := 402118510591044761360989

theorem tailTrace_783123 : CollatzResearch.WordTrace tailWord_783123 prefixEnd_783123 402118510591044761360989 := by
  unfold tailWord_783123
  simp only [CollatzResearch.WordTrace]
  refine ⟨28562842341886592605386023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19041894894591061736924015 28562842341886592605386023)
  ·
    refine ⟨42844263512829888908079035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28562842341886592605386023 42844263512829888908079035)
    ·
      refine ⟨64266395269244833362118553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42844263512829888908079035 64266395269244833362118553)
      ·
        refine ⟨48199796451933625021588915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64266395269244833362118553 48199796451933625021588915)
        ·
          refine ⟨72299694677900437532383373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48199796451933625021588915 72299694677900437532383373)
          ·
            refine ⟨27112385504212664074643765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72299694677900437532383373 27112385504212664074643765)
            ·
              refine ⟨2541786141019937256997853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27112385504212664074643765 2541786141019937256997853)
              ·
                refine ⟨953169802882476471374195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2541786141019937256997853 953169802882476471374195)
                ·
                  refine ⟨1429754704323714707061293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 953169802882476471374195 1429754704323714707061293)
                  ·
                    refine ⟨536158014121393015147985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1429754704323714707061293 536158014121393015147985)
                    ·
                      refine ⟨402118510591044761360989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 536158014121393015147985 402118510591044761360989)
                      ·
                        rfl

theorem cell23_783123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 3, 2].length) (baseStart_783123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783123 prefixEnd_783123 := by exact prefixLift 783123
  have htrace : WordTrace (prefixWord ++ tailWord_783123) baseStart_783123 baseEnd_783123 := by
    simpa [prefixWord, tailWord_783123, baseEnd_783123] using wordTrace_append hprefix tailTrace_783123
  have hstable : (prefixWord ++ tailWord_783123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783123).length < 2 ^ (prefixWord ++ tailWord_783123).sum := by decide
  have hdescent : baseEnd_783123 < baseStart_783123 := by decide
  rcases family_descends (prefixWord ++ tailWord_783123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783139 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 5]
def baseStart_783139 : Nat := 118140960795 + 783139 * 2 ^ 59
def prefixEnd_783139 : Nat := 4983230072969 + 3 ^ 40 * 783139 * 2
def baseEnd_783139 : Nat := 402126726281516698760915

theorem tailTrace_783139 : CollatzResearch.WordTrace tailWord_783139 prefixEnd_783139 402126726281516698760915 := by
  unfold tailWord_783139
  simp only [CollatzResearch.WordTrace]
  refine ⟨28563425909828627337968471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19042283939885751558645647 28563425909828627337968471)
  ·
    refine ⟨42845138864742941006952707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28563425909828627337968471 42845138864742941006952707)
    ·
      refine ⟨64267708297114411510429061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42845138864742941006952707 64267708297114411510429061)
      ·
        refine ⟨12050195305708952158205449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64267708297114411510429061 12050195305708952158205449)
        ·
          refine ⟨9037646479281714118654087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12050195305708952158205449 9037646479281714118654087)
          ·
            refine ⟨13556469718922571177981131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9037646479281714118654087 13556469718922571177981131)
            ·
              refine ⟨20334704578383856766971697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13556469718922571177981131 20334704578383856766971697)
              ·
                refine ⟨15251028433787892575228773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20334704578383856766971697 15251028433787892575228773)
                ·
                  refine ⟨2859567831335229857855395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15251028433787892575228773 2859567831335229857855395)
                  ·
                    refine ⟨4289351747002844786783093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2859567831335229857855395 4289351747002844786783093)
                    ·
                      refine ⟨402126726281516698760915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4289351747002844786783093 402126726281516698760915)
                      ·
                        rfl

theorem cell23_783139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_783139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783139 prefixEnd_783139 := by exact prefixLift 783139
  have htrace : WordTrace (prefixWord ++ tailWord_783139) baseStart_783139 baseEnd_783139 := by
    simpa [prefixWord, tailWord_783139, baseEnd_783139] using wordTrace_append hprefix tailTrace_783139
  have hstable : (prefixWord ++ tailWord_783139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783139).length < 2 ^ (prefixWord ++ tailWord_783139).sum := by decide
  have hdescent : baseEnd_783139 < baseStart_783139 := by decide
  rcases family_descends (prefixWord ++ tailWord_783139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783159 : List Nat := [1, 1, 3, 1, 2, 1, 3, 4, 7]
def baseStart_783159 : Nat := 118140960795 + 783159 * 2 ^ 59
def prefixEnd_783159 : Nat := 4983230072969 + 3 ^ 40 * 783159 * 2
def baseEnd_783159 : Nat := 44681888432734068945647

theorem tailTrace_783159 : CollatzResearch.WordTrace tailWord_783159 prefixEnd_783159 44681888432734068945647 := by
  unfold tailWord_783159
  simp only [CollatzResearch.WordTrace]
  refine ⟨28564155369756170753696531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19042770246504113835797687 28564155369756170753696531)
  ·
    refine ⟨42846233054634256130544797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28564155369756170753696531 42846233054634256130544797)
    ·
      refine ⟨16067337395487846048954299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42846233054634256130544797 16067337395487846048954299)
      ·
        refine ⟨24101006093231769073431449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16067337395487846048954299 24101006093231769073431449)
        ·
          refine ⟨18075754569923826805073587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24101006093231769073431449 18075754569923826805073587)
          ·
            refine ⟨27113631854885740207610381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18075754569923826805073587 27113631854885740207610381)
            ·
              refine ⟨10167611945582152577853893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27113631854885740207610381 10167611945582152577853893)
              ·
                refine ⟨1906427239796653608347605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10167611945582152577853893 1906427239796653608347605)
                ·
                  refine ⟨44681888432734068945647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1906427239796653608347605 44681888432734068945647)
                  ·
                    rfl

theorem cell23_783159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 7].length) (baseStart_783159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783159 prefixEnd_783159 := by exact prefixLift 783159
  have htrace : WordTrace (prefixWord ++ tailWord_783159) baseStart_783159 baseEnd_783159 := by
    simpa [prefixWord, tailWord_783159, baseEnd_783159] using wordTrace_append hprefix tailTrace_783159
  have hstable : (prefixWord ++ tailWord_783159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783159).length < 2 ^ (prefixWord ++ tailWord_783159).sum := by decide
  have hdescent : baseEnd_783159 < baseStart_783159 := by decide
  rcases family_descends (prefixWord ++ tailWord_783159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783204 : List Nat := [2, 3, 1, 1, 4, 3, 2, 1, 2, 2, 2]
def baseStart_783204 : Nat := 118140960795 + 783204 * 2 ^ 59
def prefixEnd_783204 : Nat := 4983230072969 + 3 ^ 40 * 783204 * 2
def baseEnd_783204 : Nat := 402160102524058944448117

theorem tailTrace_783204 : CollatzResearch.WordTrace tailWord_783204 prefixEnd_783204 402160102524058944448117 := by
  unfold tailWord_783204
  simp only [CollatzResearch.WordTrace]
  refine ⟨14282898327296571719542333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19043864436395428959389777 14282898327296571719542333)
  ·
    refine ⟨5356086872736214394828375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14282898327296571719542333 5356086872736214394828375)
    ·
      refine ⟨8034130309104321592242563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5356086872736214394828375 8034130309104321592242563)
      ·
        refine ⟨12051195463656482388363845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8034130309104321592242563 12051195463656482388363845)
        ·
          refine ⟨2259599149435590447818221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12051195463656482388363845 2259599149435590447818221)
          ·
            refine ⟨847349681038346417931833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2259599149435590447818221 847349681038346417931833)
            ·
              refine ⟨635512260778759813448875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 847349681038346417931833 635512260778759813448875)
              ·
                refine ⟨953268391168139720173313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635512260778759813448875 953268391168139720173313)
                ·
                  refine ⟨714951293376104790129985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 953268391168139720173313 714951293376104790129985)
                  ·
                    refine ⟨536213470032078592597489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 714951293376104790129985 536213470032078592597489)
                    ·
                      refine ⟨402160102524058944448117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 536213470032078592597489 402160102524058944448117)
                      ·
                        rfl

theorem cell23_783204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 2, 2, 2].length) (baseStart_783204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783204 prefixEnd_783204 := by exact prefixLift 783204
  have htrace : WordTrace (prefixWord ++ tailWord_783204) baseStart_783204 baseEnd_783204 := by
    simpa [prefixWord, tailWord_783204, baseEnd_783204] using wordTrace_append hprefix tailTrace_783204
  have hstable : (prefixWord ++ tailWord_783204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783204).length < 2 ^ (prefixWord ++ tailWord_783204).sum := by decide
  have hdescent : baseEnd_783204 < baseStart_783204 := by decide
  rcases family_descends (prefixWord ++ tailWord_783204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783219 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 2, 8]
def baseStart_783219 : Nat := 118140960795 + 783219 * 2 ^ 59
def prefixEnd_783219 : Nat := 4983230072969 + 3 ^ 40 * 783219 * 2
def baseEnd_783219 : Nat := 134055934911292128586849

theorem tailTrace_783219 : CollatzResearch.WordTrace tailWord_783219 prefixEnd_783219 134055934911292128586849 := by
  unfold tailWord_783219
  simp only [CollatzResearch.WordTrace]
  refine ⟨28566343749538801000880711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19044229166359200667253807 28566343749538801000880711)
  ·
    refine ⟨42849515624308201501321067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28566343749538801000880711 42849515624308201501321067)
    ·
      refine ⟨64274273436462302251981601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42849515624308201501321067 64274273436462302251981601)
      ·
        refine ⟨48205705077346726688986201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64274273436462302251981601 48205705077346726688986201)
        ·
          refine ⟨36154278808010045016739651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48205705077346726688986201 36154278808010045016739651)
          ·
            refine ⟨54231418212015067525109477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36154278808010045016739651 54231418212015067525109477)
            ·
              refine ⟨10168390914752825160958027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54231418212015067525109477 10168390914752825160958027)
              ·
                refine ⟨15252586372129237741437041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10168390914752825160958027 15252586372129237741437041)
                ·
                  refine ⟨11439439779096928306077781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15252586372129237741437041 11439439779096928306077781)
                  ·
                    refine ⟨134055934911292128586849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11439439779096928306077781 134055934911292128586849)
                    ·
                      rfl

theorem cell23_783219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 8].length) (baseStart_783219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783219 prefixEnd_783219 := by exact prefixLift 783219
  have htrace : WordTrace (prefixWord ++ tailWord_783219) baseStart_783219 baseEnd_783219 := by
    simpa [prefixWord, tailWord_783219, baseEnd_783219] using wordTrace_append hprefix tailTrace_783219
  have hstable : (prefixWord ++ tailWord_783219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783219).length < 2 ^ (prefixWord ++ tailWord_783219).sum := by decide
  have hdescent : baseEnd_783219 < baseStart_783219 := by decide
  rcases family_descends (prefixWord ++ tailWord_783219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783276 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 3]
def baseStart_783276 : Nat := 118140960795 + 783276 * 2 ^ 59
def prefixEnd_783276 : Nat := 4983230072969 + 3 ^ 40 * 783276 * 2
def baseEnd_783276 : Nat := 402197073131182662747785

theorem tailTrace_783276 : CollatzResearch.WordTrace tailWord_783276 prefixEnd_783276 402197073131182662747785 := by
  unfold tailWord_783276
  simp only [CollatzResearch.WordTrace]
  refine ⟨14284211355166149867852841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19045615140221533157137121 14284211355166149867852841)
  ·
    refine ⟨10713158516374612400889631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14284211355166149867852841 10713158516374612400889631)
    ·
      refine ⟨16069737774561918601334447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10713158516374612400889631 16069737774561918601334447)
      ·
        refine ⟨24104606661842877902001671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16069737774561918601334447 24104606661842877902001671)
        ·
          refine ⟨36156909992764316853002507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24104606661842877902001671 36156909992764316853002507)
          ·
            refine ⟨54235364989146475279503761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36156909992764316853002507 54235364989146475279503761)
            ·
              refine ⟨40676523741859856459627821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54235364989146475279503761 40676523741859856459627821)
              ·
                refine ⟨15253696403197446172360433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40676523741859856459627821 15253696403197446172360433)
                ·
                  refine ⟨11440272302398084629270325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15253696403197446172360433 11440272302398084629270325)
                  ·
                    refine ⟨1072525528349820433994093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11440272302398084629270325 1072525528349820433994093)
                    ·
                      refine ⟨402197073131182662747785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1072525528349820433994093 402197073131182662747785)
                      ·
                        rfl

theorem cell23_783276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 3].length) (baseStart_783276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783276 prefixEnd_783276 := by exact prefixLift 783276
  have htrace : WordTrace (prefixWord ++ tailWord_783276) baseStart_783276 baseEnd_783276 := by
    simpa [prefixWord, tailWord_783276, baseEnd_783276] using wordTrace_append hprefix tailTrace_783276
  have hstable : (prefixWord ++ tailWord_783276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783276).length < 2 ^ (prefixWord ++ tailWord_783276).sum := by decide
  have hdescent : baseEnd_783276 < baseStart_783276 := by decide
  rcases family_descends (prefixWord ++ tailWord_783276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783300 : List Nat := [2, 3, 3, 3, 1, 1, 1, 1, 8]
def baseStart_783300 : Nat := 118140960795 + 783300 * 2 ^ 59
def prefixEnd_783300 : Nat := 4983230072969 + 3 ^ 40 * 783300 * 2
def baseEnd_783300 : Nat := 44689932962987840983075

theorem tailTrace_783300 : CollatzResearch.WordTrace tailWord_783300 prefixEnd_783300 44689932962987840983075 := by
  unfold tailWord_783300
  simp only [CollatzResearch.WordTrace]
  refine ⟨14284649031122675917289677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19046198708163567889719569 14284649031122675917289677)
  ·
    refine ⟨5356743386671003468983629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14284649031122675917289677 5356743386671003468983629)
    ·
      refine ⟨2008778770001626300868861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5356743386671003468983629 2008778770001626300868861)
      ·
        refine ⟨753292038750609862825823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2008778770001626300868861 753292038750609862825823)
        ·
          refine ⟨1129938058125914794238735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 753292038750609862825823 1129938058125914794238735)
          ·
            refine ⟨1694907087188872191358103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1129938058125914794238735 1694907087188872191358103)
            ·
              refine ⟨2542360630783308287037155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1694907087188872191358103 2542360630783308287037155)
              ·
                refine ⟨3813540946174962430555733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2542360630783308287037155 3813540946174962430555733)
                ·
                  refine ⟨44689932962987840983075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3813540946174962430555733 44689932962987840983075)
                  ·
                    rfl

theorem cell23_783300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 8].length) (baseStart_783300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783300 prefixEnd_783300 := by exact prefixLift 783300
  have htrace : WordTrace (prefixWord ++ tailWord_783300) baseStart_783300 baseEnd_783300 := by
    simpa [prefixWord, tailWord_783300, baseEnd_783300] using wordTrace_append hprefix tailTrace_783300
  have hstable : (prefixWord ++ tailWord_783300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783300).length < 2 ^ (prefixWord ++ tailWord_783300).sum := by decide
  have hdescent : baseEnd_783300 < baseStart_783300 := by decide
  rcases family_descends (prefixWord ++ tailWord_783300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783310 : List Nat := [4, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3]
def baseStart_783310 : Nat := 118140960795 + 783310 * 2 ^ 59
def prefixEnd_783310 : Nat := 4983230072969 + 3 ^ 40 * 783310 * 2
def baseEnd_783310 : Nat := 402214531473435529722629

theorem tailTrace_783310 : CollatzResearch.WordTrace tailWord_783310 prefixEnd_783310 402214531473435529722629 := by
  unfold tailWord_783310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3571207849026140442805423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19046441861472749028295589 3571207849026140442805423)
  ·
    refine ⟨5356811773539210664208135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3571207849026140442805423 5356811773539210664208135)
    ·
      refine ⟨8035217660308815996312203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5356811773539210664208135 8035217660308815996312203)
      ·
        refine ⟨12052826490463223994468305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8035217660308815996312203 12052826490463223994468305)
        ·
          refine ⟨9039619867847417995851229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12052826490463223994468305 9039619867847417995851229)
          ·
            refine ⟨3389857450442781748444211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9039619867847417995851229 3389857450442781748444211)
            ·
              refine ⟨5084786175664172622666317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3389857450442781748444211 5084786175664172622666317)
              ·
                refine ⟨1906794815874064733499869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5084786175664172622666317 1906794815874064733499869)
                ·
                  refine ⟨715048055952774275062451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1906794815874064733499869 715048055952774275062451)
                  ·
                    refine ⟨1072572083929161412593677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 715048055952774275062451 1072572083929161412593677)
                    ·
                      refine ⟨402214531473435529722629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1072572083929161412593677 402214531473435529722629)
                      ·
                        rfl

theorem cell23_783310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_783310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783310 prefixEnd_783310 := by exact prefixLift 783310
  have htrace : WordTrace (prefixWord ++ tailWord_783310) baseStart_783310 baseEnd_783310 := by
    simpa [prefixWord, tailWord_783310, baseEnd_783310] using wordTrace_append hprefix tailTrace_783310
  have hstable : (prefixWord ++ tailWord_783310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783310).length < 2 ^ (prefixWord ++ tailWord_783310).sum := by decide
  have hdescent : baseEnd_783310 < baseStart_783310 := by decide
  rcases family_descends (prefixWord ++ tailWord_783310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783343 : List Nat := [1, 1, 2, 1, 4, 3, 1, 2, 4, 4]
def baseStart_783343 : Nat := 118140960795 + 783343 * 2 ^ 59
def prefixEnd_783343 : Nat := 4983230072969 + 3 ^ 40 * 783343 * 2
def baseEnd_783343 : Nat := 134077158778344633536659

theorem tailTrace_783343 : CollatzResearch.WordTrace tailWord_783343 prefixEnd_783343 134077158778344633536659 := by
  unfold tailWord_783343
  simp only [CollatzResearch.WordTrace]
  refine ⟨28570866401089570178394683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19047244267393046785596455 28570866401089570178394683)
  ·
    refine ⟨42856299601634355267592025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28570866401089570178394683 42856299601634355267592025)
    ·
      refine ⟨32142224701225766450694019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42856299601634355267592025 32142224701225766450694019)
      ·
        refine ⟨48213337051838649676041029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32142224701225766450694019 48213337051838649676041029)
        ·
          refine ⟨9040000697219746814257693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48213337051838649676041029 9040000697219746814257693)
          ·
            refine ⟨3390000261457405055346635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9040000697219746814257693 3390000261457405055346635)
            ·
              refine ⟨5085000392186107583019953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3390000261457405055346635 5085000392186107583019953)
              ·
                refine ⟨3813750294139580687264965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5085000392186107583019953 3813750294139580687264965)
                ·
                  refine ⟨715078180151171378862181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3813750294139580687264965 715078180151171378862181)
                  ·
                    refine ⟨134077158778344633536659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 715078180151171378862181 134077158778344633536659)
                    ·
                      rfl

theorem cell23_783343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4, 4].length) (baseStart_783343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783343 prefixEnd_783343 := by exact prefixLift 783343
  have htrace : WordTrace (prefixWord ++ tailWord_783343) baseStart_783343 baseEnd_783343 := by
    simpa [prefixWord, tailWord_783343, baseEnd_783343] using wordTrace_append hprefix tailTrace_783343
  have hstable : (prefixWord ++ tailWord_783343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783343).length < 2 ^ (prefixWord ++ tailWord_783343).sum := by decide
  have hdescent : baseEnd_783343 < baseStart_783343 := by decide
  rcases family_descends (prefixWord ++ tailWord_783343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783353 : List Nat := [1, 2, 1, 3, 1, 3, 4, 1, 1, 1, 5]
def baseStart_783353 : Nat := 118140960795 + 783353 * 2 ^ 59
def prefixEnd_783353 : Nat := 4983230072969 + 3 ^ 40 * 783353 * 2
def baseEnd_783353 : Nat := 402236611141578861484931

theorem tailTrace_783353 : CollatzResearch.WordTrace tailWord_783353 prefixEnd_783353 402236611141578861484931 := by
  unfold tailWord_783353
  simp only [CollatzResearch.WordTrace]
  refine ⟨28571231131053341886258713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19047487420702227924172475 28571231131053341886258713)
  ·
    refine ⟨21428423348290006414694035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28571231131053341886258713 21428423348290006414694035)
    ·
      refine ⟨32142635022435009622041053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21428423348290006414694035 32142635022435009622041053)
      ·
        refine ⟨12053488133413128608265395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32142635022435009622041053 12053488133413128608265395)
        ·
          refine ⟨18080232200119692912398093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12053488133413128608265395 18080232200119692912398093)
          ·
            refine ⟨6780087075044884842149285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18080232200119692912398093 6780087075044884842149285)
            ·
              refine ⟨1271266326570915907902991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6780087075044884842149285 1271266326570915907902991)
              ·
                refine ⟨1906899489856373861854487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1271266326570915907902991 1906899489856373861854487)
                ·
                  refine ⟨2860349234784560792781731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1906899489856373861854487 2860349234784560792781731)
                  ·
                    refine ⟨4290523852176841189172597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2860349234784560792781731 4290523852176841189172597)
                    ·
                      refine ⟨402236611141578861484931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4290523852176841189172597 402236611141578861484931)
                      ·
                        rfl

theorem cell23_783353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_783353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783353 prefixEnd_783353 := by exact prefixLift 783353
  have htrace : WordTrace (prefixWord ++ tailWord_783353) baseStart_783353 baseEnd_783353 := by
    simpa [prefixWord, tailWord_783353, baseEnd_783353] using wordTrace_append hprefix tailTrace_783353
  have hstable : (prefixWord ++ tailWord_783353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783353).length < 2 ^ (prefixWord ++ tailWord_783353).sum := by decide
  have hdescent : baseEnd_783353 < baseStart_783353 := by decide
  rcases family_descends (prefixWord ++ tailWord_783353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783356 : List Nat := [2, 2, 2, 1, 2, 3, 11]
def baseStart_783356 : Nat := 118140960795 + 783356 * 2 ^ 59
def prefixEnd_783356 : Nat := 4983230072969 + 3 ^ 40 * 783356 * 2
def baseEnd_783356 : Nat := 4965903105969658638857

theorem tailTrace_783356 : CollatzResearch.WordTrace tailWord_783356 prefixEnd_783356 4965903105969658638857 := by
  unfold tailWord_783356
  simp only [CollatzResearch.WordTrace]
  refine ⟨14285670275021236699308961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19047560366694982265745281 14285670275021236699308961)
  ·
    refine ⟨10714252706265927524481721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14285670275021236699308961 10714252706265927524481721)
    ·
      refine ⟨8035689529699445643361291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10714252706265927524481721 8035689529699445643361291)
      ·
        refine ⟨12053534294549168465041937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8035689529699445643361291 12053534294549168465041937)
        ·
          refine ⟨9040150720911876348781453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12053534294549168465041937 9040150720911876348781453)
          ·
            refine ⟨3390056520341953630793045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9040150720911876348781453 3390056520341953630793045)
            ·
              refine ⟨4965903105969658638857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 3390056520341953630793045 4965903105969658638857)
              ·
                rfl

theorem cell23_783356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 11].length) (baseStart_783356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783356 prefixEnd_783356 := by exact prefixLift 783356
  have htrace : WordTrace (prefixWord ++ tailWord_783356) baseStart_783356 baseEnd_783356 := by
    simpa [prefixWord, tailWord_783356, baseEnd_783356] using wordTrace_append hprefix tailTrace_783356
  have hstable : (prefixWord ++ tailWord_783356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783356).length < 2 ^ (prefixWord ++ tailWord_783356).sum := by decide
  have hdescent : baseEnd_783356 < baseStart_783356 := by decide
  rcases family_descends (prefixWord ++ tailWord_783356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783417 : List Nat := [1, 2, 1, 5, 2, 1, 1, 4, 2, 1, 3]
def baseStart_783417 : Nat := 118140960795 + 783417 * 2 ^ 59
def prefixEnd_783417 : Nat := 4983230072969 + 3 ^ 40 * 783417 * 2
def baseEnd_783417 : Nat := 402269473903466611084637

theorem tailTrace_783417 : CollatzResearch.WordTrace tailWord_783417 prefixEnd_783417 402269473903466611084637 := by
  unfold tailWord_783417
  simp only [CollatzResearch.WordTrace]
  refine ⟨28573565402821480816588505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19049043601880987211059003 28573565402821480816588505)
  ·
    refine ⟨21430174052116110612441379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28573565402821480816588505 21430174052116110612441379)
    ·
      refine ⟨32145261078174165918662069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21430174052116110612441379 32145261078174165918662069)
      ·
        refine ⟨3013618226078828054874569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32145261078174165918662069 3013618226078828054874569)
        ·
          refine ⟨2260213669559121041155927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3013618226078828054874569 2260213669559121041155927)
          ·
            refine ⟨3390320504338681561733891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2260213669559121041155927 3390320504338681561733891)
            ·
              refine ⟨5085480756508022342600837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3390320504338681561733891 5085480756508022342600837)
              ·
                refine ⟨953527641845254189237657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5085480756508022342600837 953527641845254189237657)
                ·
                  refine ⟨715145731383940641928243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 953527641845254189237657 715145731383940641928243)
                  ·
                    refine ⟨1072718597075910962892365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 715145731383940641928243 1072718597075910962892365)
                    ·
                      refine ⟨402269473903466611084637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1072718597075910962892365 402269473903466611084637)
                      ·
                        rfl

theorem cell23_783417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_783417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783417 prefixEnd_783417 := by exact prefixLift 783417
  have htrace : WordTrace (prefixWord ++ tailWord_783417) baseStart_783417 baseEnd_783417 := by
    simpa [prefixWord, tailWord_783417, baseEnd_783417] using wordTrace_append hprefix tailTrace_783417
  have hstable : (prefixWord ++ tailWord_783417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783417).length < 2 ^ (prefixWord ++ tailWord_783417).sum := by decide
  have hdescent : baseEnd_783417 < baseStart_783417 := by decide
  rcases family_descends (prefixWord ++ tailWord_783417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783470 : List Nat := [4, 1, 2, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_783470 : Nat := 118140960795 + 783470 * 2 ^ 59
def prefixEnd_783470 : Nat := 4983230072969 + 3 ^ 40 * 783470 * 2
def baseEnd_783470 : Nat := 402296688378154903721893

theorem tailTrace_783470 : CollatzResearch.WordTrace tailWord_783470 prefixEnd_783470 402296688378154903721893 := by
  unfold tailWord_783470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3571937308953683858533483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19050332314419647245511909 3571937308953683858533483)
  ·
    refine ⟨5357905963430525787800225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3571937308953683858533483 5357905963430525787800225)
    ·
      refine ⟨4018429472572894340850169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5357905963430525787800225 4018429472572894340850169)
      ·
        refine ⟨3013822104429670755637627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4018429472572894340850169 3013822104429670755637627)
        ·
          refine ⟨4520733156644506133456441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3013822104429670755637627 4520733156644506133456441)
          ·
            refine ⟨3390549867483379600092331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4520733156644506133456441 3390549867483379600092331)
            ·
              refine ⟨5085824801225069400138497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3390549867483379600092331 5085824801225069400138497)
              ·
                refine ⟨3814368600918802050103873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5085824801225069400138497 3814368600918802050103873)
                ·
                  refine ⟨2860776450689101537577905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3814368600918802050103873 2860776450689101537577905)
                  ·
                    refine ⟨2145582338016826153183429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2860776450689101537577905 2145582338016826153183429)
                    ·
                      refine ⟨402296688378154903721893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2145582338016826153183429 402296688378154903721893)
                      ·
                        rfl

theorem cell23_783470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_783470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783470 prefixEnd_783470 := by exact prefixLift 783470
  have htrace : WordTrace (prefixWord ++ tailWord_783470) baseStart_783470 baseEnd_783470 := by
    simpa [prefixWord, tailWord_783470, baseEnd_783470] using wordTrace_append hprefix tailTrace_783470
  have hstable : (prefixWord ++ tailWord_783470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783470).length < 2 ^ (prefixWord ++ tailWord_783470).sum := by decide
  have hdescent : baseEnd_783470 < baseStart_783470 := by decide
  rcases family_descends (prefixWord ++ tailWord_783470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783480 : List Nat := [2, 1, 2, 1, 1, 1, 6, 4, 5]
def baseStart_783480 : Nat := 118140960795 + 783480 * 2 ^ 59
def prefixEnd_783480 : Nat := 4983230072969 + 3 ^ 40 * 783480 * 2
def baseEnd_783480 : Nat := 44700202576077762732983

theorem tailTrace_783480 : CollatzResearch.WordTrace tailWord_783480 prefixEnd_783480 44700202576077762732983 := by
  unfold tailWord_783480
  simp only [CollatzResearch.WordTrace]
  refine ⟨14287931600796621288065947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19050575467728828384087929 14287931600796621288065947)
  ·
    refine ⟨21431897401194931932098921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14287931600796621288065947 21431897401194931932098921)
    ·
      refine ⟨16073923050896198949074191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21431897401194931932098921 16073923050896198949074191)
      ·
        refine ⟨24110884576344298423611287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16073923050896198949074191 24110884576344298423611287)
        ·
          refine ⟨36166326864516447635416931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24110884576344298423611287 36166326864516447635416931)
          ·
            refine ⟨54249490296774671453125397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36166326864516447635416931 54249490296774671453125397)
            ·
              refine ⟨2542944857661312724365253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54249490296774671453125397 2542944857661312724365253)
              ·
                refine ⟨476802160811496135818485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2542944857661312724365253 476802160811496135818485)
                ·
                  refine ⟨44700202576077762732983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 476802160811496135818485 44700202576077762732983)
                  ·
                    rfl

theorem cell23_783480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4, 5].length) (baseStart_783480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783480 prefixEnd_783480 := by exact prefixLift 783480
  have htrace : WordTrace (prefixWord ++ tailWord_783480) baseStart_783480 baseEnd_783480 := by
    simpa [prefixWord, tailWord_783480, baseEnd_783480] using wordTrace_append hprefix tailTrace_783480
  have hstable : (prefixWord ++ tailWord_783480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783480).length < 2 ^ (prefixWord ++ tailWord_783480).sum := by decide
  have hdescent : baseEnd_783480 < baseStart_783480 := by decide
  rcases family_descends (prefixWord ++ tailWord_783480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783500 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 2, 5, 2]
def baseStart_783500 : Nat := 118140960795 + 783500 * 2 ^ 59
def prefixEnd_783500 : Nat := 4983230072969 + 3 ^ 40 * 783500 * 2
def baseEnd_783500 : Nat := 402312092797789786346755

theorem tailTrace_783500 : CollatzResearch.WordTrace tailWord_783500 prefixEnd_783500 402312092797789786346755 := by
  unfold tailWord_783500
  simp only [CollatzResearch.WordTrace]
  refine ⟨14288296330760392995929977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19051061774347190661239969 14288296330760392995929977)
  ·
    refine ⟨10716222248070294746947483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14288296330760392995929977 10716222248070294746947483)
    ·
      refine ⟨16074333372105442120421225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10716222248070294746947483 16074333372105442120421225)
      ·
        refine ⟨12055750029079081590315919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16074333372105442120421225 12055750029079081590315919)
        ·
          refine ⟨18083625043618622385473879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12055750029079081590315919 18083625043618622385473879)
          ·
            refine ⟨27125437565427933578210819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18083625043618622385473879 27125437565427933578210819)
            ·
              refine ⟨40688156348141900367316229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27125437565427933578210819 40688156348141900367316229)
              ·
                refine ⟨7629029315276606318871793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40688156348141900367316229 7629029315276606318871793)
                ·
                  refine ⟨5721771986457454739153845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7629029315276606318871793 5721771986457454739153845)
                  ·
                    refine ⟨536416123730386381795673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5721771986457454739153845 536416123730386381795673)
                    ·
                      refine ⟨402312092797789786346755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 536416123730386381795673 402312092797789786346755)
                      ·
                        rfl

theorem cell23_783500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 2, 5, 2].length) (baseStart_783500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783500 prefixEnd_783500 := by exact prefixLift 783500
  have htrace : WordTrace (prefixWord ++ tailWord_783500) baseStart_783500 baseEnd_783500 := by
    simpa [prefixWord, tailWord_783500, baseEnd_783500] using wordTrace_append hprefix tailTrace_783500
  have hstable : (prefixWord ++ tailWord_783500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783500).length < 2 ^ (prefixWord ++ tailWord_783500).sum := by decide
  have hdescent : baseEnd_783500 < baseStart_783500 := by decide
  rcases family_descends (prefixWord ++ tailWord_783500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783514 : List Nat := [3, 1, 1, 5, 1, 3, 1, 3, 5]
def baseStart_783514 : Nat := 118140960795 + 783514 * 2 ^ 59
def prefixEnd_783514 : Nat := 4983230072969 + 3 ^ 40 * 783514 * 2
def baseEnd_783514 : Nat := 44702142391883636841299

theorem tailTrace_783514 : CollatzResearch.WordTrace tailWord_783514 prefixEnd_783514 44702142391883636841299 := by
  unfold tailWord_783514
  simp only [CollatzResearch.WordTrace]
  refine ⟨7144275820867516595717399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19051402188980044255246397 7144275820867516595717399)
  ·
    refine ⟨10716413731301274893576099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7144275820867516595717399 10716413731301274893576099)
    ·
      refine ⟨16074620596951912340364149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10716413731301274893576099 16074620596951912340364149)
      ·
        refine ⟨1506995680964241781909139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16074620596951912340364149 1506995680964241781909139)
        ·
          refine ⟨2260493521446362672863709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1506995680964241781909139 2260493521446362672863709)
          ·
            refine ⟨847685070542386002323891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2260493521446362672863709 847685070542386002323891)
            ·
              refine ⟨1271527605813579003485837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 847685070542386002323891 1271527605813579003485837)
              ·
                refine ⟨476822852180092126307189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1271527605813579003485837 476822852180092126307189)
                ·
                  refine ⟨44702142391883636841299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 476822852180092126307189 44702142391883636841299)
                  ·
                    rfl

theorem cell23_783514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3, 5].length) (baseStart_783514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783514 prefixEnd_783514 := by exact prefixLift 783514
  have htrace : WordTrace (prefixWord ++ tailWord_783514) baseStart_783514 baseEnd_783514 := by
    simpa [prefixWord, tailWord_783514, baseEnd_783514] using wordTrace_append hprefix tailTrace_783514
  have hstable : (prefixWord ++ tailWord_783514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783514).length < 2 ^ (prefixWord ++ tailWord_783514).sum := by decide
  have hdescent : baseEnd_783514 < baseStart_783514 := by decide
  rcases family_descends (prefixWord ++ tailWord_783514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783527 : List Nat := [1, 1, 6, 2, 1, 2, 1, 2, 2, 5]
def baseStart_783527 : Nat := 118140960795 + 783527 * 2 ^ 59
def prefixEnd_783527 : Nat := 4983230072969 + 3 ^ 40 * 783527 * 2
def baseEnd_783527 : Nat := 134108652258487060236377

theorem tailTrace_783527 : CollatzResearch.WordTrace tailWord_783527 prefixEnd_783527 134108652258487060236377 := by
  unfold tailWord_783527
  simp only [CollatzResearch.WordTrace]
  refine ⟨28577577432422969603092835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19051718288281979735395223 28577577432422969603092835)
  ·
    refine ⟨42866366148634454404639253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28577577432422969603092835 42866366148634454404639253)
    ·
      refine ⟨2009360913217240050217465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42866366148634454404639253 2009360913217240050217465)
      ·
        refine ⟨1507020684912930037663099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2009360913217240050217465 1507020684912930037663099)
        ·
          refine ⟨2260531027369395056494649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1507020684912930037663099 2260531027369395056494649)
          ·
            refine ⟨1695398270527046292370987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2260531027369395056494649 1695398270527046292370987)
            ·
              refine ⟨2543097405790569438556481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1695398270527046292370987 2543097405790569438556481)
              ·
                refine ⟨1907323054342927078917361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2543097405790569438556481 1907323054342927078917361)
                ·
                  refine ⟨1430492290757195309188021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1907323054342927078917361 1430492290757195309188021)
                  ·
                    refine ⟨134108652258487060236377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1430492290757195309188021 134108652258487060236377)
                    ·
                      rfl

theorem cell23_783527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_783527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783527 prefixEnd_783527 := by exact prefixLift 783527
  have htrace : WordTrace (prefixWord ++ tailWord_783527) baseStart_783527 baseEnd_783527 := by
    simpa [prefixWord, tailWord_783527, baseEnd_783527] using wordTrace_append hprefix tailTrace_783527
  have hstable : (prefixWord ++ tailWord_783527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783527).length < 2 ^ (prefixWord ++ tailWord_783527).sum := by decide
  have hdescent : baseEnd_783527 < baseStart_783527 := by decide
  rcases family_descends (prefixWord ++ tailWord_783527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783542 : List Nat := [5, 1, 3, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_783542 : Nat := 118140960795 + 783542 * 2 ^ 59
def prefixEnd_783542 : Nat := 4983230072969 + 3 ^ 40 * 783542 * 2
def baseEnd_783542 : Nat := 402333658985278622021563

theorem tailTrace_783542 : CollatzResearch.WordTrace tailWord_783542 prefixEnd_783542 402333658985278622021563 := by
  unfold tailWord_783542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1786132782960539197805555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19052083018245751443259253 1786132782960539197805555)
  ·
    refine ⟨2679199174440808796708333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1786132782960539197805555 2679199174440808796708333)
    ·
      refine ⟨1004699690415303298765625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2679199174440808796708333 1004699690415303298765625)
      ·
        refine ⟨753524767811477474074219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1004699690415303298765625 753524767811477474074219)
        ·
          refine ⟨1130287151717216211111329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 753524767811477474074219 1130287151717216211111329)
          ·
            refine ⟨847715363787912158333497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1130287151717216211111329 847715363787912158333497)
            ·
              refine ⟨635786522840934118750123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 847715363787912158333497 635786522840934118750123)
              ·
                refine ⟨953679784261401178125185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635786522840934118750123 953679784261401178125185)
                ·
                  refine ⟨715259838196050883593889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 953679784261401178125185 715259838196050883593889)
                  ·
                    refine ⟨536444878647038162695417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 715259838196050883593889 536444878647038162695417)
                    ·
                      refine ⟨402333658985278622021563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 536444878647038162695417 402333658985278622021563)
                      ·
                        rfl

theorem cell23_783542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_783542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783542 prefixEnd_783542 := by exact prefixLift 783542
  have htrace : WordTrace (prefixWord ++ tailWord_783542) baseStart_783542 baseEnd_783542 := by
    simpa [prefixWord, tailWord_783542, baseEnd_783542] using wordTrace_append hprefix tailTrace_783542
  have hstable : (prefixWord ++ tailWord_783542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783542).length < 2 ^ (prefixWord ++ tailWord_783542).sum := by decide
  have hdescent : baseEnd_783542 < baseStart_783542 := by decide
  rcases family_descends (prefixWord ++ tailWord_783542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783591 : List Nat := [1, 1, 5, 3, 2, 1, 1, 4, 1, 4]
def baseStart_783591 : Nat := 118140960795 + 783591 * 2 ^ 59
def prefixEnd_783591 : Nat := 4983230072969 + 3 ^ 40 * 783591 * 2
def baseEnd_783591 : Nat := 134119606512449643436279

theorem tailTrace_783591 : CollatzResearch.WordTrace tailWord_783591 prefixEnd_783591 134119606512449643436279 := by
  unfold tailWord_783591
  simp only [CollatzResearch.WordTrace]
  refine ⟨28579911704191108533422627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19053274469460739022281751 28579911704191108533422627)
  ·
    refine ⟨42869867556286662800133941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28579911704191108533422627 42869867556286662800133941)
    ·
      refine ⟨4019050083401874637512557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42869867556286662800133941 4019050083401874637512557)
      ·
        refine ⟨1507143781275702989067209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4019050083401874637512557 1507143781275702989067209)
        ·
          refine ⟨1130357835956777241800407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1507143781275702989067209 1130357835956777241800407)
          ·
            refine ⟨1695536753935165862700611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1130357835956777241800407 1695536753935165862700611)
            ·
              refine ⟨2543305130902748794050917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1695536753935165862700611 2543305130902748794050917)
              ·
                refine ⟨476869712044265398884547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2543305130902748794050917 476869712044265398884547)
                ·
                  refine ⟨715304568066398098326821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 476869712044265398884547 715304568066398098326821)
                  ·
                    refine ⟨134119606512449643436279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 715304568066398098326821 134119606512449643436279)
                    ·
                      rfl

theorem cell23_783591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_783591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783591 prefixEnd_783591 := by exact prefixLift 783591
  have htrace : WordTrace (prefixWord ++ tailWord_783591) baseStart_783591 baseEnd_783591 := by
    simpa [prefixWord, tailWord_783591, baseEnd_783591] using wordTrace_append hprefix tailTrace_783591
  have hstable : (prefixWord ++ tailWord_783591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783591).length < 2 ^ (prefixWord ++ tailWord_783591).sum := by decide
  have hdescent : baseEnd_783591 < baseStart_783591 := by decide
  rcases family_descends (prefixWord ++ tailWord_783591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783593 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 4, 1, 7]
def baseStart_783593 : Nat := 118140960795 + 783593 * 2 ^ 59
def prefixEnd_783593 : Nat := 4983230072969 + 3 ^ 40 * 783593 * 2
def baseEnd_783593 : Nat := 402359846498657922483827

theorem tailTrace_783593 : CollatzResearch.WordTrace tailWord_783593 prefixEnd_783593 402359846498657922483827 := by
  unfold tailWord_783593
  simp only [CollatzResearch.WordTrace]
  refine ⟨28579984650183862874995433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19053323100122575249996955 28579984650183862874995433)
  ·
    refine ⟨21434988487637897156246575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28579984650183862874995433 21434988487637897156246575)
    ·
      refine ⟨32152482731456845734369863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21434988487637897156246575 32152482731456845734369863)
      ·
        refine ⟨48228724097185268601554795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32152482731456845734369863 48228724097185268601554795)
        ·
          refine ⟨72343086145777902902332193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48228724097185268601554795 72343086145777902902332193)
          ·
            refine ⟨54257314609333427176749145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72343086145777902902332193 54257314609333427176749145)
            ·
              refine ⟨40692985957000070382561859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54257314609333427176749145 40692985957000070382561859)
              ·
                refine ⟨61039478935500105573842789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40692985957000070382561859 61039478935500105573842789)
                ·
                  refine ⟨11444902300406269795095523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61039478935500105573842789 11444902300406269795095523)
                  ·
                    refine ⟨17167353450609404692643285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11444902300406269795095523 17167353450609404692643285)
                    ·
                      refine ⟨402359846498657922483827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 17167353450609404692643285 402359846498657922483827)
                      ·
                        rfl

theorem cell23_783593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 1, 7].length) (baseStart_783593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783593 prefixEnd_783593 := by exact prefixLift 783593
  have htrace : WordTrace (prefixWord ++ tailWord_783593) baseStart_783593 baseEnd_783593 := by
    simpa [prefixWord, tailWord_783593, baseEnd_783593] using wordTrace_append hprefix tailTrace_783593
  have hstable : (prefixWord ++ tailWord_783593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783593).length < 2 ^ (prefixWord ++ tailWord_783593).sum := by decide
  have hdescent : baseEnd_783593 < baseStart_783593 := by decide
  rcases family_descends (prefixWord ++ tailWord_783593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783614 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_783614 : Nat := 118140960795 + 783614 * 2 ^ 59
def prefixEnd_783614 : Nat := 4983230072969 + 3 ^ 40 * 783614 * 2
def baseEnd_783614 : Nat := 402370629592402340321231

theorem tailTrace_783614 : CollatzResearch.WordTrace tailWord_783614 prefixEnd_783614 402370629592402340321231 := by
  unfold tailWord_783614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3572593822888472932688737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19053833722071855641006597 3572593822888472932688737)
  ·
    refine ⟨2679445367166354699516553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3572593822888472932688737 2679445367166354699516553)
    ·
      refine ⟨2009584025374766024637415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2679445367166354699516553 2009584025374766024637415)
      ·
        refine ⟨3014376038062149036956123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2009584025374766024637415 3014376038062149036956123)
        ·
          refine ⟨4521564057093223555434185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3014376038062149036956123 4521564057093223555434185)
          ·
            refine ⟨3391173042819917666575639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4521564057093223555434185 3391173042819917666575639)
            ·
              refine ⟨5086759564229876499863459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3391173042819917666575639 5086759564229876499863459)
              ·
                refine ⟨7630139346344814749795189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5086759564229876499863459 7630139346344814749795189)
                ·
                  refine ⟨715325563719826382793299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7630139346344814749795189 715325563719826382793299)
                  ·
                    refine ⟨1072988345579739574189949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 715325563719826382793299 1072988345579739574189949)
                    ·
                      refine ⟨402370629592402340321231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1072988345579739574189949 402370629592402340321231)
                      ·
                        rfl

theorem cell23_783614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_783614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783614 prefixEnd_783614 := by exact prefixLift 783614
  have htrace : WordTrace (prefixWord ++ tailWord_783614) baseStart_783614 baseEnd_783614 := by
    simpa [prefixWord, tailWord_783614, baseEnd_783614] using wordTrace_append hprefix tailTrace_783614
  have hstable : (prefixWord ++ tailWord_783614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783614).length < 2 ^ (prefixWord ++ tailWord_783614).sum := by decide
  have hdescent : baseEnd_783614 < baseStart_783614 := by decide
  rcases family_descends (prefixWord ++ tailWord_783614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783618 : List Nat := [3, 4, 1, 1, 4, 1, 1, 1, 2, 2, 3]
def baseStart_783618 : Nat := 118140960795 + 783618 * 2 ^ 59
def prefixEnd_783618 : Nat := 4983230072969 + 3 ^ 40 * 783618 * 2
def baseEnd_783618 : Nat := 402372683515020324671213

theorem tailTrace_783618 : CollatzResearch.WordTrace tailWord_783618 prefixEnd_783618 402372683515020324671213 := by
  unfold tailWord_783618
  simp only [CollatzResearch.WordTrace]
  refine ⟨7145224118773323036163877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19053930983395528096437005 7145224118773323036163877)
  ·
    refine ⟨1339729522269998069280727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7145224118773323036163877 1339729522269998069280727)
    ·
      refine ⟨2009594283404997103921091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1339729522269998069280727 2009594283404997103921091)
      ·
        refine ⟨3014391425107495655881637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2009594283404997103921091 3014391425107495655881637)
        ·
          refine ⟨565198392207655435477807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3014391425107495655881637 565198392207655435477807)
          ·
            refine ⟨847797588311483153216711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565198392207655435477807 847797588311483153216711)
            ·
              refine ⟨1271696382467224729825067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 847797588311483153216711 1271696382467224729825067)
              ·
                refine ⟨1907544573700837094737601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1271696382467224729825067 1907544573700837094737601)
                ·
                  refine ⟨1430658430275627821053201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1907544573700837094737601 1430658430275627821053201)
                  ·
                    refine ⟨1072993822706720865789901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1430658430275627821053201 1072993822706720865789901)
                    ·
                      refine ⟨402372683515020324671213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1072993822706720865789901 402372683515020324671213)
                      ·
                        rfl

theorem cell23_783618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_783618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783618 prefixEnd_783618 := by exact prefixLift 783618
  have htrace : WordTrace (prefixWord ++ tailWord_783618) baseStart_783618 baseEnd_783618 := by
    simpa [prefixWord, tailWord_783618, baseEnd_783618] using wordTrace_append hprefix tailTrace_783618
  have hstable : (prefixWord ++ tailWord_783618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783618).length < 2 ^ (prefixWord ++ tailWord_783618).sum := by decide
  have hdescent : baseEnd_783618 < baseStart_783618 := by decide
  rcases family_descends (prefixWord ++ tailWord_783618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783624 : List Nat := [2, 1, 3, 2, 4, 1, 1, 1, 1, 5, 2]
def baseStart_783624 : Nat := 118140960795 + 783624 * 2 ^ 59
def prefixEnd_783624 : Nat := 4983230072969 + 3 ^ 40 * 783624 * 2
def baseEnd_783624 : Nat := 402375764398947301196185

theorem tailTrace_783624 : CollatzResearch.WordTrace tailWord_783624 prefixEnd_783624 402375764398947301196185 := by
  unfold tailWord_783624
  simp only [CollatzResearch.WordTrace]
  refine ⟨14290557656535777584686963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19054076875381036779582617 14290557656535777584686963)
  ·
    refine ⟨21435836484803666377030445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14290557656535777584686963 21435836484803666377030445)
    ·
      refine ⟨8038438681801374891386417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21435836484803666377030445 8038438681801374891386417)
      ·
        refine ⟨6028829011351031168539813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8038438681801374891386417 6028829011351031168539813)
        ·
          refine ⟨1130405439628318344101215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6028829011351031168539813 1130405439628318344101215)
          ·
            refine ⟨1695608159442477516151823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1130405439628318344101215 1695608159442477516151823)
            ·
              refine ⟨2543412239163716274227735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1695608159442477516151823 2543412239163716274227735)
              ·
                refine ⟨3815118358745574411341603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2543412239163716274227735 3815118358745574411341603)
                ·
                  refine ⟨5722677538118361617012405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3815118358745574411341603 5722677538118361617012405)
                  ·
                    refine ⟨536501019198596401594913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5722677538118361617012405 536501019198596401594913)
                    ·
                      refine ⟨402375764398947301196185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 536501019198596401594913 402375764398947301196185)
                      ·
                        rfl

theorem cell23_783624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_783624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783624 prefixEnd_783624 := by exact prefixLift 783624
  have htrace : WordTrace (prefixWord ++ tailWord_783624) baseStart_783624 baseEnd_783624 := by
    simpa [prefixWord, tailWord_783624, baseEnd_783624] using wordTrace_append hprefix tailTrace_783624
  have hstable : (prefixWord ++ tailWord_783624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783624).length < 2 ^ (prefixWord ++ tailWord_783624).sum := by decide
  have hdescent : baseEnd_783624 < baseStart_783624 := by decide
  rcases family_descends (prefixWord ++ tailWord_783624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783664 : List Nat := [2, 1, 1, 1, 2, 2, 7, 1, 2, 4]
def baseStart_783664 : Nat := 118140960795 + 783664 * 2 ^ 59
def prefixEnd_783664 : Nat := 4983230072969 + 3 ^ 40 * 783664 * 2
def baseEnd_783664 : Nat := 134132101208375714898667

theorem tailTrace_783664 : CollatzResearch.WordTrace tailWord_783664 prefixEnd_783664 134132101208375714898667 := by
  unfold tailWord_783664
  simp only [CollatzResearch.WordTrace]
  refine ⟨14291287116463321000415023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19055049488617761333886697 14291287116463321000415023)
  ·
    refine ⟨21436930674694981500622535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14291287116463321000415023 21436930674694981500622535)
    ·
      refine ⟨32155396012042472250933803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21436930674694981500622535 32155396012042472250933803)
      ·
        refine ⟨48233094018063708376400705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32155396012042472250933803 48233094018063708376400705)
        ·
          refine ⟨36174820513547781282300529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48233094018063708376400705 36174820513547781282300529)
          ·
            refine ⟨27131115385160835961725397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36174820513547781282300529 27131115385160835961725397)
            ·
              refine ⟨635885516839707092852939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 27131115385160835961725397 635885516839707092852939)
              ·
                refine ⟨953828275259560639279409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635885516839707092852939 953828275259560639279409)
                ·
                  refine ⟨715371206444670479459557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 953828275259560639279409 715371206444670479459557)
                  ·
                    refine ⟨134132101208375714898667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 715371206444670479459557 134132101208375714898667)
                    ·
                      rfl

theorem cell23_783664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 2, 4].length) (baseStart_783664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783664 prefixEnd_783664 := by exact prefixLift 783664
  have htrace : WordTrace (prefixWord ++ tailWord_783664) baseStart_783664 baseEnd_783664 := by
    simpa [prefixWord, tailWord_783664, baseEnd_783664] using wordTrace_append hprefix tailTrace_783664
  have hstable : (prefixWord ++ tailWord_783664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783664).length < 2 ^ (prefixWord ++ tailWord_783664).sum := by decide
  have hdescent : baseEnd_783664 < baseStart_783664 := by decide
  rcases family_descends (prefixWord ++ tailWord_783664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783667 : List Nat := [1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 4]
def baseStart_783667 : Nat := 118140960795 + 783667 * 2 ^ 59
def prefixEnd_783667 : Nat := 4983230072969 + 3 ^ 40 * 783667 * 2
def baseEnd_783667 : Nat := 402397844067090632958487

theorem tailTrace_783667 : CollatzResearch.WordTrace tailWord_783667 prefixEnd_783667 402397844067090632958487 := by
  unfold tailWord_783667
  simp only [CollatzResearch.WordTrace]
  refine ⟨28582683651915773513189255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19055122434610515675459503 28582683651915773513189255)
  ·
    refine ⟨42874025477873660269783883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28582683651915773513189255 42874025477873660269783883)
    ·
      refine ⟨64311038216810490404675825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42874025477873660269783883 64311038216810490404675825)
      ·
        refine ⟨48233278662607867803506869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64311038216810490404675825 48233278662607867803506869)
        ·
          refine ⟨4521869874619487606578769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48233278662607867803506869 4521869874619487606578769)
          ·
            refine ⟨3391402405964615704934077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4521869874619487606578769 3391402405964615704934077)
            ·
              refine ⟨1271775902236730889350279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3391402405964615704934077 1271775902236730889350279)
              ·
                refine ⟨1907663853355096334025419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1271775902236730889350279 1907663853355096334025419)
                ·
                  refine ⟨2861495780032644501038129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1907663853355096334025419 2861495780032644501038129)
                  ·
                    refine ⟨2146121835024483375778597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2861495780032644501038129 2146121835024483375778597)
                    ·
                      refine ⟨402397844067090632958487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2146121835024483375778597 402397844067090632958487)
                      ·
                        rfl

theorem cell23_783667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 4].length) (baseStart_783667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783667 prefixEnd_783667 := by exact prefixLift 783667
  have htrace : WordTrace (prefixWord ++ tailWord_783667) baseStart_783667 baseEnd_783667 := by
    simpa [prefixWord, tailWord_783667, baseEnd_783667] using wordTrace_append hprefix tailTrace_783667
  have hstable : (prefixWord ++ tailWord_783667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783667).length < 2 ^ (prefixWord ++ tailWord_783667).sum := by decide
  have hdescent : baseEnd_783667 < baseStart_783667 := by decide
  rcases family_descends (prefixWord ++ tailWord_783667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783674 : List Nat := [3, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3]
def baseStart_783674 : Nat := 118140960795 + 783674 * 2 ^ 59
def prefixEnd_783674 : Nat := 4983230072969 + 3 ^ 40 * 783674 * 2
def baseEnd_783674 : Nat := 402401438431672105570955

theorem tailTrace_783674 : CollatzResearch.WordTrace tailWord_783674 prefixEnd_783674 402401438431672105570955 := by
  unfold tailWord_783674
  simp only [CollatzResearch.WordTrace]
  refine ⟨7145734740722603427173519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19055292641926942472462717 7145734740722603427173519)
  ·
    refine ⟨10718602111083905140760279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7145734740722603427173519 10718602111083905140760279)
    ·
      refine ⟨16077903166625857711140419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10718602111083905140760279 16077903166625857711140419)
      ·
        refine ⟨24116854749938786566710629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16077903166625857711140419 24116854749938786566710629)
        ·
          refine ⟨4521910265613522481258243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24116854749938786566710629 4521910265613522481258243)
          ·
            refine ⟨6782865398420283721887365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4521910265613522481258243 6782865398420283721887365)
            ·
              refine ⟨1271787262203803197853881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6782865398420283721887365 1271787262203803197853881)
              ·
                refine ⟨953840446652852398390411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1271787262203803197853881 953840446652852398390411)
                ·
                  refine ⟨1430760669979278597585617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 953840446652852398390411 1430760669979278597585617)
                  ·
                    refine ⟨1073070502484458948189213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1430760669979278597585617 1073070502484458948189213)
                    ·
                      refine ⟨402401438431672105570955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1073070502484458948189213 402401438431672105570955)
                      ·
                        rfl

theorem cell23_783674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3].length) (baseStart_783674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783674 prefixEnd_783674 := by exact prefixLift 783674
  have htrace : WordTrace (prefixWord ++ tailWord_783674) baseStart_783674 baseEnd_783674 := by
    simpa [prefixWord, tailWord_783674, baseEnd_783674] using wordTrace_append hprefix tailTrace_783674
  have hstable : (prefixWord ++ tailWord_783674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783674).length < 2 ^ (prefixWord ++ tailWord_783674).sum := by decide
  have hdescent : baseEnd_783674 < baseStart_783674 := by decide
  rcases family_descends (prefixWord ++ tailWord_783674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783704 : List Nat := [2, 1, 2, 2, 1, 1, 4, 4, 2, 1, 3]
def baseStart_783704 : Nat := 118140960795 + 783704 * 2 ^ 59
def prefixEnd_783704 : Nat := 4983230072969 + 3 ^ 40 * 783704 * 2
def baseEnd_783704 : Nat := 402416842851306988195817

theorem tailTrace_783704 : CollatzResearch.WordTrace tailWord_783704 prefixEnd_783704 402416842851306988195817 := by
  unfold tailWord_783704
  simp only [CollatzResearch.WordTrace]
  refine ⟨14292016576390864416143083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19056022101854485888190777 14292016576390864416143083)
  ·
    refine ⟨21438024864586296624214625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14292016576390864416143083 21438024864586296624214625)
    ·
      refine ⟨16078518648439722468160969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21438024864586296624214625 16078518648439722468160969)
      ·
        refine ⟨12058888986329791851120727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16078518648439722468160969 12058888986329791851120727)
        ·
          refine ⟨18088333479494687776681091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12058888986329791851120727 18088333479494687776681091)
          ·
            refine ⟨27132500219242031665021637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18088333479494687776681091 27132500219242031665021637)
            ·
              refine ⟨5087343791107880937191557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27132500219242031665021637 5087343791107880937191557)
              ·
                refine ⟨953876960832727675723417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5087343791107880937191557 953876960832727675723417)
                ·
                  refine ⟨715407720624545756792563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 953876960832727675723417 715407720624545756792563)
                  ·
                    refine ⟨1073111580936818635188845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 715407720624545756792563 1073111580936818635188845)
                    ·
                      refine ⟨402416842851306988195817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1073111580936818635188845 402416842851306988195817)
                      ·
                        rfl

theorem cell23_783704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_783704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783704 prefixEnd_783704 := by exact prefixLift 783704
  have htrace : WordTrace (prefixWord ++ tailWord_783704) baseStart_783704 baseEnd_783704 := by
    simpa [prefixWord, tailWord_783704, baseEnd_783704] using wordTrace_append hprefix tailTrace_783704
  have hstable : (prefixWord ++ tailWord_783704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783704).length < 2 ^ (prefixWord ++ tailWord_783704).sum := by decide
  have hdescent : baseEnd_783704 < baseStart_783704 := by decide
  rcases family_descends (prefixWord ++ tailWord_783704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783744 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 6, 2, 2]
def baseStart_783744 : Nat := 118140960795 + 783744 * 2 ^ 59
def prefixEnd_783744 : Nat := 4983230072969 + 3 ^ 40 * 783744 * 2
def baseEnd_783744 : Nat := 402437382077486831695633

theorem tailTrace_783744 : CollatzResearch.WordTrace tailWord_783744 prefixEnd_783744 402437382077486831695633 := by
  unfold tailWord_783744
  simp only [CollatzResearch.WordTrace]
  refine ⟨14292746036318407831871143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19056994715091210442494857 14292746036318407831871143)
  ·
    refine ⟨21439119054477611747806715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14292746036318407831871143 21439119054477611747806715)
    ·
      refine ⟨32158678581716417621710073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21439119054477611747806715 32158678581716417621710073)
      ·
        refine ⟨24119008936287313216282555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32158678581716417621710073 24119008936287313216282555)
        ·
          refine ⟨36178513404430969824423833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24119008936287313216282555 36178513404430969824423833)
          ·
            refine ⟨27133885053323227368317875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36178513404430969824423833 27133885053323227368317875)
            ·
              refine ⟨40700827579984841052476813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27133885053323227368317875 40700827579984841052476813)
              ·
                refine ⟨15262810342494315394678805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40700827579984841052476813 15262810342494315394678805)
                ·
                  refine ⟨715444234804421034125569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15262810342494315394678805 715444234804421034125569)
                  ·
                    refine ⟨536583176103315775594177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 715444234804421034125569 536583176103315775594177)
                    ·
                      refine ⟨402437382077486831695633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 536583176103315775594177 402437382077486831695633)
                      ·
                        rfl

theorem cell23_783744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 6, 2, 2].length) (baseStart_783744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783744 prefixEnd_783744 := by exact prefixLift 783744
  have htrace : WordTrace (prefixWord ++ tailWord_783744) baseStart_783744 baseEnd_783744 := by
    simpa [prefixWord, tailWord_783744, baseEnd_783744] using wordTrace_append hprefix tailTrace_783744
  have hstable : (prefixWord ++ tailWord_783744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783744).length < 2 ^ (prefixWord ++ tailWord_783744).sum := by decide
  have hdescent : baseEnd_783744 < baseStart_783744 := by decide
  rcases family_descends (prefixWord ++ tailWord_783744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783747 : List Nat := [1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 5]
def baseStart_783747 : Nat := 118140960795 + 783747 * 2 ^ 59
def prefixEnd_783747 : Nat := 4983230072969 + 3 ^ 40 * 783747 * 2
def baseEnd_783747 : Nat := 402438922519450319958119

theorem tailTrace_783747 : CollatzResearch.WordTrace tailWord_783747 prefixEnd_783747 402438922519450319958119 := by
  unfold tailWord_783747
  simp only [CollatzResearch.WordTrace]
  refine ⟨28585601491625947176101495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19057067661083964784067663 28585601491625947176101495)
  ·
    refine ⟨42878402237438920764152243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28585601491625947176101495 42878402237438920764152243)
    ·
      refine ⟨64317603356158381146228365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42878402237438920764152243 64317603356158381146228365)
      ·
        refine ⟨24119101258559392929835637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64317603356158381146228365 24119101258559392929835637)
        ·
          refine ⟨2261165742989943087172091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24119101258559392929835637 2261165742989943087172091)
          ·
            refine ⟨3391748614484914630758137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2261165742989943087172091 3391748614484914630758137)
            ·
              refine ⟨2543811460863685973068603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3391748614484914630758137 2543811460863685973068603)
              ·
                refine ⟨3815717191295528959602905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2543811460863685973068603 3815717191295528959602905)
                ·
                  refine ⟨2861787893471646719702179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3815717191295528959602905 2861787893471646719702179)
                  ·
                    refine ⟨4292681840207470079553269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2861787893471646719702179 4292681840207470079553269)
                    ·
                      refine ⟨402438922519450319958119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4292681840207470079553269 402438922519450319958119)
                      ·
                        rfl

theorem cell23_783747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_783747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783747 prefixEnd_783747 := by exact prefixLift 783747
  have htrace : WordTrace (prefixWord ++ tailWord_783747) baseStart_783747 baseEnd_783747 := by
    simpa [prefixWord, tailWord_783747, baseEnd_783747] using wordTrace_append hprefix tailTrace_783747
  have hstable : (prefixWord ++ tailWord_783747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783747).length < 2 ^ (prefixWord ++ tailWord_783747).sum := by decide
  have hdescent : baseEnd_783747 < baseStart_783747 := by decide
  rcases family_descends (prefixWord ++ tailWord_783747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783748 : List Nat := [2, 3, 2, 1, 1, 4, 3, 1, 1, 3, 2]
def baseStart_783748 : Nat := 118140960795 + 783748 * 2 ^ 59
def prefixEnd_783748 : Nat := 4983230072969 + 3 ^ 40 * 783748 * 2
def baseEnd_783748 : Nat := 402439436000104816045615

theorem tailTrace_783748 : CollatzResearch.WordTrace tailWord_783748 prefixEnd_783748 402439436000104816045615 := by
  unfold tailWord_783748
  simp only [CollatzResearch.WordTrace]
  refine ⟨14292818982311162173443949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19057091976414882897925265 14292818982311162173443949)
  ·
    refine ⟨5359807118366685815041481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14292818982311162173443949 5359807118366685815041481)
    ·
      refine ⟨4019855338775014361281111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5359807118366685815041481 4019855338775014361281111)
      ·
        refine ⟨6029783008162521541921667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4019855338775014361281111 6029783008162521541921667)
        ·
          refine ⟨9044674512243782312882501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6029783008162521541921667 9044674512243782312882501)
          ·
            refine ⟨1695876471045709183665469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9044674512243782312882501 1695876471045709183665469)
            ·
              refine ⟨635953676642140943874551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1695876471045709183665469 635953676642140943874551)
              ·
                refine ⟨953930514963211415811827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635953676642140943874551 953930514963211415811827)
                ·
                  refine ⟨1430895772444817123717741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 953930514963211415811827 1430895772444817123717741)
                  ·
                    refine ⟨536585914666806421394153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1430895772444817123717741 536585914666806421394153)
                    ·
                      refine ⟨402439436000104816045615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 536585914666806421394153 402439436000104816045615)
                      ·
                        rfl

theorem cell23_783748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_783748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783748 prefixEnd_783748 := by exact prefixLift 783748
  have htrace : WordTrace (prefixWord ++ tailWord_783748) baseStart_783748 baseEnd_783748 := by
    simpa [prefixWord, tailWord_783748, baseEnd_783748] using wordTrace_append hprefix tailTrace_783748
  have hstable : (prefixWord ++ tailWord_783748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783748).length < 2 ^ (prefixWord ++ tailWord_783748).sum := by decide
  have hdescent : baseEnd_783748 < baseStart_783748 := by decide
  rcases family_descends (prefixWord ++ tailWord_783748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783764 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_783764 : Nat := 118140960795 + 783764 * 2 ^ 59
def prefixEnd_783764 : Nat := 4983230072969 + 3 ^ 40 * 783764 * 2
def baseEnd_783764 : Nat := 402447651690576753445541

theorem tailTrace_783764 : CollatzResearch.WordTrace tailWord_783764 prefixEnd_783764 402447651690576753445541 := by
  unfold tailWord_783764
  simp only [CollatzResearch.WordTrace]
  refine ⟨14293110766282179539735173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19057481021709572719646897 14293110766282179539735173)
  ·
    refine ⟨2679958268677908663700345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14293110766282179539735173 2679958268677908663700345)
    ·
      refine ⟨2009968701508431497775259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2679958268677908663700345 2009968701508431497775259)
      ·
        refine ⟨3014953052262647246662889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2009968701508431497775259 3014953052262647246662889)
        ·
          refine ⟨2261214789196985434997167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3014953052262647246662889 2261214789196985434997167)
          ·
            refine ⟨3391822183795478152495751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2261214789196985434997167 3391822183795478152495751)
            ·
              refine ⟨5087733275693217228743627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3391822183795478152495751 5087733275693217228743627)
              ·
                refine ⟨7631599913539825843115441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5087733275693217228743627 7631599913539825843115441)
                ·
                  refine ⟨5723699935154869382336581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7631599913539825843115441 5723699935154869382336581)
                  ·
                    refine ⟨1073193737841538009188109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5723699935154869382336581 1073193737841538009188109)
                    ·
                      refine ⟨402447651690576753445541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1073193737841538009188109 402447651690576753445541)
                      ·
                        rfl

theorem cell23_783764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_783764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783764 prefixEnd_783764 := by exact prefixLift 783764
  have htrace : WordTrace (prefixWord ++ tailWord_783764) baseStart_783764 baseEnd_783764 := by
    simpa [prefixWord, tailWord_783764, baseEnd_783764] using wordTrace_append hprefix tailTrace_783764
  have hstable : (prefixWord ++ tailWord_783764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783764).length < 2 ^ (prefixWord ++ tailWord_783764).sum := by decide
  have hdescent : baseEnd_783764 < baseStart_783764 := by decide
  rcases family_descends (prefixWord ++ tailWord_783764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783778 : List Nat := [3, 3, 1, 2, 1, 2, 2, 3, 2, 2, 2]
def baseStart_783778 : Nat := 118140960795 + 783778 * 2 ^ 59
def prefixEnd_783778 : Nat := 4983230072969 + 3 ^ 40 * 783778 * 2
def baseEnd_783778 : Nat := 402454840419739698670477

theorem tailTrace_783778 : CollatzResearch.WordTrace tailWord_783778 prefixEnd_783778 402454840419739698670477 := by
  unfold tailWord_783778
  simp only [CollatzResearch.WordTrace]
  refine ⟨7146683038628409867619997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19057821436342426313653325 7146683038628409867619997)
  ·
    refine ⟨2680006139485653700357499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7146683038628409867619997 2680006139485653700357499)
    ·
      refine ⟨4020009209228480550536249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2680006139485653700357499 4020009209228480550536249)
      ·
        refine ⟨3015006906921360412902187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4020009209228480550536249 3015006906921360412902187)
        ·
          refine ⟨4522510360382040619353281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3015006906921360412902187 4522510360382040619353281)
          ·
            refine ⟨3391882770286530464514961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4522510360382040619353281 3391882770286530464514961)
            ·
              refine ⟨2543912077714897848386221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3391882770286530464514961 2543912077714897848386221)
              ·
                refine ⟨953967029143086693144833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2543912077714897848386221 953967029143086693144833)
                ·
                  refine ⟨715475271857315019858625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 953967029143086693144833 715475271857315019858625)
                  ·
                    refine ⟨536606453892986264893969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 715475271857315019858625 536606453892986264893969)
                    ·
                      refine ⟨402454840419739698670477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 536606453892986264893969 402454840419739698670477)
                      ·
                        rfl

theorem cell23_783778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_783778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783778 prefixEnd_783778 := by exact prefixLift 783778
  have htrace : WordTrace (prefixWord ++ tailWord_783778) baseStart_783778 baseEnd_783778 := by
    simpa [prefixWord, tailWord_783778, baseEnd_783778] using wordTrace_append hprefix tailTrace_783778
  have hstable : (prefixWord ++ tailWord_783778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783778).length < 2 ^ (prefixWord ++ tailWord_783778).sum := by decide
  have hdescent : baseEnd_783778 < baseStart_783778 := by decide
  rcases family_descends (prefixWord ++ tailWord_783778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783801 : List Nat := [1, 2, 1, 4, 4, 1, 2, 3, 5]
def baseStart_783801 : Nat := 118140960795 + 783801 * 2 ^ 59
def prefixEnd_783801 : Nat := 4983230072969 + 3 ^ 40 * 783801 * 2
def baseEnd_783801 : Nat := 44718516719421456520319

theorem tailTrace_783801 : CollatzResearch.WordTrace tailWord_783801 prefixEnd_783801 44718516719421456520319 := by
  unfold tailWord_783801
  simp only [CollatzResearch.WordTrace]
  refine ⟨28587571033430314398567257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19058380688953542932378171 28587571033430314398567257)
  ·
    refine ⟨21440678275072735798925443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28587571033430314398567257 21440678275072735798925443)
    ·
      refine ⟨32161017412609103698388165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21440678275072735798925443 32161017412609103698388165)
      ·
        refine ⟨6030190764864206943447781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32161017412609103698388165 6030190764864206943447781)
        ·
          refine ⟨1130660768412038801896459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6030190764864206943447781 1130660768412038801896459)
          ·
            refine ⟨1695991152618058202844689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1130660768412038801896459 1695991152618058202844689)
            ·
              refine ⟨1271993364463543652133517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1695991152618058202844689 1271993364463543652133517)
              ·
                refine ⟨476997511673828869550069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1271993364463543652133517 476997511673828869550069)
                ·
                  refine ⟨44718516719421456520319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 476997511673828869550069 44718516719421456520319)
                  ·
                    rfl

theorem cell23_783801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3, 5].length) (baseStart_783801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783801 prefixEnd_783801 := by exact prefixLift 783801
  have htrace : WordTrace (prefixWord ++ tailWord_783801) baseStart_783801 baseEnd_783801 := by
    simpa [prefixWord, tailWord_783801, baseEnd_783801] using wordTrace_append hprefix tailTrace_783801
  have hstable : (prefixWord ++ tailWord_783801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783801).length < 2 ^ (prefixWord ++ tailWord_783801).sum := by decide
  have hdescent : baseEnd_783801 < baseStart_783801 := by decide
  rcases family_descends (prefixWord ++ tailWord_783801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783817 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 4, 1, 4]
def baseStart_783817 : Nat := 118140960795 + 783817 * 2 ^ 59
def prefixEnd_783817 : Nat := 4983230072969 + 3 ^ 40 * 783817 * 2
def baseEnd_783817 : Nat := 402474866165265046082797

theorem tailTrace_783817 : CollatzResearch.WordTrace tailWord_783817 prefixEnd_783817 402474866165265046082797 := by
  unfold tailWord_783817
  simp only [CollatzResearch.WordTrace]
  refine ⟨28588154601372349131149705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19058769734248232754099803 28588154601372349131149705)
  ·
    refine ⟨21441115951029261848362279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28588154601372349131149705 21441115951029261848362279)
    ·
      refine ⟨32161673926543892772543419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21441115951029261848362279 32161673926543892772543419)
      ·
        refine ⟨48242510889815839158815129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32161673926543892772543419 48242510889815839158815129)
        ·
          refine ⟨36181883167361879369111347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48242510889815839158815129 36181883167361879369111347)
          ·
            refine ⟨54272824751042819053667021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36181883167361879369111347 54272824751042819053667021)
            ·
              refine ⟨20352309281641057145125133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54272824751042819053667021 20352309281641057145125133)
              ·
                refine ⟨7632115980615396429421925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20352309281641057145125133 7632115980615396429421925)
                ·
                  refine ⟨1431021746365386830516611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7632115980615396429421925 1431021746365386830516611)
                  ·
                    refine ⟨2146532619548080245774917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1431021746365386830516611 2146532619548080245774917)
                    ·
                      refine ⟨402474866165265046082797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2146532619548080245774917 402474866165265046082797)
                      ·
                        rfl

theorem cell23_783817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 1, 4].length) (baseStart_783817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783817 prefixEnd_783817 := by exact prefixLift 783817
  have htrace : WordTrace (prefixWord ++ tailWord_783817) baseStart_783817 baseEnd_783817 := by
    simpa [prefixWord, tailWord_783817, baseEnd_783817] using wordTrace_append hprefix tailTrace_783817
  have hstable : (prefixWord ++ tailWord_783817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783817).length < 2 ^ (prefixWord ++ tailWord_783817).sum := by decide
  have hdescent : baseEnd_783817 < baseStart_783817 := by decide
  rcases family_descends (prefixWord ++ tailWord_783817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783854 : List Nat := [4, 1, 2, 1, 2, 1, 1, 3, 1, 4, 3]
def baseStart_783854 : Nat := 118140960795 + 783854 * 2 ^ 59
def prefixEnd_783854 : Nat := 4983230072969 + 3 ^ 40 * 783854 * 2
def baseEnd_783854 : Nat := 402493864949481401320127

theorem tailTrace_783854 : CollatzResearch.WordTrace tailWord_783854 prefixEnd_783854 402493864949481401320127 := by
  unfold tailWord_783854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3573688012779788056280827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19059669401492202966831077 3573688012779788056280827)
  ·
    refine ⟨5360532019169682084421241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3573688012779788056280827 5360532019169682084421241)
    ·
      refine ⟨4020399014377261563315931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5360532019169682084421241 4020399014377261563315931)
      ·
        refine ⟨6030598521565892344973897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4020399014377261563315931 6030598521565892344973897)
        ·
          refine ⟨4522948891174419258730423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6030598521565892344973897 4522948891174419258730423)
          ·
            refine ⟨6784423336761628888095635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4522948891174419258730423 6784423336761628888095635)
            ·
              refine ⟨10176635005142443332143453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6784423336761628888095635 10176635005142443332143453)
              ·
                refine ⟨3816238126928416249553795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10176635005142443332143453 3816238126928416249553795)
                ·
                  refine ⟨5724357190392624374330693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3816238126928416249553795 5724357190392624374330693)
                  ·
                    refine ⟨1073316973198617070187005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5724357190392624374330693 1073316973198617070187005)
                    ·
                      refine ⟨402493864949481401320127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1073316973198617070187005 402493864949481401320127)
                      ·
                        rfl

theorem cell23_783854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_783854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783854 prefixEnd_783854 := by exact prefixLift 783854
  have htrace : WordTrace (prefixWord ++ tailWord_783854) baseStart_783854 baseEnd_783854 := by
    simpa [prefixWord, tailWord_783854, baseEnd_783854] using wordTrace_append hprefix tailTrace_783854
  have hstable : (prefixWord ++ tailWord_783854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783854).length < 2 ^ (prefixWord ++ tailWord_783854).sum := by decide
  have hdescent : baseEnd_783854 < baseStart_783854 := by decide
  rcases family_descends (prefixWord ++ tailWord_783854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783857 : List Nat := [1, 2, 2, 2, 3, 2, 1, 2, 8]
def baseStart_783857 : Nat := 118140960795 + 783857 * 2 ^ 59
def prefixEnd_783857 : Nat := 4983230072969 + 3 ^ 40 * 783857 * 2
def baseEnd_783857 : Nat := 44721711710160543286957

theorem tailTrace_783857 : CollatzResearch.WordTrace tailWord_783857 prefixEnd_783857 44721711710160543286957 := by
  unfold tailWord_783857
  simp only [CollatzResearch.WordTrace]
  refine ⟨28589613521227435962605825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19059742347484957308403883 28589613521227435962605825)
  ·
    refine ⟨21442210140920576971954369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28589613521227435962605825 21442210140920576971954369)
    ·
      refine ⟨16081657605690432728965777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21442210140920576971954369 16081657605690432728965777)
      ·
        refine ⟨12061243204267824546724333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16081657605690432728965777 12061243204267824546724333)
        ·
          refine ⟨4522966201600434205021625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12061243204267824546724333 4522966201600434205021625)
          ·
            refine ⟨3392224651200325653766219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4522966201600434205021625 3392224651200325653766219)
            ·
              refine ⟨5088336976800488480649329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3392224651200325653766219 5088336976800488480649329)
              ·
                refine ⟨3816252732600366360486997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5088336976800488480649329 3816252732600366360486997)
                ·
                  refine ⟨44721711710160543286957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3816252732600366360486997 44721711710160543286957)
                  ·
                    rfl

theorem cell23_783857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 8].length) (baseStart_783857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783857 prefixEnd_783857 := by exact prefixLift 783857
  have htrace : WordTrace (prefixWord ++ tailWord_783857) baseStart_783857 baseEnd_783857 := by
    simpa [prefixWord, tailWord_783857, baseEnd_783857] using wordTrace_append hprefix tailTrace_783857
  have hstable : (prefixWord ++ tailWord_783857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783857).length < 2 ^ (prefixWord ++ tailWord_783857).sum := by decide
  have hdescent : baseEnd_783857 < baseStart_783857 := by decide
  rcases family_descends (prefixWord ++ tailWord_783857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783867 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 1, 7, 3]
def baseStart_783867 : Nat := 118140960795 + 783867 * 2 ^ 59
def prefixEnd_783867 : Nat := 4983230072969 + 3 ^ 40 * 783867 * 2
def baseEnd_783867 : Nat := 402500540197989850457567

theorem tailTrace_783867 : CollatzResearch.WordTrace tailWord_783867 prefixEnd_783867 402500540197989850457567 := by
  unfold tailWord_783867
  simp only [CollatzResearch.WordTrace]
  refine ⟨28589978251191207670469855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19059985500794138446979903 28589978251191207670469855)
  ·
    refine ⟨42884967376786811505704783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28589978251191207670469855 42884967376786811505704783)
    ·
      refine ⟨64327451065180217258557175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42884967376786811505704783 64327451065180217258557175)
      ·
        refine ⟨96491176597770325887835763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64327451065180217258557175 96491176597770325887835763)
        ·
          refine ⟨144736764896655488831753645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96491176597770325887835763 144736764896655488831753645)
          ·
            refine ⟨54276286836245808311907617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144736764896655488831753645 54276286836245808311907617)
            ·
              refine ⟨40707215127184356233930713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54276286836245808311907617 40707215127184356233930713)
              ·
                refine ⟨30530411345388267175448035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40707215127184356233930713 30530411345388267175448035)
                ·
                  refine ⟨45795617018082400763172053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30530411345388267175448035 45795617018082400763172053)
                  ·
                    refine ⟨1073334773861306267886845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45795617018082400763172053 1073334773861306267886845)
                    ·
                      refine ⟨402500540197989850457567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1073334773861306267886845 402500540197989850457567)
                      ·
                        rfl

theorem cell23_783867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7, 3].length) (baseStart_783867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783867 prefixEnd_783867 := by exact prefixLift 783867
  have htrace : WordTrace (prefixWord ++ tailWord_783867) baseStart_783867 baseEnd_783867 := by
    simpa [prefixWord, tailWord_783867, baseEnd_783867] using wordTrace_append hprefix tailTrace_783867
  have hstable : (prefixWord ++ tailWord_783867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783867).length < 2 ^ (prefixWord ++ tailWord_783867).sum := by decide
  have hdescent : baseEnd_783867 < baseStart_783867 := by decide
  rcases family_descends (prefixWord ++ tailWord_783867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783891 : List Nat := [1, 1, 1, 2, 1, 8, 2, 1, 6]
def baseStart_783891 : Nat := 118140960795 + 783891 * 2 ^ 59
def prefixEnd_783891 : Nat := 4983230072969 + 3 ^ 40 * 783891 * 2
def baseEnd_783891 : Nat := 44723651525966417395273

theorem tailTrace_783891 : CollatzResearch.WordTrace tailWord_783891 prefixEnd_783891 44723651525966417395273 := by
  unfold tailWord_783891
  simp only [CollatzResearch.WordTrace]
  refine ⟨28590853603104259769343527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19060569068736173179562351 28590853603104259769343527)
  ·
    refine ⟨42886280404656389654015291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28590853603104259769343527 42886280404656389654015291)
    ·
      refine ⟨64329420606984584481022937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42886280404656389654015291 64329420606984584481022937)
      ·
        refine ⟨48247065455238438360767203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64329420606984584481022937 48247065455238438360767203)
        ·
          refine ⟨72370598182857657541150805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48247065455238438360767203 72370598182857657541150805)
          ·
            refine ⟨848092947455363174310361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 72370598182857657541150805 848092947455363174310361)
            ·
              refine ⟨636069710591522380732771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 848092947455363174310361 636069710591522380732771)
              ·
                refine ⟨954104565887283571099157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636069710591522380732771 954104565887283571099157)
                ·
                  refine ⟨44723651525966417395273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 954104565887283571099157 44723651525966417395273)
                  ·
                    rfl

theorem cell23_783891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 6].length) (baseStart_783891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783891 prefixEnd_783891 := by exact prefixLift 783891
  have htrace : WordTrace (prefixWord ++ tailWord_783891) baseStart_783891 baseEnd_783891 := by
    simpa [prefixWord, tailWord_783891, baseEnd_783891] using wordTrace_append hprefix tailTrace_783891
  have hstable : (prefixWord ++ tailWord_783891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783891).length < 2 ^ (prefixWord ++ tailWord_783891).sum := by decide
  have hdescent : baseEnd_783891 < baseStart_783891 := by decide
  rcases family_descends (prefixWord ++ tailWord_783891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783901 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 5, 1, 3]
def baseStart_783901 : Nat := 118140960795 + 783901 * 2 ^ 59
def prefixEnd_783901 : Nat := 4983230072969 + 3 ^ 40 * 783901 * 2
def baseEnd_783901 : Nat := 402517998540242717432411

theorem tailTrace_783901 : CollatzResearch.WordTrace tailWord_783901 prefixEnd_783901 402517998540242717432411 := by
  unfold tailWord_783901
  simp only [CollatzResearch.WordTrace]
  refine ⟨28591218333068031477207557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19060812222045354318138371 28591218333068031477207557)
  ·
    refine ⟨5360853437450255901976417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28591218333068031477207557 5360853437450255901976417)
    ·
      refine ⟨4020640078087691926482313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5360853437450255901976417 4020640078087691926482313)
      ·
        refine ⟨3015480058565768944861735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4020640078087691926482313 3015480058565768944861735)
        ·
          refine ⟨4523220087848653417292603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3015480058565768944861735 4523220087848653417292603)
          ·
            refine ⟨6784830131772980125938905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4523220087848653417292603 6784830131772980125938905)
            ·
              refine ⟨5088622598829735094454179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6784830131772980125938905 5088622598829735094454179)
              ·
                refine ⟨7632933898244602641681269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5088622598829735094454179 7632933898244602641681269)
                ·
                  refine ⟨715587552960431497657619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7632933898244602641681269 715587552960431497657619)
                  ·
                    refine ⟨1073381329440647246486429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 715587552960431497657619 1073381329440647246486429)
                    ·
                      refine ⟨402517998540242717432411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1073381329440647246486429 402517998540242717432411)
                      ·
                        rfl

theorem cell23_783901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_783901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783901 prefixEnd_783901 := by exact prefixLift 783901
  have htrace : WordTrace (prefixWord ++ tailWord_783901) baseStart_783901 baseEnd_783901 := by
    simpa [prefixWord, tailWord_783901, baseEnd_783901] using wordTrace_append hprefix tailTrace_783901
  have hstable : (prefixWord ++ tailWord_783901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783901).length < 2 ^ (prefixWord ++ tailWord_783901).sum := by decide
  have hdescent : baseEnd_783901 < baseStart_783901 := by decide
  rcases family_descends (prefixWord ++ tailWord_783901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783902 : List Nat := [4, 3, 3, 1, 1, 1, 2, 1, 2, 1, 4]
def baseStart_783902 : Nat := 118140960795 + 783902 * 2 ^ 59
def prefixEnd_783902 : Nat := 4983230072969 + 3 ^ 40 * 783902 * 2
def baseEnd_783902 : Nat := 402518512020897213519907

theorem tailTrace_783902 : CollatzResearch.WordTrace tailWord_783902 prefixEnd_783902 402518512020897213519907 := by
  unfold tailWord_783902
  simp only [CollatzResearch.WordTrace]
  refine ⟨3573906850758051080999245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19060836537376272431995973 3573906850758051080999245)
  ·
    refine ⟨1340215069034269155374717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3573906850758051080999245 1340215069034269155374717)
    ·
      refine ⟨502580650887850933265519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1340215069034269155374717 502580650887850933265519)
      ·
        refine ⟨753870976331776399898279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502580650887850933265519 753870976331776399898279)
        ·
          refine ⟨1130806464497664599847419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 753870976331776399898279 1130806464497664599847419)
          ·
            refine ⟨1696209696746496899771129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1130806464497664599847419 1696209696746496899771129)
            ·
              refine ⟨1272157272559872674828347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1696209696746496899771129 1272157272559872674828347)
              ·
                refine ⟨1908235908839809012242521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1272157272559872674828347 1908235908839809012242521)
                ·
                  refine ⟨1431176931629856759181891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1908235908839809012242521 1431176931629856759181891)
                  ·
                    refine ⟨2146765397444785138772837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1431176931629856759181891 2146765397444785138772837)
                    ·
                      refine ⟨402518512020897213519907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2146765397444785138772837 402518512020897213519907)
                      ·
                        rfl

theorem cell23_783902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_783902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783902 prefixEnd_783902 := by exact prefixLift 783902
  have htrace : WordTrace (prefixWord ++ tailWord_783902) baseStart_783902 baseEnd_783902 := by
    simpa [prefixWord, tailWord_783902, baseEnd_783902] using wordTrace_append hprefix tailTrace_783902
  have hstable : (prefixWord ++ tailWord_783902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783902).length < 2 ^ (prefixWord ++ tailWord_783902).sum := by decide
  have hdescent : baseEnd_783902 < baseStart_783902 := by decide
  rcases family_descends (prefixWord ++ tailWord_783902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783935 : List Nat := [1, 1, 2, 2, 3, 3, 4, 2, 1, 1, 3]
def baseStart_783935 : Nat := 118140960795 + 783935 * 2 ^ 59
def prefixEnd_783935 : Nat := 4983230072969 + 3 ^ 40 * 783935 * 2
def baseEnd_783935 : Nat := 402535456882495584407255

theorem tailTrace_783935 : CollatzResearch.WordTrace tailWord_783935 prefixEnd_783935 402535456882495584407255 := by
  unfold tailWord_783935
  simp only [CollatzResearch.WordTrace]
  refine ⟨28592458414944855283945259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19061638943296570189296839 28592458414944855283945259)
  ·
    refine ⟨42888687622417282925917889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28592458414944855283945259 42888687622417282925917889)
    ·
      refine ⟨32166515716812962194438417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42888687622417282925917889 32166515716812962194438417)
      ·
        refine ⟨24124886787609721645828813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32166515716812962194438417 24124886787609721645828813)
        ·
          refine ⟨9046832545353645617185805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24124886787609721645828813 9046832545353645617185805)
          ·
            refine ⟨3392562204507617106444677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9046832545353645617185805 3392562204507617106444677)
            ·
              refine ⟨636105413345178207458377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3392562204507617106444677 636105413345178207458377)
              ·
                refine ⟨477079060008883655593783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 636105413345178207458377 477079060008883655593783)
                ·
                  refine ⟨715618590013325483390675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 477079060008883655593783 715618590013325483390675)
                  ·
                    refine ⟨1073427885019988225086013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 715618590013325483390675 1073427885019988225086013)
                    ·
                      refine ⟨402535456882495584407255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1073427885019988225086013 402535456882495584407255)
                      ·
                        rfl

theorem cell23_783935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2, 1, 1, 3].length) (baseStart_783935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783935 prefixEnd_783935 := by exact prefixLift 783935
  have htrace : WordTrace (prefixWord ++ tailWord_783935) baseStart_783935 baseEnd_783935 := by
    simpa [prefixWord, tailWord_783935, baseEnd_783935] using wordTrace_append hprefix tailTrace_783935
  have hstable : (prefixWord ++ tailWord_783935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783935).length < 2 ^ (prefixWord ++ tailWord_783935).sum := by decide
  have hdescent : baseEnd_783935 < baseStart_783935 := by decide
  rcases family_descends (prefixWord ++ tailWord_783935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783975 : List Nat := [1, 1, 5, 1, 1, 1, 3, 5, 1, 2, 2]
def baseStart_783975 : Nat := 118140960795 + 783975 * 2 ^ 59
def prefixEnd_783975 : Nat := 4983230072969 + 3 ^ 40 * 783975 * 2
def baseEnd_783975 : Nat := 402555996108675427907071

theorem tailTrace_783975 : CollatzResearch.WordTrace tailWord_783975 prefixEnd_783975 402555996108675427907071 := by
  unfold tailWord_783975
  simp only [CollatzResearch.WordTrace]
  refine ⟨28593917334799942115401379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19062611556533294743600919 28593917334799942115401379)
  ·
    refine ⟨42890876002199913173102069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28593917334799942115401379 42890876002199913173102069)
    ·
      refine ⟨4021019625206241859978319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42890876002199913173102069 4021019625206241859978319)
      ·
        refine ⟨6031529437809362789967479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4021019625206241859978319 6031529437809362789967479)
        ·
          refine ⟨9047294156714044184951219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6031529437809362789967479 9047294156714044184951219)
          ·
            refine ⟨13570941235071066277426829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9047294156714044184951219 13570941235071066277426829)
            ·
              refine ⟨5089102963151649854035061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13570941235071066277426829 5089102963151649854035061)
              ·
                refine ⟨477103402795467173815787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5089102963151649854035061 477103402795467173815787)
                ·
                  refine ⟨715655104193200760723681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 477103402795467173815787 715655104193200760723681)
                  ·
                    refine ⟨536741328144900570542761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 715655104193200760723681 536741328144900570542761)
                    ·
                      refine ⟨402555996108675427907071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 536741328144900570542761 402555996108675427907071)
                      ·
                        rfl

theorem cell23_783975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_783975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783975 prefixEnd_783975 := by exact prefixLift 783975
  have htrace : WordTrace (prefixWord ++ tailWord_783975) baseStart_783975 baseEnd_783975 := by
    simpa [prefixWord, tailWord_783975, baseEnd_783975] using wordTrace_append hprefix tailTrace_783975
  have hstable : (prefixWord ++ tailWord_783975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783975).length < 2 ^ (prefixWord ++ tailWord_783975).sum := by decide
  have hdescent : baseEnd_783975 < baseStart_783975 := by decide
  rcases family_descends (prefixWord ++ tailWord_783975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783978 : List Nat := [3, 1, 3, 2, 1, 3, 1, 3, 1, 2, 3]
def baseStart_783978 : Nat := 118140960795 + 783978 * 2 ^ 59
def prefixEnd_783978 : Nat := 4983230072969 + 3 ^ 40 * 783978 * 2
def baseEnd_783978 : Nat := 402557536550638916169557

theorem tailTrace_783978 : CollatzResearch.WordTrace tailWord_783978 prefixEnd_783978 402557536550638916169557 := by
  unfold tailWord_783978
  simp only [CollatzResearch.WordTrace]
  refine ⟨7148506688447268406940147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19062684502526049085173725 7148506688447268406940147)
  ·
    refine ⟨10722760032670902610410221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7148506688447268406940147 10722760032670902610410221)
    ·
      refine ⟨4021035012251588478903833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10722760032670902610410221 4021035012251588478903833)
      ·
        refine ⟨3015776259188691359177875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4021035012251588478903833 3015776259188691359177875)
        ·
          refine ⟨4523664388783037038766813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3015776259188691359177875 4523664388783037038766813)
          ·
            refine ⟨1696374145793638889537555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4523664388783037038766813 1696374145793638889537555)
            ·
              refine ⟨2544561218690458334306333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1696374145793638889537555 2544561218690458334306333)
              ·
                refine ⟨954210457008921875364875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2544561218690458334306333 954210457008921875364875)
                ·
                  refine ⟨1431315685513382813047313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 954210457008921875364875 1431315685513382813047313)
                  ·
                    refine ⟨1073486764135037109785485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1431315685513382813047313 1073486764135037109785485)
                    ·
                      refine ⟨402557536550638916169557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1073486764135037109785485 402557536550638916169557)
                      ·
                        rfl

theorem cell23_783978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_783978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_783978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_783978 prefixEnd_783978 := by exact prefixLift 783978
  have htrace : WordTrace (prefixWord ++ tailWord_783978) baseStart_783978 baseEnd_783978 := by
    simpa [prefixWord, tailWord_783978, baseEnd_783978] using wordTrace_append hprefix tailTrace_783978
  have hstable : (prefixWord ++ tailWord_783978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783978).length < 2 ^ (prefixWord ++ tailWord_783978).sum := by decide
  have hdescent : baseEnd_783978 < baseStart_783978 := by decide
  rcases family_descends (prefixWord ++ tailWord_783978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784048 : List Nat := [2, 1, 1, 1, 2, 1, 6, 1, 4, 2, 2]
def baseStart_784048 : Nat := 118140960795 + 784048 * 2 ^ 59
def prefixEnd_784048 : Nat := 4983230072969 + 3 ^ 40 * 784048 * 2
def baseEnd_784048 : Nat := 402593480196453642294235

theorem tailTrace_784048 : CollatzResearch.WordTrace tailWord_784048 prefixEnd_784048 402593480196453642294235 := by
  unfold tailWord_784048
  simp only [CollatzResearch.WordTrace]
  refine ⟨14298289931767737791404399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19064386575690317055205865 14298289931767737791404399)
  ·
    refine ⟨21447434897651606687106599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14298289931767737791404399 21447434897651606687106599)
    ·
      refine ⟨32171152346477410030659899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21447434897651606687106599 32171152346477410030659899)
      ·
        refine ⟨48256728519716115045989849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32171152346477410030659899 48256728519716115045989849)
        ·
          refine ⟨36192546389787086284492387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48256728519716115045989849 36192546389787086284492387)
          ·
            refine ⟨54288819584680629426738581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36192546389787086284492387 54288819584680629426738581)
            ·
              refine ⟨2544788418031904504378371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54288819584680629426738581 2544788418031904504378371)
              ·
                refine ⟨3817182627047856756567557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2544788418031904504378371 3817182627047856756567557)
                ·
                  refine ⟨715721742571473141856417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3817182627047856756567557 715721742571473141856417)
                  ·
                    refine ⟨536791306928604856392313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 715721742571473141856417 536791306928604856392313)
                    ·
                      refine ⟨402593480196453642294235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 536791306928604856392313 402593480196453642294235)
                      ·
                        rfl

theorem cell23_784048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 4, 2, 2].length) (baseStart_784048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784048 prefixEnd_784048 := by exact prefixLift 784048
  have htrace : WordTrace (prefixWord ++ tailWord_784048) baseStart_784048 baseEnd_784048 := by
    simpa [prefixWord, tailWord_784048, baseEnd_784048] using wordTrace_append hprefix tailTrace_784048
  have hstable : (prefixWord ++ tailWord_784048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784048).length < 2 ^ (prefixWord ++ tailWord_784048).sum := by decide
  have hdescent : baseEnd_784048 < baseStart_784048 := by decide
  rcases family_descends (prefixWord ++ tailWord_784048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784086 : List Nat := [5, 2, 1, 3, 1, 1, 3, 1, 1, 3, 2]
def baseStart_784086 : Nat := 118140960795 + 784086 * 2 ^ 59
def prefixEnd_784086 : Nat := 4983230072969 + 3 ^ 40 * 784086 * 2
def baseEnd_784086 : Nat := 402612992461324493619061

theorem tailTrace_784086 : CollatzResearch.WordTrace tailWord_784086 prefixEnd_784086 402612992461324493619061 := by
  unfold tailWord_784086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1787372864837363004543257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19065310558265205381794741 1787372864837363004543257)
  ·
    refine ⟨1340529648628022253407443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1787372864837363004543257 1340529648628022253407443)
    ·
      refine ⟨2010794472942033380111165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1340529648628022253407443 2010794472942033380111165)
      ·
        refine ⟨754047927353262517541687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2010794472942033380111165 754047927353262517541687)
        ·
          refine ⟨1131071891029893776312531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754047927353262517541687 1131071891029893776312531)
          ·
            refine ⟨1696607836544840664468797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131071891029893776312531 1696607836544840664468797)
            ·
              refine ⟨636227938704315249175799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1696607836544840664468797 636227938704315249175799)
              ·
                refine ⟨954341908056472873763699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636227938704315249175799 954341908056472873763699)
                ·
                  refine ⟨1431512862084709310645549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 954341908056472873763699 1431512862084709310645549)
                  ·
                    refine ⟨536817323281765991492081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1431512862084709310645549 536817323281765991492081)
                    ·
                      refine ⟨402612992461324493619061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 536817323281765991492081 402612992461324493619061)
                      ·
                        rfl

theorem cell23_784086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_784086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784086 prefixEnd_784086 := by exact prefixLift 784086
  have htrace : WordTrace (prefixWord ++ tailWord_784086) baseStart_784086 baseEnd_784086 := by
    simpa [prefixWord, tailWord_784086, baseEnd_784086] using wordTrace_append hprefix tailTrace_784086
  have hstable : (prefixWord ++ tailWord_784086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784086).length < 2 ^ (prefixWord ++ tailWord_784086).sum := by decide
  have hdescent : baseEnd_784086 < baseStart_784086 := by decide
  rcases family_descends (prefixWord ++ tailWord_784086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784101 : List Nat := [1, 3, 1, 4, 1, 1, 1, 4, 2, 5]
def baseStart_784101 : Nat := 118140960795 + 784101 * 2 ^ 59
def prefixEnd_784101 : Nat := 4983230072969 + 3 ^ 40 * 784101 * 2
def baseEnd_784101 : Nat := 134206898223713978310497

theorem tailTrace_784101 : CollatzResearch.WordTrace tailWord_784101 prefixEnd_784101 134206898223713978310497 := by
  unfold tailWord_784101
  simp only [CollatzResearch.WordTrace]
  refine ⟨28598512932343465634488157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19065675288228977089658771 28598512932343465634488157)
  ·
    refine ⟨10724442349628799612933059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28598512932343465634488157 10724442349628799612933059)
    ·
      refine ⟨16086663524443199419399589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10724442349628799612933059 16086663524443199419399589)
      ·
        refine ⟨3016249410833099891137423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16086663524443199419399589 3016249410833099891137423)
        ·
          refine ⟨4524374116249649836706135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3016249410833099891137423 4524374116249649836706135)
          ·
            refine ⟨6786561174374474755059203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4524374116249649836706135 6786561174374474755059203)
            ·
              refine ⟨10179841761561712132588805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6786561174374474755059203 10179841761561712132588805)
              ·
                refine ⟨1908720330292821024860401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10179841761561712132588805 1908720330292821024860401)
                ·
                  refine ⟨1431540247719615768645301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1908720330292821024860401 1431540247719615768645301)
                  ·
                    refine ⟨134206898223713978310497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1431540247719615768645301 134206898223713978310497)
                    ·
                      rfl

theorem cell23_784101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 5].length) (baseStart_784101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784101 prefixEnd_784101 := by exact prefixLift 784101
  have htrace : WordTrace (prefixWord ++ tailWord_784101) baseStart_784101 baseEnd_784101 := by
    simpa [prefixWord, tailWord_784101, baseEnd_784101] using wordTrace_append hprefix tailTrace_784101
  have hstable : (prefixWord ++ tailWord_784101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784101).length < 2 ^ (prefixWord ++ tailWord_784101).sum := by decide
  have hdescent : baseEnd_784101 < baseStart_784101 := by decide
  rcases family_descends (prefixWord ++ tailWord_784101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784131 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 5, 4]
def baseStart_784131 : Nat := 118140960795 + 784131 * 2 ^ 59
def prefixEnd_784131 : Nat := 4983230072969 + 3 ^ 40 * 784131 * 2
def baseEnd_784131 : Nat := 134212033030258939185451

theorem tailTrace_784131 : CollatzResearch.WordTrace tailWord_784131 prefixEnd_784131 134212033030258939185451 := by
  unfold tailWord_784131
  simp only [CollatzResearch.WordTrace]
  refine ⟨28599607122234780758080247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19066404748156520505386831 28599607122234780758080247)
  ·
    refine ⟨42899410683352171137120371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28599607122234780758080247 42899410683352171137120371)
    ·
      refine ⟨64349116025028256705680557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42899410683352171137120371 64349116025028256705680557)
      ·
        refine ⟨24130918509385596264630209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64349116025028256705680557 24130918509385596264630209)
        ·
          refine ⟨18098188882039197198472657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24130918509385596264630209 18098188882039197198472657)
          ·
            refine ⟨13573641661529397898854493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18098188882039197198472657 13573641661529397898854493)
            ·
              refine ⟨5090115623073524212070435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13573641661529397898854493 5090115623073524212070435)
              ·
                refine ⟨7635173434610286318105653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5090115623073524212070435 7635173434610286318105653)
                ·
                  refine ⟨715797509494714342322405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7635173434610286318105653 715797509494714342322405)
                  ·
                    refine ⟨134212033030258939185451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 715797509494714342322405 134212033030258939185451)
                    ·
                      rfl

theorem cell23_784131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5, 4].length) (baseStart_784131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784131 prefixEnd_784131 := by exact prefixLift 784131
  have htrace : WordTrace (prefixWord ++ tailWord_784131) baseStart_784131 baseEnd_784131 := by
    simpa [prefixWord, tailWord_784131, baseEnd_784131] using wordTrace_append hprefix tailTrace_784131
  have hstable : (prefixWord ++ tailWord_784131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784131).length < 2 ^ (prefixWord ++ tailWord_784131).sum := by decide
  have hdescent : baseEnd_784131 < baseStart_784131 := by decide
  rcases family_descends (prefixWord ++ tailWord_784131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784135 : List Nat := [1, 1, 4, 4, 2, 2, 1, 1, 2, 5]
def baseStart_784135 : Nat := 118140960795 + 784135 * 2 ^ 59
def prefixEnd_784135 : Nat := 4983230072969 + 3 ^ 40 * 784135 * 2
def baseEnd_784135 : Nat := 134212717671131600635445

theorem tailTrace_784135 : CollatzResearch.WordTrace tailWord_784135 prefixEnd_784135 134212717671131600635445 := by
  unfold tailWord_784135
  simp only [CollatzResearch.WordTrace]
  refine ⟨28599753014220289441225859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19066502009480192960817239 28599753014220289441225859)
  ·
    refine ⟨42899629521330434161838789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28599753014220289441225859 42899629521330434161838789)
    ·
      refine ⟨8043680535249456405344773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42899629521330434161838789 8043680535249456405344773)
      ·
        refine ⟨1508190100359273076002145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8043680535249456405344773 1508190100359273076002145)
        ·
          refine ⟨1131142575269454807001609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1508190100359273076002145 1131142575269454807001609)
          ·
            refine ⟨848356931452091105251207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1131142575269454807001609 848356931452091105251207)
            ·
              refine ⟨1272535397178136657876811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 848356931452091105251207 1272535397178136657876811)
              ·
                refine ⟨1908803095767204986815217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1272535397178136657876811 1908803095767204986815217)
                ·
                  refine ⟨1431602321825403740111413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1908803095767204986815217 1431602321825403740111413)
                  ·
                    refine ⟨134212717671131600635445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1431602321825403740111413 134212717671131600635445)
                    ·
                      rfl

theorem cell23_784135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_784135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784135 prefixEnd_784135 := by exact prefixLift 784135
  have htrace : WordTrace (prefixWord ++ tailWord_784135) baseStart_784135 baseEnd_784135 := by
    simpa [prefixWord, tailWord_784135, baseEnd_784135] using wordTrace_append hprefix tailTrace_784135
  have hstable : (prefixWord ++ tailWord_784135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784135).length < 2 ^ (prefixWord ++ tailWord_784135).sum := by decide
  have hdescent : baseEnd_784135 < baseStart_784135 := by decide
  rcases family_descends (prefixWord ++ tailWord_784135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784138 : List Nat := [3, 1, 2, 2, 1, 3, 3, 1, 2, 1, 4]
def baseStart_784138 : Nat := 118140960795 + 784138 * 2 ^ 59
def prefixEnd_784138 : Nat := 4983230072969 + 3 ^ 40 * 784138 * 2
def baseEnd_784138 : Nat := 402639693455358290168821

theorem tailTrace_784138 : CollatzResearch.WordTrace tailWord_784138 prefixEnd_784138 402639693455358290168821 := by
  unfold tailWord_784138
  simp only [CollatzResearch.WordTrace]
  refine ⟨7149965608302355238396267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19066574955472947302390045 7149965608302355238396267)
  ·
    refine ⟨10724948412453532857594401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7149965608302355238396267 10724948412453532857594401)
    ·
      refine ⟨8043711309340149643195801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10724948412453532857594401 8043711309340149643195801)
      ·
        refine ⟨6032783482005112232396851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8043711309340149643195801 6032783482005112232396851)
        ·
          refine ⟨9049175223007668348595277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6032783482005112232396851 9049175223007668348595277)
          ·
            refine ⟨3393440708627875630723229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9049175223007668348595277 3393440708627875630723229)
            ·
              refine ⟨1272540265735453361521211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3393440708627875630723229 1272540265735453361521211)
              ·
                refine ⟨1908810398603180042281817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1272540265735453361521211 1908810398603180042281817)
                ·
                  refine ⟨1431607798952385031711363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1908810398603180042281817 1431607798952385031711363)
                  ·
                    refine ⟨2147411698428577547567045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1431607798952385031711363 2147411698428577547567045)
                    ·
                      refine ⟨402639693455358290168821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2147411698428577547567045 402639693455358290168821)
                      ·
                        rfl

theorem cell23_784138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_784138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784138 prefixEnd_784138 := by exact prefixLift 784138
  have htrace : WordTrace (prefixWord ++ tailWord_784138) baseStart_784138 baseEnd_784138 := by
    simpa [prefixWord, tailWord_784138, baseEnd_784138] using wordTrace_append hprefix tailTrace_784138
  have hstable : (prefixWord ++ tailWord_784138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784138).length < 2 ^ (prefixWord ++ tailWord_784138).sum := by decide
  have hdescent : baseEnd_784138 < baseStart_784138 := by decide
  rcases family_descends (prefixWord ++ tailWord_784138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784151 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 6]
def baseStart_784151 : Nat := 118140960795 + 784151 * 2 ^ 59
def prefixEnd_784151 : Nat := 4983230072969 + 3 ^ 40 * 784151 * 2
def baseEnd_784151 : Nat := 402646368703866739306261

theorem tailTrace_784151 : CollatzResearch.WordTrace tailWord_784151 prefixEnd_784151 402646368703866739306261 := by
  unfold tailWord_784151
  simp only [CollatzResearch.WordTrace]
  refine ⟨28600336582162324173808307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19066891054774882782538871 28600336582162324173808307)
  ·
    refine ⟨42900504873243486260712461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28600336582162324173808307 42900504873243486260712461)
    ·
      refine ⟨16087689327466307347767173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42900504873243486260712461 16087689327466307347767173)
      ·
        refine ⟨3016441748899932627706345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16087689327466307347767173 3016441748899932627706345)
        ·
          refine ⟨2262331311674949470779759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3016441748899932627706345 2262331311674949470779759)
          ·
            refine ⟨3393496967512424206169639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2262331311674949470779759 3393496967512424206169639)
            ·
              refine ⟨5090245451268636309254459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3393496967512424206169639 5090245451268636309254459)
              ·
                refine ⟨7635368176902954463881689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5090245451268636309254459 7635368176902954463881689)
                ·
                  refine ⟨5726526132677215847911267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7635368176902954463881689 5726526132677215847911267)
                  ·
                    refine ⟨8589789199015823771866901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5726526132677215847911267 8589789199015823771866901)
                    ·
                      refine ⟨402646368703866739306261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8589789199015823771866901 402646368703866739306261)
                      ·
                        rfl

theorem cell23_784151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_784151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784151 prefixEnd_784151 := by exact prefixLift 784151
  have htrace : WordTrace (prefixWord ++ tailWord_784151) baseStart_784151 baseEnd_784151 := by
    simpa [prefixWord, tailWord_784151, baseEnd_784151] using wordTrace_append hprefix tailTrace_784151
  have hstable : (prefixWord ++ tailWord_784151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784151).length < 2 ^ (prefixWord ++ tailWord_784151).sum := by decide
  have hdescent : baseEnd_784151 < baseStart_784151 := by decide
  rcases family_descends (prefixWord ++ tailWord_784151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784161 : List Nat := [1, 2, 3, 2, 1, 4, 1, 1, 8]
def baseStart_784161 : Nat := 118140960795 + 784161 * 2 ^ 59
def prefixEnd_784161 : Nat := 4983230072969 + 3 ^ 40 * 784161 * 2
def baseEnd_784161 : Nat := 44739055945601300020135

theorem tailTrace_784161 : CollatzResearch.WordTrace tailWord_784161 prefixEnd_784161 44739055945601300020135 := by
  unfold tailWord_784161
  simp only [CollatzResearch.WordTrace]
  refine ⟨28600701312126095881672337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19067134208084063921114891 28600701312126095881672337)
  ·
    refine ⟨21450525984094571911254253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28600701312126095881672337 21450525984094571911254253)
    ·
      refine ⟨8043947244035464466720345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21450525984094571911254253 8043947244035464466720345)
      ·
        refine ⟨6032960433026598350040259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8043947244035464466720345 6032960433026598350040259)
        ·
          refine ⟨9049440649539897525060389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6032960433026598350040259 9049440649539897525060389)
          ·
            refine ⟨1696770121788730785948823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9049440649539897525060389 1696770121788730785948823)
            ·
              refine ⟨2545155182683096178923235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1696770121788730785948823 2545155182683096178923235)
              ·
                refine ⟨3817732774024644268384853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2545155182683096178923235 3817732774024644268384853)
                ·
                  refine ⟨44739055945601300020135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3817732774024644268384853 44739055945601300020135)
                  ·
                    rfl

theorem cell23_784161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 8].length) (baseStart_784161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784161 prefixEnd_784161 := by exact prefixLift 784161
  have htrace : WordTrace (prefixWord ++ tailWord_784161) baseStart_784161 baseEnd_784161 := by
    simpa [prefixWord, tailWord_784161, baseEnd_784161] using wordTrace_append hprefix tailTrace_784161
  have hstable : (prefixWord ++ tailWord_784161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784161).length < 2 ^ (prefixWord ++ tailWord_784161).sum := by decide
  have hdescent : baseEnd_784161 < baseStart_784161 := by decide
  rcases family_descends (prefixWord ++ tailWord_784161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784165 : List Nat := [1, 3, 1, 2, 3, 2, 2, 4, 1, 4]
def baseStart_784165 : Nat := 118140960795 + 784165 * 2 ^ 59
def prefixEnd_784165 : Nat := 4983230072969 + 3 ^ 40 * 784165 * 2
def baseEnd_784165 : Nat := 134217852477676561510399

theorem tailTrace_784165 : CollatzResearch.WordTrace tailWord_784165 prefixEnd_784165 134217852477676561510399 := by
  unfold tailWord_784165
  simp only [CollatzResearch.WordTrace]
  refine ⟨28600847204111604564817949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19067231469407736376545299 28600847204111604564817949)
  ·
    refine ⟨10725317701541851711806731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28600847204111604564817949 10725317701541851711806731)
    ·
      refine ⟨16087976552312777567710097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10725317701541851711806731 16087976552312777567710097)
      ·
        refine ⟨12065982414234583175782573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16087976552312777567710097 12065982414234583175782573)
        ·
          refine ⟨4524743405337968690918465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12065982414234583175782573 4524743405337968690918465)
          ·
            refine ⟨3393557554003476518188849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4524743405337968690918465 3393557554003476518188849)
            ·
              refine ⟨2545168165502607388641637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3393557554003476518188849 2545168165502607388641637)
              ·
                refine ⟨477219031031738885370307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2545168165502607388641637 477219031031738885370307)
                ·
                  refine ⟨715828546547608328055461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 477219031031738885370307 715828546547608328055461)
                  ·
                    refine ⟨134217852477676561510399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 715828546547608328055461 134217852477676561510399)
                    ·
                      rfl

theorem cell23_784165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4, 1, 4].length) (baseStart_784165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784165 prefixEnd_784165 := by exact prefixLift 784165
  have htrace : WordTrace (prefixWord ++ tailWord_784165) baseStart_784165 baseEnd_784165 := by
    simpa [prefixWord, tailWord_784165, baseEnd_784165] using wordTrace_append hprefix tailTrace_784165
  have hstable : (prefixWord ++ tailWord_784165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784165).length < 2 ^ (prefixWord ++ tailWord_784165).sum := by decide
  have hdescent : baseEnd_784165 < baseStart_784165 := by decide
  rcases family_descends (prefixWord ++ tailWord_784165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784211 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 4]
def baseStart_784211 : Nat := 118140960795 + 784211 * 2 ^ 59
def prefixEnd_784211 : Nat := 4983230072969 + 3 ^ 40 * 784211 * 2
def baseEnd_784211 : Nat := 402677177543136504555985

theorem tailTrace_784211 : CollatzResearch.WordTrace tailWord_784211 prefixEnd_784211 402677177543136504555985 := by
  unfold tailWord_784211
  simp only [CollatzResearch.WordTrace]
  refine ⟨28602524961944954420992487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19068349974629969613994991 28602524961944954420992487)
  ·
    refine ⟨42903787442917431631488731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28602524961944954420992487 42903787442917431631488731)
    ·
      refine ⟨64355681164376147447233097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42903787442917431631488731 64355681164376147447233097)
      ·
        refine ⟨48266760873282110585424823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64355681164376147447233097 48266760873282110585424823)
        ·
          refine ⟨72400141309923165878137235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48266760873282110585424823 72400141309923165878137235)
          ·
            refine ⟨108600211964884748817205853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72400141309923165878137235 108600211964884748817205853)
            ·
              refine ⟨40725079486831780806452195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108600211964884748817205853 40725079486831780806452195)
              ·
                refine ⟨61087619230247671209678293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40725079486831780806452195 61087619230247671209678293)
                ·
                  refine ⟨1431741075708929793976835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 61087619230247671209678293 1431741075708929793976835)
                  ·
                    refine ⟨2147611613563394690965253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1431741075708929793976835 2147611613563394690965253)
                    ·
                      refine ⟨402677177543136504555985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2147611613563394690965253 402677177543136504555985)
                      ·
                        rfl

theorem cell23_784211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 4].length) (baseStart_784211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784211 prefixEnd_784211 := by exact prefixLift 784211
  have htrace : WordTrace (prefixWord ++ tailWord_784211) baseStart_784211 baseEnd_784211 := by
    simpa [prefixWord, tailWord_784211, baseEnd_784211] using wordTrace_append hprefix tailTrace_784211
  have hstable : (prefixWord ++ tailWord_784211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784211).length < 2 ^ (prefixWord ++ tailWord_784211).sum := by decide
  have hdescent : baseEnd_784211 < baseStart_784211 := by decide
  rcases family_descends (prefixWord ++ tailWord_784211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784241 : List Nat := [1, 2, 2, 2, 1, 3, 1, 3, 1, 1, 6]
def baseStart_784241 : Nat := 118140960795 + 784241 * 2 ^ 59
def prefixEnd_784241 : Nat := 4983230072969 + 3 ^ 40 * 784241 * 2
def baseEnd_784241 : Nat := 402692581962771387180847

theorem tailTrace_784241 : CollatzResearch.WordTrace tailWord_784241 prefixEnd_784241 402692581962771387180847 := by
  unfold tailWord_784241
  simp only [CollatzResearch.WordTrace]
  refine ⟨28603619151836269544584577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19069079434557513029723051 28603619151836269544584577)
  ·
    refine ⟨21452714363877202158438433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28603619151836269544584577 21452714363877202158438433)
    ·
      refine ⟨16089535772907901618828825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21452714363877202158438433 16089535772907901618828825)
      ·
        refine ⟨12067151829680926214121619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16089535772907901618828825 12067151829680926214121619)
        ·
          refine ⟨18100727744521389321182429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12067151829680926214121619 18100727744521389321182429)
          ·
            refine ⟨6787772904195520995443411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18100727744521389321182429 6787772904195520995443411)
            ·
              refine ⟨10181659356293281493165117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6787772904195520995443411 10181659356293281493165117)
              ·
                refine ⟨3818122258609980559936919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10181659356293281493165117 3818122258609980559936919)
                ·
                  refine ⟨5727183387914970839905379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3818122258609980559936919 5727183387914970839905379)
                  ·
                    refine ⟨8590775081872456259858069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5727183387914970839905379 8590775081872456259858069)
                    ·
                      refine ⟨402692581962771387180847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8590775081872456259858069 402692581962771387180847)
                      ·
                        rfl

theorem cell23_784241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_784241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784241 prefixEnd_784241 := by exact prefixLift 784241
  have htrace : WordTrace (prefixWord ++ tailWord_784241) baseStart_784241 baseEnd_784241 := by
    simpa [prefixWord, tailWord_784241, baseEnd_784241] using wordTrace_append hprefix tailTrace_784241
  have hstable : (prefixWord ++ tailWord_784241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784241).length < 2 ^ (prefixWord ++ tailWord_784241).sum := by decide
  have hdescent : baseEnd_784241 < baseStart_784241 := by decide
  rcases family_descends (prefixWord ++ tailWord_784241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784279 : List Nat := [1, 1, 3, 3, 1, 4, 1, 4, 1, 2, 2]
def baseStart_784279 : Nat := 118140960795 + 784279 * 2 ^ 59
def prefixEnd_784279 : Nat := 4983230072969 + 3 ^ 40 * 784279 * 2
def baseEnd_784279 : Nat := 402712094227642238505673

theorem tailTrace_784279 : CollatzResearch.WordTrace tailWord_784279 prefixEnd_784279 402712094227642238505673 := by
  unfold tailWord_784279
  simp only [CollatzResearch.WordTrace]
  refine ⟨28605005125698602034467891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19070003417132401356311927 28605005125698602034467891)
  ·
    refine ⟨42907507688547903051701837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28605005125698602034467891 42907507688547903051701837)
    ·
      refine ⟨16090315383205463644388189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42907507688547903051701837 16090315383205463644388189)
      ·
        refine ⟨6033868268702048866645571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16090315383205463644388189 6033868268702048866645571)
        ·
          refine ⟨9050802403053073299968357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6033868268702048866645571 9050802403053073299968357)
          ·
            refine ⟨1697025450572451243744067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9050802403053073299968357 1697025450572451243744067)
            ·
              refine ⟨2545538175858676865616101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1697025450572451243744067 2545538175858676865616101)
              ·
                refine ⟨477288407973501912303019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2545538175858676865616101 477288407973501912303019)
                ·
                  refine ⟨715932611960252868454529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 477288407973501912303019 715932611960252868454529)
                  ·
                    refine ⟨536949458970189651340897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 715932611960252868454529 536949458970189651340897)
                    ·
                      refine ⟨402712094227642238505673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 536949458970189651340897 402712094227642238505673)
                      ·
                        rfl

theorem cell23_784279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_784279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784279 prefixEnd_784279 := by exact prefixLift 784279
  have htrace : WordTrace (prefixWord ++ tailWord_784279) baseStart_784279 baseEnd_784279 := by
    simpa [prefixWord, tailWord_784279, baseEnd_784279] using wordTrace_append hprefix tailTrace_784279
  have hstable : (prefixWord ++ tailWord_784279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784279).length < 2 ^ (prefixWord ++ tailWord_784279).sum := by decide
  have hdescent : baseEnd_784279 < baseStart_784279 := by decide
  rcases family_descends (prefixWord ++ tailWord_784279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784281 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 2, 7]
def baseStart_784281 : Nat := 118140960795 + 784281 * 2 ^ 59
def prefixEnd_784281 : Nat := 4983230072969 + 3 ^ 40 * 784281 * 2
def baseEnd_784281 : Nat := 134237707062983743560221

theorem tailTrace_784281 : CollatzResearch.WordTrace tailWord_784281 prefixEnd_784281 134237707062983743560221 := by
  unfold tailWord_784281
  simp only [CollatzResearch.WordTrace]
  refine ⟨28605078071691356376040697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19070052047794237584027131 28605078071691356376040697)
  ·
    refine ⟨21453808553768517282030523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28605078071691356376040697 21453808553768517282030523)
    ·
      refine ⟨32180712830652775923045785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21453808553768517282030523 32180712830652775923045785)
      ·
        refine ⟨24135534622989581942284339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32180712830652775923045785 24135534622989581942284339)
        ·
          refine ⟨36203301934484372913426509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24135534622989581942284339 36203301934484372913426509)
          ·
            refine ⟨13576238225431639842534941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36203301934484372913426509 13576238225431639842534941)
            ·
              refine ⟨5091089334536864940950603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13576238225431639842534941 5091089334536864940950603)
              ·
                refine ⟨7636634001805297411425905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5091089334536864940950603 7636634001805297411425905)
                ·
                  refine ⟨5727475501353973058569429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7636634001805297411425905 5727475501353973058569429)
                  ·
                    refine ⟨134237707062983743560221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5727475501353973058569429 134237707062983743560221)
                    ·
                      rfl

theorem cell23_784281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 7].length) (baseStart_784281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784281 prefixEnd_784281 := by exact prefixLift 784281
  have htrace : WordTrace (prefixWord ++ tailWord_784281) baseStart_784281 baseEnd_784281 := by
    simpa [prefixWord, tailWord_784281, baseEnd_784281] using wordTrace_append hprefix tailTrace_784281
  have hstable : (prefixWord ++ tailWord_784281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784281).length < 2 ^ (prefixWord ++ tailWord_784281).sum := by decide
  have hdescent : baseEnd_784281 < baseStart_784281 := by decide
  rcases family_descends (prefixWord ++ tailWord_784281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784291 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 5]
def baseStart_784291 : Nat := 118140960795 + 784291 * 2 ^ 59
def prefixEnd_784291 : Nat := 4983230072969 + 3 ^ 40 * 784291 * 2
def baseEnd_784291 : Nat := 402718255995496191555617

theorem tailTrace_784291 : CollatzResearch.WordTrace tailWord_784291 prefixEnd_784291 402718255995496191555617 := by
  unfold tailWord_784291
  simp only [CollatzResearch.WordTrace]
  refine ⟨28605442801655128083904727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19070295201103418722603151 28605442801655128083904727)
  ·
    refine ⟨42908164202482692125857091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28605442801655128083904727 42908164202482692125857091)
    ·
      refine ⟨64362246303724038188785637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42908164202482692125857091 64362246303724038188785637)
      ·
        refine ⟨12067921181948257160397307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64362246303724038188785637 12067921181948257160397307)
        ·
          refine ⟨18101881772922385740595961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12067921181948257160397307 18101881772922385740595961)
          ·
            refine ⟨13576411329691789305446971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18101881772922385740595961 13576411329691789305446971)
            ·
              refine ⟨20364616994537683958170457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13576411329691789305446971 20364616994537683958170457)
              ·
                refine ⟨15273462745903262968627843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20364616994537683958170457 15273462745903262968627843)
                ·
                  refine ⟨22910194118854894452941765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15273462745903262968627843 22910194118854894452941765)
                  ·
                    refine ⟨4295661397285292709926581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22910194118854894452941765 4295661397285292709926581)
                    ·
                      refine ⟨402718255995496191555617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4295661397285292709926581 402718255995496191555617)
                      ·
                        rfl

theorem cell23_784291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_784291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784291 prefixEnd_784291 := by exact prefixLift 784291
  have htrace : WordTrace (prefixWord ++ tailWord_784291) baseStart_784291 baseEnd_784291 := by
    simpa [prefixWord, tailWord_784291, baseEnd_784291] using wordTrace_append hprefix tailTrace_784291
  have hstable : (prefixWord ++ tailWord_784291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784291).length < 2 ^ (prefixWord ++ tailWord_784291).sum := by decide
  have hdescent : baseEnd_784291 < baseStart_784291 := by decide
  rcases family_descends (prefixWord ++ tailWord_784291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784295 : List Nat := [1, 1, 6, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_784295 : Nat := 118140960795 + 784295 * 2 ^ 59
def prefixEnd_784295 : Nat := 4983230072969 + 3 ^ 40 * 784295 * 2
def baseEnd_784295 : Nat := 402720309918114175905599

theorem tailTrace_784295 : CollatzResearch.WordTrace tailWord_784295 prefixEnd_784295 402720309918114175905599 := by
  unfold tailWord_784295
  simp only [CollatzResearch.WordTrace]
  refine ⟨28605588693640636767050339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19070392462427091178033559 28605588693640636767050339)
  ·
    refine ⟨42908383040460955150575509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28605588693640636767050339 42908383040460955150575509)
    ·
      refine ⟨2011330455021607272683227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42908383040460955150575509 2011330455021607272683227)
      ·
        refine ⟨3016995682532410909024841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2011330455021607272683227 3016995682532410909024841)
        ·
          refine ⟨2262746761899308181768631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3016995682532410909024841 2262746761899308181768631)
          ·
            refine ⟨3394120142848962272652947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2262746761899308181768631 3394120142848962272652947)
            ·
              refine ⟨5091180214273443408979421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3394120142848962272652947 5091180214273443408979421)
              ·
                refine ⟨1909192580352541278367283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5091180214273443408979421 1909192580352541278367283)
                ·
                  refine ⟨2863788870528811917550925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1909192580352541278367283 2863788870528811917550925)
                  ·
                    refine ⟨1073920826448304469081597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2863788870528811917550925 1073920826448304469081597)
                    ·
                      refine ⟨402720309918114175905599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1073920826448304469081597 402720309918114175905599)
                      ·
                        rfl

theorem cell23_784295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_784295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784295 prefixEnd_784295 := by exact prefixLift 784295
  have htrace : WordTrace (prefixWord ++ tailWord_784295) baseStart_784295 baseEnd_784295 := by
    simpa [prefixWord, tailWord_784295, baseEnd_784295] using wordTrace_append hprefix tailTrace_784295
  have hstable : (prefixWord ++ tailWord_784295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784295).length < 2 ^ (prefixWord ++ tailWord_784295).sum := by decide
  have hdescent : baseEnd_784295 < baseStart_784295 := by decide
  rcases family_descends (prefixWord ++ tailWord_784295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784296 : List Nat := [2, 1, 6, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_784296 : Nat := 118140960795 + 784296 * 2 ^ 59
def prefixEnd_784296 : Nat := 4983230072969 + 3 ^ 40 * 784296 * 2
def baseEnd_784296 : Nat := 402720823398768671993095

theorem tailTrace_784296 : CollatzResearch.WordTrace tailWord_784296 prefixEnd_784296 402720823398768671993095 := by
  unfold tailWord_784296
  simp only [CollatzResearch.WordTrace]
  refine ⟨14302812583318506968918371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19070416777758009291891161 14302812583318506968918371)
  ·
    refine ⟨21454218874977760453377557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14302812583318506968918371 21454218874977760453377557)
    ·
      refine ⟨1005666509764582521252073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21454218874977760453377557 1005666509764582521252073)
      ·
        refine ⟨754249882323436890939055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1005666509764582521252073 754249882323436890939055)
        ·
          refine ⟨1131374823485155336408583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754249882323436890939055 1131374823485155336408583)
          ·
            refine ⟨1697062235227733004612875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131374823485155336408583 1697062235227733004612875)
            ·
              refine ⟨2545593352841599506919313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1697062235227733004612875 2545593352841599506919313)
              ·
                refine ⟨1909195014631199630189485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2545593352841599506919313 1909195014631199630189485)
                ·
                  refine ⟨715948130486699861321057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1909195014631199630189485 715948130486699861321057)
                  ·
                    refine ⟨536961097865024895990793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 715948130486699861321057 536961097865024895990793)
                    ·
                      refine ⟨402720823398768671993095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 536961097865024895990793 402720823398768671993095)
                      ·
                        rfl

theorem cell23_784296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_784296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784296 prefixEnd_784296 := by exact prefixLift 784296
  have htrace : WordTrace (prefixWord ++ tailWord_784296) baseStart_784296 baseEnd_784296 := by
    simpa [prefixWord, tailWord_784296, baseEnd_784296] using wordTrace_append hprefix tailTrace_784296
  have hstable : (prefixWord ++ tailWord_784296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784296).length < 2 ^ (prefixWord ++ tailWord_784296).sum := by decide
  have hdescent : baseEnd_784296 < baseStart_784296 := by decide
  rcases family_descends (prefixWord ++ tailWord_784296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784311 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 3, 8]
def baseStart_784311 : Nat := 118140960795 + 784311 * 2 ^ 59
def prefixEnd_784311 : Nat := 4983230072969 + 3 ^ 40 * 784311 * 2
def baseEnd_784311 : Nat := 134242841869528704435175

theorem tailTrace_784311 : CollatzResearch.WordTrace tailWord_784311 prefixEnd_784311 134242841869528704435175 := by
  unfold tailWord_784311
  simp only [CollatzResearch.WordTrace]
  refine ⟨28606172261582671499632787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19070781507721780999755191 28606172261582671499632787)
  ·
    refine ⟨42909258392374007249449181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28606172261582671499632787 42909258392374007249449181)
    ·
      refine ⟨16090971897140252718543443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42909258392374007249449181 16090971897140252718543443)
      ·
        refine ⟨24136457845710379077815165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16090971897140252718543443 24136457845710379077815165)
        ·
          refine ⟨9051171692141392154180687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24136457845710379077815165 9051171692141392154180687)
          ·
            refine ⟨13576757538212088231271031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9051171692141392154180687 13576757538212088231271031)
            ·
              refine ⟨20365136307318132346906547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13576757538212088231271031 20365136307318132346906547)
              ·
                refine ⟨30547704460977198520359821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20365136307318132346906547 30547704460977198520359821)
                ·
                  refine ⟨11455389172866449445134933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30547704460977198520359821 11455389172866449445134933)
                  ·
                    refine ⟨134242841869528704435175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11455389172866449445134933 134242841869528704435175)
                    ·
                      rfl

theorem cell23_784311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_784311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784311 prefixEnd_784311 := by exact prefixLift 784311
  have htrace : WordTrace (prefixWord ++ tailWord_784311) baseStart_784311 baseEnd_784311 := by
    simpa [prefixWord, tailWord_784311, baseEnd_784311] using wordTrace_append hprefix tailTrace_784311
  have hstable : (prefixWord ++ tailWord_784311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784311).length < 2 ^ (prefixWord ++ tailWord_784311).sum := by decide
  have hdescent : baseEnd_784311 < baseStart_784311 := by decide
  rcases family_descends (prefixWord ++ tailWord_784311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784316 : List Nat := [2, 2, 2, 5, 1, 2, 2, 1, 1, 2, 3]
def baseStart_784316 : Nat := 118140960795 + 784316 * 2 ^ 59
def prefixEnd_784316 : Nat := 4983230072969 + 3 ^ 40 * 784316 * 2
def baseEnd_784316 : Nat := 402731093011858593743003

theorem tailTrace_784316 : CollatzResearch.WordTrace tailWord_784316 prefixEnd_784316 402731093011858593743003 := by
  unfold tailWord_784316
  simp only [CollatzResearch.WordTrace]
  refine ⟨14303177313282278676782401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19070903084376371569043201 14303177313282278676782401)
  ·
    refine ⟨10727382984961709007586801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14303177313282278676782401 10727382984961709007586801)
    ·
      refine ⟨8045537238721281755690101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10727382984961709007586801 8045537238721281755690101)
      ·
        refine ⟨754269116130120164595947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8045537238721281755690101 754269116130120164595947)
        ·
          refine ⟨1131403674195180246893921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754269116130120164595947 1131403674195180246893921)
          ·
            refine ⟨848552755646385185170441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1131403674195180246893921 848552755646385185170441)
            ·
              refine ⟨636414566734788888877831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 848552755646385185170441 636414566734788888877831)
              ·
                refine ⟨954621850102183333316747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636414566734788888877831 954621850102183333316747)
                ·
                  refine ⟨1431932775153274999975121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 954621850102183333316747 1431932775153274999975121)
                  ·
                    refine ⟨1073949581364956249981341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1431932775153274999975121 1073949581364956249981341)
                    ·
                      refine ⟨402731093011858593743003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1073949581364956249981341 402731093011858593743003)
                      ·
                        rfl

theorem cell23_784316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_784316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784316 prefixEnd_784316 := by exact prefixLift 784316
  have htrace : WordTrace (prefixWord ++ tailWord_784316) baseStart_784316 baseEnd_784316 := by
    simpa [prefixWord, tailWord_784316, baseEnd_784316] using wordTrace_append hprefix tailTrace_784316
  have hstable : (prefixWord ++ tailWord_784316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784316).length < 2 ^ (prefixWord ++ tailWord_784316).sum := by decide
  have hdescent : baseEnd_784316 < baseStart_784316 := by decide
  rcases family_descends (prefixWord ++ tailWord_784316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784328 : List Nat := [2, 1, 3, 1, 4, 1, 1, 2, 2, 6]
def baseStart_784328 : Nat := 118140960795 + 784328 * 2 ^ 59
def prefixEnd_784328 : Nat := 4983230072969 + 3 ^ 40 * 784328 * 2
def baseEnd_784328 : Nat := 134245751593237515597649

theorem tailTrace_784328 : CollatzResearch.WordTrace tailWord_784328 prefixEnd_784328 134245751593237515597649 := by
  unfold tailWord_784328
  simp only [CollatzResearch.WordTrace]
  refine ⟨14303396151260541701500819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19071194868347388935334425 14303396151260541701500819)
  ·
    refine ⟨21455094226890812552251229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14303396151260541701500819 21455094226890812552251229)
    ·
      refine ⟨8045660335084054707094211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21455094226890812552251229 8045660335084054707094211)
      ·
        refine ⟨12068490502626082060641317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8045660335084054707094211 12068490502626082060641317)
        ·
          refine ⟨2262841969242390386370247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12068490502626082060641317 2262841969242390386370247)
          ·
            refine ⟨3394262953863585579555371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2262841969242390386370247 3394262953863585579555371)
            ·
              refine ⟨5091394430795378369333057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3394262953863585579555371 5091394430795378369333057)
              ·
                refine ⟨3818545823096533776999793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5091394430795378369333057 3818545823096533776999793)
                ·
                  refine ⟨2863909367322400332749845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3818545823096533776999793 2863909367322400332749845)
                  ·
                    refine ⟨134245751593237515597649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2863909367322400332749845 134245751593237515597649)
                    ·
                      rfl

theorem cell23_784328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_784328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784328 prefixEnd_784328 := by exact prefixLift 784328
  have htrace : WordTrace (prefixWord ++ tailWord_784328) baseStart_784328 baseEnd_784328 := by
    simpa [prefixWord, tailWord_784328, baseEnd_784328] using wordTrace_append hprefix tailTrace_784328
  have hstable : (prefixWord ++ tailWord_784328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784328).length < 2 ^ (prefixWord ++ tailWord_784328).sum := by decide
  have hdescent : baseEnd_784328 < baseStart_784328 := by decide
  rcases family_descends (prefixWord ++ tailWord_784328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784352 : List Nat := [2, 1, 1, 3, 1, 1, 1, 7, 2, 2, 2]
def baseStart_784352 : Nat := 118140960795 + 784352 * 2 ^ 59
def prefixEnd_784352 : Nat := 4983230072969 + 3 ^ 40 * 784352 * 2
def baseEnd_784352 : Nat := 402749578315420452892837

theorem tailTrace_784352 : CollatzResearch.WordTrace tailWord_784352 prefixEnd_784352 402749578315420452892837 := by
  unfold tailWord_784352
  simp only [CollatzResearch.WordTrace]
  refine ⟨14303833827217067750937655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19071778436289423667916873 14303833827217067750937655)
  ·
    refine ⟨21455750740825601626406483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14303833827217067750937655 21455750740825601626406483)
    ·
      refine ⟨32183626111238402439609725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21455750740825601626406483 32183626111238402439609725)
      ·
        refine ⟨12068859791714400914853647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32183626111238402439609725 12068859791714400914853647)
        ·
          refine ⟨18103289687571601372280471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12068859791714400914853647 18103289687571601372280471)
          ·
            refine ⟨27154934531357402058420707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18103289687571601372280471 27154934531357402058420707)
            ·
              refine ⟨40732401797036103087631061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27154934531357402058420707 40732401797036103087631061)
              ·
                refine ⟨954665667118033666116353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 40732401797036103087631061 954665667118033666116353)
                ·
                  refine ⟨715999250338525249587265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 954665667118033666116353 715999250338525249587265)
                  ·
                    refine ⟨536999437753893937190449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 715999250338525249587265 536999437753893937190449)
                    ·
                      refine ⟨402749578315420452892837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 536999437753893937190449 402749578315420452892837)
                      ·
                        rfl

theorem cell23_784352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 2, 2, 2].length) (baseStart_784352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784352 prefixEnd_784352 := by exact prefixLift 784352
  have htrace : WordTrace (prefixWord ++ tailWord_784352) baseStart_784352 baseEnd_784352 := by
    simpa [prefixWord, tailWord_784352, baseEnd_784352] using wordTrace_append hprefix tailTrace_784352
  have hstable : (prefixWord ++ tailWord_784352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784352).length < 2 ^ (prefixWord ++ tailWord_784352).sum := by decide
  have hdescent : baseEnd_784352 < baseStart_784352 := by decide
  rcases family_descends (prefixWord ++ tailWord_784352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784368 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 3]
def baseStart_784368 : Nat := 118140960795 + 784368 * 2 ^ 59
def prefixEnd_784368 : Nat := 4983230072969 + 3 ^ 40 * 784368 * 2
def baseEnd_784368 : Nat := 402757794005892390292763

theorem tailTrace_784368 : CollatzResearch.WordTrace tailWord_784368 prefixEnd_784368 402757794005892390292763 := by
  unfold tailWord_784368
  simp only [CollatzResearch.WordTrace]
  refine ⟨14304125611188085117228879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19072167481584113489638505 14304125611188085117228879)
  ·
    refine ⟨21456188416782127675843319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14304125611188085117228879 21456188416782127675843319)
    ·
      refine ⟨32184282625173191513764979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21456188416782127675843319 32184282625173191513764979)
      ·
        refine ⟨48276423937759787270647469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32184282625173191513764979 48276423937759787270647469)
        ·
          refine ⟨18103658976659920226492801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48276423937759787270647469 18103658976659920226492801)
          ·
            refine ⟨13577744232494940169869601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18103658976659920226492801 13577744232494940169869601)
            ·
              refine ⟨10183308174371205127402201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13577744232494940169869601 10183308174371205127402201)
              ·
                refine ⟨7637481130778403845551651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10183308174371205127402201 7637481130778403845551651)
                ·
                  refine ⟨11456221696167605768327477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7637481130778403845551651 11456221696167605768327477)
                  ·
                    refine ⟨1074020784015713040780701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11456221696167605768327477 1074020784015713040780701)
                    ·
                      refine ⟨402757794005892390292763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1074020784015713040780701 402757794005892390292763)
                      ·
                        rfl

theorem cell23_784368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 3].length) (baseStart_784368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784368 prefixEnd_784368 := by exact prefixLift 784368
  have htrace : WordTrace (prefixWord ++ tailWord_784368) baseStart_784368 baseEnd_784368 := by
    simpa [prefixWord, tailWord_784368, baseEnd_784368] using wordTrace_append hprefix tailTrace_784368
  have hstable : (prefixWord ++ tailWord_784368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784368).length < 2 ^ (prefixWord ++ tailWord_784368).sum := by decide
  have hdescent : baseEnd_784368 < baseStart_784368 := by decide
  rcases family_descends (prefixWord ++ tailWord_784368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784392 : List Nat := [2, 1, 3, 2, 1, 2, 5, 2, 5]
def baseStart_784392 : Nat := 118140960795 + 784392 * 2 ^ 59
def prefixEnd_784392 : Nat := 4983230072969 + 3 ^ 40 * 784392 * 2
def baseEnd_784392 : Nat := 44752235282400032932517

theorem tailTrace_784392 : CollatzResearch.WordTrace tailWord_784392 prefixEnd_784392 44752235282400032932517 := by
  unfold tailWord_784392
  simp only [CollatzResearch.WordTrace]
  refine ⟨14304563287144611166665715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19072751049526148222220953 14304563287144611166665715)
  ·
    refine ⟨21456844930716916749998573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14304563287144611166665715 21456844930716916749998573)
    ·
      refine ⟨8046316849018843781249465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21456844930716916749998573 8046316849018843781249465)
      ·
        refine ⟨6034737636764132835937099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8046316849018843781249465 6034737636764132835937099)
        ·
          refine ⟨9052106455146199253905649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6034737636764132835937099 9052106455146199253905649)
          ·
            refine ⟨6789079841359649440429237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9052106455146199253905649 6789079841359649440429237)
            ·
              refine ⟨636476235127467135040241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6789079841359649440429237 636476235127467135040241)
              ·
                refine ⟨477357176345600351280181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 636476235127467135040241 477357176345600351280181)
                ·
                  refine ⟨44752235282400032932517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 477357176345600351280181 44752235282400032932517)
                  ·
                    rfl

theorem cell23_784392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2, 5].length) (baseStart_784392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784392 prefixEnd_784392 := by exact prefixLift 784392
  have htrace : WordTrace (prefixWord ++ tailWord_784392) baseStart_784392 baseEnd_784392 := by
    simpa [prefixWord, tailWord_784392, baseEnd_784392] using wordTrace_append hprefix tailTrace_784392
  have hstable : (prefixWord ++ tailWord_784392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784392).length < 2 ^ (prefixWord ++ tailWord_784392).sum := by decide
  have hdescent : baseEnd_784392 < baseStart_784392 := by decide
  rcases family_descends (prefixWord ++ tailWord_784392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784395 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 2, 5, 2]
def baseStart_784395 : Nat := 118140960795 + 784395 * 2 ^ 59
def prefixEnd_784395 : Nat := 4983230072969 + 3 ^ 40 * 784395 * 2
def baseEnd_784395 : Nat := 402771657983563784655139

theorem tailTrace_784395 : CollatzResearch.WordTrace tailWord_784395 prefixEnd_784395 402771657983563784655139 := by
  unfold tailWord_784395
  simp only [CollatzResearch.WordTrace]
  refine ⟨28609235993278353845690639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19072823995518902563793759 28609235993278353845690639)
  ·
    refine ⟨42913853989917530768535959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28609235993278353845690639 42913853989917530768535959)
    ·
      refine ⟨64370780984876296152803939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42913853989917530768535959 64370780984876296152803939)
      ·
        refine ⟨96556171477314444229205909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64370780984876296152803939 96556171477314444229205909)
        ·
          refine ⟨4526070537999114573244027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96556171477314444229205909 4526070537999114573244027)
          ·
            refine ⟨6789105806998671859866041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4526070537999114573244027 6789105806998671859866041)
            ·
              refine ⟨5091829355249003894899531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6789105806998671859866041 5091829355249003894899531)
              ·
                refine ⟨7637744032873505842349297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5091829355249003894899531 7637744032873505842349297)
                ·
                  refine ⟨5728308024655129381761973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7637744032873505842349297 5728308024655129381761973)
                  ·
                    refine ⟨537028877311418379540185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5728308024655129381761973 537028877311418379540185)
                    ·
                      refine ⟨402771657983563784655139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 537028877311418379540185 402771657983563784655139)
                      ·
                        rfl

theorem cell23_784395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 5, 2].length) (baseStart_784395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784395 prefixEnd_784395 := by exact prefixLift 784395
  have htrace : WordTrace (prefixWord ++ tailWord_784395) baseStart_784395 baseEnd_784395 := by
    simpa [prefixWord, tailWord_784395, baseEnd_784395] using wordTrace_append hprefix tailTrace_784395
  have hstable : (prefixWord ++ tailWord_784395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784395).length < 2 ^ (prefixWord ++ tailWord_784395).sum := by decide
  have hdescent : baseEnd_784395 < baseStart_784395 := by decide
  rcases family_descends (prefixWord ++ tailWord_784395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784397 : List Nat := [1, 7, 1, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_784397 : Nat := 118140960795 + 784397 * 2 ^ 59
def prefixEnd_784397 : Nat := 4983230072969 + 3 ^ 40 * 784397 * 2
def baseEnd_784397 : Nat := 402772684944872776830131

theorem tailTrace_784397 : CollatzResearch.WordTrace tailWord_784397 prefixEnd_784397 402772684944872776830131 := by
  unfold tailWord_784397
  simp only [CollatzResearch.WordTrace]
  refine ⟨28609308939271108187263445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19072872626180738791508963 28609308939271108187263445)
  ·
    refine ⟨670530678264166598138987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 28609308939271108187263445 670530678264166598138987)
    ·
      refine ⟨1005796017396249897208481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 670530678264166598138987 1005796017396249897208481)
      ·
        refine ⟨754347013047187422906361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1005796017396249897208481 754347013047187422906361)
        ·
          refine ⟨565760259785390567179771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 754347013047187422906361 565760259785390567179771)
          ·
            refine ⟨848640389678085850769657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565760259785390567179771 848640389678085850769657)
            ·
              refine ⟨636480292258564388077243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 848640389678085850769657 636480292258564388077243)
              ·
                refine ⟨954720438387846582115865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636480292258564388077243 954720438387846582115865)
                ·
                  refine ⟨716040328790884936586899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 954720438387846582115865 716040328790884936586899)
                  ·
                    refine ⟨1074060493186327404880349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 716040328790884936586899 1074060493186327404880349)
                    ·
                      refine ⟨402772684944872776830131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1074060493186327404880349 402772684944872776830131)
                      ·
                        rfl

theorem cell23_784397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_784397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784397 prefixEnd_784397 := by exact prefixLift 784397
  have htrace : WordTrace (prefixWord ++ tailWord_784397) baseStart_784397 baseEnd_784397 := by
    simpa [prefixWord, tailWord_784397, baseEnd_784397] using wordTrace_append hprefix tailTrace_784397
  have hstable : (prefixWord ++ tailWord_784397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784397).length < 2 ^ (prefixWord ++ tailWord_784397).sum := by decide
  have hdescent : baseEnd_784397 < baseStart_784397 := by decide
  rcases family_descends (prefixWord ++ tailWord_784397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784509 : List Nat := [1, 4, 1, 1, 3, 3, 2, 1, 3, 1, 3]
def baseStart_784509 : Nat := 118140960795 + 784509 * 2 ^ 59
def prefixEnd_784509 : Nat := 4983230072969 + 3 ^ 40 * 784509 * 2
def baseEnd_784509 : Nat := 402830194778176338629615

theorem tailTrace_784509 : CollatzResearch.WordTrace tailWord_784509 prefixEnd_784509 402830194778176338629615 := by
  unfold tailWord_784509
  simp only [CollatzResearch.WordTrace]
  refine ⟨28613393914865351315340581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19075595943243567543560387 28613393914865351315340581)
  ·
    refine ⟨5365011359037253371626359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28613393914865351315340581 5365011359037253371626359)
    ·
      refine ⟨8047517038555880057439539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5365011359037253371626359 8047517038555880057439539)
      ·
        refine ⟨12071275557833820086159309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8047517038555880057439539 12071275557833820086159309)
        ·
          refine ⟨4526728334187682532309741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12071275557833820086159309 4526728334187682532309741)
          ·
            refine ⟨1697523125320380949616153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4526728334187682532309741 1697523125320380949616153)
            ·
              refine ⟨1273142343990285712212115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1697523125320380949616153 1273142343990285712212115)
              ·
                refine ⟨1909713515985428568318173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1273142343990285712212115 1909713515985428568318173)
                ·
                  refine ⟨716142568494535713119315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1909713515985428568318173 716142568494535713119315)
                  ·
                    refine ⟨1074213852741803569678973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 716142568494535713119315 1074213852741803569678973)
                    ·
                      refine ⟨402830194778176338629615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1074213852741803569678973 402830194778176338629615)
                      ·
                        rfl

theorem cell23_784509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_784509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784509 prefixEnd_784509 := by exact prefixLift 784509
  have htrace : WordTrace (prefixWord ++ tailWord_784509) baseStart_784509 baseEnd_784509 := by
    simpa [prefixWord, tailWord_784509, baseEnd_784509] using wordTrace_append hprefix tailTrace_784509
  have hstable : (prefixWord ++ tailWord_784509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784509).length < 2 ^ (prefixWord ++ tailWord_784509).sum := by decide
  have hdescent : baseEnd_784509 < baseStart_784509 := by decide
  rcases family_descends (prefixWord ++ tailWord_784509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784543 : List Nat := [1, 1, 2, 6, 1, 3, 1, 3, 1, 1, 3]
def baseStart_784543 : Nat := 118140960795 + 784543 * 2 ^ 59
def prefixEnd_784543 : Nat := 4983230072969 + 3 ^ 40 * 784543 * 2
def baseEnd_784543 : Nat := 402847653120429205604459

theorem tailTrace_784543 : CollatzResearch.WordTrace tailWord_784543 prefixEnd_784543 402847653120429205604459 := by
  unfold tailWord_784543
  simp only [CollatzResearch.WordTrace]
  refine ⟨28614633996742175122078283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19076422664494783414718855 28614633996742175122078283)
  ·
    refine ⟨42921950995113262683117425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28614633996742175122078283 42921950995113262683117425)
    ·
      refine ⟨32191463246334947012338069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42921950995113262683117425 32191463246334947012338069)
      ·
        refine ⟨1508974839671950641203347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32191463246334947012338069 1508974839671950641203347)
        ·
          refine ⟨2263462259507925961805021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1508974839671950641203347 2263462259507925961805021)
          ·
            refine ⟨848798347315472235676883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2263462259507925961805021 848798347315472235676883)
            ·
              refine ⟨1273197520973208353515325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 848798347315472235676883 1273197520973208353515325)
              ·
                refine ⟨477449070364953132568247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1273197520973208353515325 477449070364953132568247)
                ·
                  refine ⟨716173605547429698852371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 477449070364953132568247 716173605547429698852371)
                  ·
                    refine ⟨1074260408321144548278557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 716173605547429698852371 1074260408321144548278557)
                    ·
                      refine ⟨402847653120429205604459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1074260408321144548278557 402847653120429205604459)
                      ·
                        rfl

theorem cell23_784543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_784543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784543 prefixEnd_784543 := by exact prefixLift 784543
  have htrace : WordTrace (prefixWord ++ tailWord_784543) baseStart_784543 baseEnd_784543 := by
    simpa [prefixWord, tailWord_784543, baseEnd_784543] using wordTrace_append hprefix tailTrace_784543
  have hstable : (prefixWord ++ tailWord_784543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784543).length < 2 ^ (prefixWord ++ tailWord_784543).sum := by decide
  have hdescent : baseEnd_784543 < baseStart_784543 := by decide
  rcases family_descends (prefixWord ++ tailWord_784543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784572 : List Nat := [2, 2, 2, 3, 3, 1, 2, 8]
def baseStart_784572 : Nat := 118140960795 + 784572 * 2 ^ 59
def prefixEnd_784572 : Nat := 4983230072969 + 3 ^ 40 * 784572 * 2
def baseEnd_784572 : Nat := 14920834965163318227475

theorem tailTrace_784572 : CollatzResearch.WordTrace tailWord_784572 prefixEnd_784572 14920834965163318227475 := by
  unfold tailWord_784572
  simp only [CollatzResearch.WordTrace]
  refine ⟨14307845856818556537441985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19077127809091408716589313 14307845856818556537441985)
  ·
    refine ⟨10730884392613917403081489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14307845856818556537441985 10730884392613917403081489)
    ·
      refine ⟨8048163294460438052311117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10730884392613917403081489 8048163294460438052311117)
      ·
        refine ⟨3018061235422664269616669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8048163294460438052311117 3018061235422664269616669)
        ·
          refine ⟨1131772963283499101106251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3018061235422664269616669 1131772963283499101106251)
          ·
            refine ⟨1697659444925248651659377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131772963283499101106251 1697659444925248651659377)
            ·
              refine ⟨1273244583693936488744533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1697659444925248651659377 1273244583693936488744533)
              ·
                refine ⟨14920834965163318227475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1273244583693936488744533 14920834965163318227475)
                ·
                  rfl

theorem cell23_784572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 8].length) (baseStart_784572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784572 prefixEnd_784572 := by exact prefixLift 784572
  have htrace : WordTrace (prefixWord ++ tailWord_784572) baseStart_784572 baseEnd_784572 := by
    simpa [prefixWord, tailWord_784572, baseEnd_784572] using wordTrace_append hprefix tailTrace_784572
  have hstable : (prefixWord ++ tailWord_784572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784572).length < 2 ^ (prefixWord ++ tailWord_784572).sum := by decide
  have hdescent : baseEnd_784572 < baseStart_784572 := by decide
  rcases family_descends (prefixWord ++ tailWord_784572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784576 : List Nat := [2, 1, 1, 2, 5, 3, 2, 1, 2, 4]
def baseStart_784576 : Nat := 118140960795 + 784576 * 2 ^ 59
def prefixEnd_784576 : Nat := 4983230072969 + 3 ^ 40 * 784576 * 2
def baseEnd_784576 : Nat := 134288199327342525497269

theorem tailTrace_784576 : CollatzResearch.WordTrace tailWord_784576 prefixEnd_784576 134288199327342525497269 := by
  unfold tailWord_784576
  simp only [CollatzResearch.WordTrace]
  refine ⟨14307918802811310879014791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19077225070415081172019721 14307918802811310879014791)
  ·
    refine ⟨21461878204216966318522187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14307918802811310879014791 21461878204216966318522187)
    ·
      refine ⟨32192817306325449477783281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21461878204216966318522187 32192817306325449477783281)
      ·
        refine ⟨24144612979744087108337461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32192817306325449477783281 24144612979744087108337461)
        ·
          refine ⟨2263557466851008166406637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24144612979744087108337461 2263557466851008166406637)
          ·
            refine ⟨848834050069128062402489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2263557466851008166406637 848834050069128062402489)
            ·
              refine ⟨636625537551846046801867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 848834050069128062402489 636625537551846046801867)
              ·
                refine ⟨954938306327769070202801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636625537551846046801867 954938306327769070202801)
                ·
                  refine ⟨716203729745826802652101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 954938306327769070202801 716203729745826802652101)
                  ·
                    refine ⟨134288199327342525497269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 716203729745826802652101 134288199327342525497269)
                    ·
                      rfl

theorem cell23_784576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 2, 4].length) (baseStart_784576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784576 prefixEnd_784576 := by exact prefixLift 784576
  have htrace : WordTrace (prefixWord ++ tailWord_784576) baseStart_784576 baseEnd_784576 := by
    simpa [prefixWord, tailWord_784576, baseEnd_784576] using wordTrace_append hprefix tailTrace_784576
  have hstable : (prefixWord ++ tailWord_784576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784576).length < 2 ^ (prefixWord ++ tailWord_784576).sum := by decide
  have hdescent : baseEnd_784576 < baseStart_784576 := by decide
  rcases family_descends (prefixWord ++ tailWord_784576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784610 : List Nat := [3, 3, 4, 1, 1, 1, 2, 2, 2, 4]
def baseStart_784610 : Nat := 118140960795 + 784610 * 2 ^ 59
def prefixEnd_784610 : Nat := 4983230072969 + 3 ^ 40 * 784610 * 2
def baseEnd_784610 : Nat := 134294018774760147822217

theorem tailTrace_784610 : CollatzResearch.WordTrace tailWord_784610 prefixEnd_784610 134294018774760147822217 := by
  unfold tailWord_784610
  simp only [CollatzResearch.WordTrace]
  refine ⟨7154269421874861391191821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19078051791666297043178189 7154269421874861391191821)
  ·
    refine ⟨2682851033203073021696933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7154269421874861391191821 2682851033203073021696933)
    ·
      refine ⟨503034568725576191568175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2682851033203073021696933 503034568725576191568175)
      ·
        refine ⟨754551853088364287352263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503034568725576191568175 754551853088364287352263)
        ·
          refine ⟨1131827779632546431028395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754551853088364287352263 1131827779632546431028395)
          ·
            refine ⟨1697741669448819646542593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131827779632546431028395 1697741669448819646542593)
            ·
              refine ⟨1273306252086614734906945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1697741669448819646542593 1273306252086614734906945)
              ·
                refine ⟨954979689064961051180209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1273306252086614734906945 954979689064961051180209)
                ·
                  refine ⟨716234766798720788385157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 954979689064961051180209 716234766798720788385157)
                  ·
                    refine ⟨134294018774760147822217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 716234766798720788385157 134294018774760147822217)
                    ·
                      rfl

theorem cell23_784610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_784610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784610 prefixEnd_784610 := by exact prefixLift 784610
  have htrace : WordTrace (prefixWord ++ tailWord_784610) baseStart_784610 baseEnd_784610 := by
    simpa [prefixWord, tailWord_784610, baseEnd_784610] using wordTrace_append hprefix tailTrace_784610
  have hstable : (prefixWord ++ tailWord_784610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784610).length < 2 ^ (prefixWord ++ tailWord_784610).sum := by decide
  have hdescent : baseEnd_784610 < baseStart_784610 := by decide
  rcases family_descends (prefixWord ++ tailWord_784610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784616 : List Nat := [2, 1, 4, 1, 2, 3, 2, 2, 2, 1, 3]
def baseStart_784616 : Nat := 118140960795 + 784616 * 2 ^ 59
def prefixEnd_784616 : Nat := 4983230072969 + 3 ^ 40 * 784616 * 2
def baseEnd_784616 : Nat := 402885137208207419991623

theorem tailTrace_784616 : CollatzResearch.WordTrace tailWord_784616 prefixEnd_784616 402885137208207419991623 := by
  unfold tailWord_784616
  simp only [CollatzResearch.WordTrace]
  refine ⟨14308648262738854294742851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19078197683651805726323801 14308648262738854294742851)
  ·
    refine ⟨21462972394108281442114277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14308648262738854294742851 21462972394108281442114277)
    ·
      refine ⟨4024307323895302770396427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21462972394108281442114277 4024307323895302770396427)
      ·
        refine ⟨6036460985842954155594641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4024307323895302770396427 6036460985842954155594641)
        ·
          refine ⟨4527345739382215616695981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6036460985842954155594641 4527345739382215616695981)
          ·
            refine ⟨1697754652268330856260993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4527345739382215616695981 1697754652268330856260993)
            ·
              refine ⟨1273315989201248142195745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1697754652268330856260993 1273315989201248142195745)
              ·
                refine ⟨954986991900936106646809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1273315989201248142195745 954986991900936106646809)
                ·
                  refine ⟨716240243925702079985107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 954986991900936106646809 716240243925702079985107)
                  ·
                    refine ⟨1074360365888553119977661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 716240243925702079985107 1074360365888553119977661)
                    ·
                      refine ⟨402885137208207419991623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1074360365888553119977661 402885137208207419991623)
                      ·
                        rfl

theorem cell23_784616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_784616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784616 prefixEnd_784616 := by exact prefixLift 784616
  have htrace : WordTrace (prefixWord ++ tailWord_784616) baseStart_784616 baseEnd_784616 := by
    simpa [prefixWord, tailWord_784616, baseEnd_784616] using wordTrace_append hprefix tailTrace_784616
  have hstable : (prefixWord ++ tailWord_784616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784616).length < 2 ^ (prefixWord ++ tailWord_784616).sum := by decide
  have hdescent : baseEnd_784616 < baseStart_784616 := by decide
  rcases family_descends (prefixWord ++ tailWord_784616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784625 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 1, 3, 5]
def baseStart_784625 : Nat := 118140960795 + 784625 * 2 ^ 59
def prefixEnd_784625 : Nat := 4983230072969 + 3 ^ 40 * 784625 * 2
def baseEnd_784625 : Nat := 402889758534097884779081

theorem tailTrace_784625 : CollatzResearch.WordTrace tailWord_784625 prefixEnd_784625 402889758534097884779081 := by
  unfold tailWord_784625
  simp only [CollatzResearch.WordTrace]
  refine ⟨28617624782445103126563329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19078416521630068751042219 28617624782445103126563329)
  ·
    refine ⟨21463218586833827344922497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28617624782445103126563329 21463218586833827344922497)
    ·
      refine ⟨16097413940125370508691873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21463218586833827344922497 16097413940125370508691873)
      ·
        refine ⟨12073060455094027881518905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16097413940125370508691873 12073060455094027881518905)
        ·
          refine ⟨9054795341320520911139179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12073060455094027881518905 9054795341320520911139179)
          ·
            refine ⟨13582193011980781366708769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9054795341320520911139179 13582193011980781366708769)
            ·
              refine ⟨10186644758985586025031577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13582193011980781366708769 10186644758985586025031577)
              ·
                refine ⟨7639983569239189518773683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10186644758985586025031577 7639983569239189518773683)
                ·
                  refine ⟨11459975353858784278160525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7639983569239189518773683 11459975353858784278160525)
                  ·
                    refine ⟨4297490757697044104310197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11459975353858784278160525 4297490757697044104310197)
                    ·
                      refine ⟨402889758534097884779081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4297490757697044104310197 402889758534097884779081)
                      ·
                        rfl

theorem cell23_784625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_784625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784625 prefixEnd_784625 := by exact prefixLift 784625
  have htrace : WordTrace (prefixWord ++ tailWord_784625) baseStart_784625 baseEnd_784625 := by
    simpa [prefixWord, tailWord_784625, baseEnd_784625] using wordTrace_append hprefix tailTrace_784625
  have hstable : (prefixWord ++ tailWord_784625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784625).length < 2 ^ (prefixWord ++ tailWord_784625).sum := by decide
  have hdescent : baseEnd_784625 < baseStart_784625 := by decide
  rcases family_descends (prefixWord ++ tailWord_784625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784639 : List Nat := [1, 1, 2, 2, 1, 4, 4, 1, 1, 4, 2]
def baseStart_784639 : Nat := 118140960795 + 784639 * 2 ^ 59
def prefixEnd_784639 : Nat := 4983230072969 + 3 ^ 40 * 784639 * 2
def baseEnd_784639 : Nat := 402896947263260830004017

theorem tailTrace_784639 : CollatzResearch.WordTrace tailWord_784639 prefixEnd_784639 402896947263260830004017 := by
  unfold tailWord_784639
  simp only [CollatzResearch.WordTrace]
  refine ⟨28618135404394383517572971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19078756936262922345048647 28618135404394383517572971)
  ·
    refine ⟨42927203106591575276359457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28618135404394383517572971 42927203106591575276359457)
    ·
      refine ⟨32195402329943681457269593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42927203106591575276359457 32195402329943681457269593)
      ·
        refine ⟨24146551747457761092952195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32195402329943681457269593 24146551747457761092952195)
        ·
          refine ⟨36219827621186641639428293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24146551747457761092952195 36219827621186641639428293)
          ·
            refine ⟨6791217678972495307392805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36219827621186641639428293 6791217678972495307392805)
            ·
              refine ⟨1273353314807342870136151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6791217678972495307392805 1273353314807342870136151)
              ·
                refine ⟨1910029972211014305204227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1273353314807342870136151 1910029972211014305204227)
                ·
                  refine ⟨2865044958316521457806341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1910029972211014305204227 2865044958316521457806341)
                  ·
                    refine ⟨537195929684347773338689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2865044958316521457806341 537195929684347773338689)
                    ·
                      refine ⟨402896947263260830004017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 537195929684347773338689 402896947263260830004017)
                      ·
                        rfl

theorem cell23_784639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 4, 2].length) (baseStart_784639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784639 prefixEnd_784639 := by exact prefixLift 784639
  have htrace : WordTrace (prefixWord ++ tailWord_784639) baseStart_784639 baseEnd_784639 := by
    simpa [prefixWord, tailWord_784639, baseEnd_784639] using wordTrace_append hprefix tailTrace_784639
  have hstable : (prefixWord ++ tailWord_784639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784639).length < 2 ^ (prefixWord ++ tailWord_784639).sum := by decide
  have hdescent : baseEnd_784639 < baseStart_784639 := by decide
  rcases family_descends (prefixWord ++ tailWord_784639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784690 : List Nat := [3, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2]
def baseStart_784690 : Nat := 118140960795 + 784690 * 2 ^ 59
def prefixEnd_784690 : Nat := 4983230072969 + 3 ^ 40 * 784690 * 2
def baseEnd_784690 : Nat := 402923134776640130466283

theorem tailTrace_784690 : CollatzResearch.WordTrace tailWord_784690 prefixEnd_784690 402923134776640130466283 := by
  unfold tailWord_784690
  simp only [CollatzResearch.WordTrace]
  refine ⟨7154998881802404806919881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19079997018139746151786349 7154998881802404806919881)
  ·
    refine ⟨5366249161351803605189911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7154998881802404806919881 5366249161351803605189911)
    ·
      refine ⟨8049373742027705407784867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5366249161351803605189911 8049373742027705407784867)
      ·
        refine ⟨12074060613041558111677301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8049373742027705407784867 12074060613041558111677301)
        ·
          refine ⟨1131943182472646072969747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12074060613041558111677301 1131943182472646072969747)
          ·
            refine ⟨1697914773708969109454621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131943182472646072969747 1697914773708969109454621)
            ·
              refine ⟨636718040140863416045483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1697914773708969109454621 636718040140863416045483)
              ·
                refine ⟨955077060211295124068225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636718040140863416045483 955077060211295124068225)
                ·
                  refine ⟨716307795158471343051169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 955077060211295124068225 716307795158471343051169)
                  ·
                    refine ⟨537230846368853507288377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 716307795158471343051169 537230846368853507288377)
                    ·
                      refine ⟨402923134776640130466283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 537230846368853507288377 402923134776640130466283)
                      ·
                        rfl

theorem cell23_784690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2].length) (baseStart_784690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784690 prefixEnd_784690 := by exact prefixLift 784690
  have htrace : WordTrace (prefixWord ++ tailWord_784690) baseStart_784690 baseEnd_784690 := by
    simpa [prefixWord, tailWord_784690, baseEnd_784690] using wordTrace_append hprefix tailTrace_784690
  have hstable : (prefixWord ++ tailWord_784690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784690).length < 2 ^ (prefixWord ++ tailWord_784690).sum := by decide
  have hdescent : baseEnd_784690 < baseStart_784690 := by decide
  rcases family_descends (prefixWord ++ tailWord_784690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784712 : List Nat := [2, 1, 3, 1, 1, 2, 4, 1, 1, 3, 4]
def baseStart_784712 : Nat := 118140960795 + 784712 * 2 ^ 59
def prefixEnd_784712 : Nat := 4983230072969 + 3 ^ 40 * 784712 * 2
def baseEnd_784712 : Nat := 402934431351039044391181

theorem tailTrace_784712 : CollatzResearch.WordTrace tailWord_784712 prefixEnd_784712 402934431351039044391181 := by
  unfold tailWord_784712
  simp only [CollatzResearch.WordTrace]
  refine ⟨14310398966564958492490195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19080531955419944656653593 14310398966564958492490195)
  ·
    refine ⟨21465598449847437738735293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14310398966564958492490195 21465598449847437738735293)
    ·
      refine ⟨8049599418692789152025735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21465598449847437738735293 8049599418692789152025735)
      ·
        refine ⟨12074399128039183728038603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8049599418692789152025735 12074399128039183728038603)
        ·
          refine ⟨18111598692058775592057905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12074399128039183728038603 18111598692058775592057905)
          ·
            refine ⟨13583699019044081694043429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18111598692058775592057905 13583699019044081694043429)
            ·
              refine ⟨2546943566070765317633143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13583699019044081694043429 2546943566070765317633143)
              ·
                refine ⟨3820415349106147976449715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2546943566070765317633143 3820415349106147976449715)
                ·
                  refine ⟨5730623023659221964674573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3820415349106147976449715 5730623023659221964674573)
                  ·
                    refine ⟨2148983633872208236752965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5730623023659221964674573 2148983633872208236752965)
                    ·
                      refine ⟨402934431351039044391181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2148983633872208236752965 402934431351039044391181)
                      ·
                        rfl

theorem cell23_784712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_784712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784712 prefixEnd_784712 := by exact prefixLift 784712
  have htrace : WordTrace (prefixWord ++ tailWord_784712) baseStart_784712 baseEnd_784712 := by
    simpa [prefixWord, tailWord_784712, baseEnd_784712] using wordTrace_append hprefix tailTrace_784712
  have hstable : (prefixWord ++ tailWord_784712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784712).length < 2 ^ (prefixWord ++ tailWord_784712).sum := by decide
  have hdescent : baseEnd_784712 < baseStart_784712 := by decide
  rcases family_descends (prefixWord ++ tailWord_784712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784749 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 4, 2, 3]
def baseStart_784749 : Nat := 118140960795 + 784749 * 2 ^ 59
def prefixEnd_784749 : Nat := 4983230072969 + 3 ^ 40 * 784749 * 2
def baseEnd_784749 : Nat := 402953430135255399628511

theorem tailTrace_784749 : CollatzResearch.WordTrace tailWord_784749 prefixEnd_784749 402953430135255399628511 := by
  unfold tailWord_784749
  simp only [CollatzResearch.WordTrace]
  refine ⟨28622147433995872304077301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19081431622663914869384867 28622147433995872304077301)
  ·
    refine ⟨2683326321937113028507247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28622147433995872304077301 2683326321937113028507247)
    ·
      refine ⟨4024989482905669542760871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2683326321937113028507247 4024989482905669542760871)
      ·
        refine ⟨6037484224358504314141307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4024989482905669542760871 6037484224358504314141307)
        ·
          refine ⟨9056226336537756471211961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6037484224358504314141307 9056226336537756471211961)
          ·
            refine ⟨6792169752403317353408971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9056226336537756471211961 6792169752403317353408971)
            ·
              refine ⟨10188254628604976030113457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6792169752403317353408971 10188254628604976030113457)
              ·
                refine ⟨7641190971453732022585093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10188254628604976030113457 7641190971453732022585093)
                ·
                  refine ⟨1432723307147574754234705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7641190971453732022585093 1432723307147574754234705)
                  ·
                    refine ⟨1074542480360681065676029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1432723307147574754234705 1074542480360681065676029)
                    ·
                      refine ⟨402953430135255399628511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1074542480360681065676029 402953430135255399628511)
                      ·
                        rfl

theorem cell23_784749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_784749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784749 prefixEnd_784749 := by exact prefixLift 784749
  have htrace : WordTrace (prefixWord ++ tailWord_784749) baseStart_784749 baseEnd_784749 := by
    simpa [prefixWord, tailWord_784749, baseEnd_784749] using wordTrace_append hprefix tailTrace_784749
  have hstable : (prefixWord ++ tailWord_784749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784749).length < 2 ^ (prefixWord ++ tailWord_784749).sum := by decide
  have hdescent : baseEnd_784749 < baseStart_784749 := by decide
  rcases family_descends (prefixWord ++ tailWord_784749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784789 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 3, 5, 2]
def baseStart_784789 : Nat := 118140960795 + 784789 * 2 ^ 59
def prefixEnd_784789 : Nat := 4983230072969 + 3 ^ 40 * 784789 * 2
def baseEnd_784789 : Nat := 402973969361435243128327

theorem tailTrace_784789 : CollatzResearch.WordTrace tailWord_784789 prefixEnd_784789 402973969361435243128327 := by
  unfold tailWord_784789
  simp only [CollatzResearch.WordTrace]
  refine ⟨28623606353850959135533421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19082404235900639423688947 28623606353850959135533421)
  ·
    refine ⟨10733852382694109675825033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28623606353850959135533421 10733852382694109675825033)
    ·
      refine ⟨8050389287020582256868775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10733852382694109675825033 8050389287020582256868775)
      ·
        refine ⟨12075583930530873385303163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8050389287020582256868775 12075583930530873385303163)
        ·
          refine ⟨18113375895796310077954745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12075583930530873385303163 18113375895796310077954745)
          ·
            refine ⟨13585031921847232558466059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18113375895796310077954745 13585031921847232558466059)
            ·
              refine ⟨20377547882770848837699089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13585031921847232558466059 20377547882770848837699089)
              ·
                refine ⟨15283160912078136628274317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20377547882770848837699089 15283160912078136628274317)
                ·
                  refine ⟨5731185342029301235602869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15283160912078136628274317 5731185342029301235602869)
                  ·
                    refine ⟨537298625815246990837769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5731185342029301235602869 537298625815246990837769)
                    ·
                      refine ⟨402973969361435243128327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 537298625815246990837769 402973969361435243128327)
                      ·
                        rfl

theorem cell23_784789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 5, 2].length) (baseStart_784789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784789 prefixEnd_784789 := by exact prefixLift 784789
  have htrace : WordTrace (prefixWord ++ tailWord_784789) baseStart_784789 baseEnd_784789 := by
    simpa [prefixWord, tailWord_784789, baseEnd_784789] using wordTrace_append hprefix tailTrace_784789
  have hstable : (prefixWord ++ tailWord_784789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784789).length < 2 ^ (prefixWord ++ tailWord_784789).sum := by decide
  have hdescent : baseEnd_784789 < baseStart_784789 := by decide
  rcases family_descends (prefixWord ++ tailWord_784789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784823 : List Nat := [1, 1, 3, 1, 3, 5, 1, 1, 2, 3, 2]
def baseStart_784823 : Nat := 118140960795 + 784823 * 2 ^ 59
def prefixEnd_784823 : Nat := 4983230072969 + 3 ^ 40 * 784823 * 2
def baseEnd_784823 : Nat := 402991427703688110103171

theorem tailTrace_784823 : CollatzResearch.WordTrace tailWord_784823 prefixEnd_784823 402991427703688110103171 := by
  unfold tailWord_784823
  simp only [CollatzResearch.WordTrace]
  refine ⟨28624846435727782942271123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19083230957151855294847415 28624846435727782942271123)
  ·
    refine ⟨42937269653591674413406685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28624846435727782942271123 42937269653591674413406685)
    ·
      refine ⟨16101476120096877905027507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42937269653591674413406685 16101476120096877905027507)
      ·
        refine ⟨24152214180145316857541261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16101476120096877905027507 24152214180145316857541261)
        ·
          refine ⟨9057080317554493821577973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24152214180145316857541261 9057080317554493821577973)
          ·
            refine ⟨849101279770733795772935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9057080317554493821577973 849101279770733795772935)
            ·
              refine ⟨1273651919656100693659403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849101279770733795772935 1273651919656100693659403)
              ·
                refine ⟨1910477879484151040489105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1273651919656100693659403 1910477879484151040489105)
                ·
                  refine ⟨1432858409613113280366829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1910477879484151040489105 1432858409613113280366829)
                  ·
                    refine ⟨537321903604917480137561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1432858409613113280366829 537321903604917480137561)
                    ·
                      refine ⟨402991427703688110103171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 537321903604917480137561 402991427703688110103171)
                      ·
                        rfl

theorem cell23_784823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 3, 2].length) (baseStart_784823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784823 prefixEnd_784823 := by exact prefixLift 784823
  have htrace : WordTrace (prefixWord ++ tailWord_784823) baseStart_784823 baseEnd_784823 := by
    simpa [prefixWord, tailWord_784823, baseEnd_784823] using wordTrace_append hprefix tailTrace_784823
  have hstable : (prefixWord ++ tailWord_784823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784823).length < 2 ^ (prefixWord ++ tailWord_784823).sum := by decide
  have hdescent : baseEnd_784823 < baseStart_784823 := by decide
  rcases family_descends (prefixWord ++ tailWord_784823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784829 : List Nat := [1, 4, 1, 2, 2, 2, 2, 2, 1, 6]
def baseStart_784829 : Nat := 118140960795 + 784829 * 2 ^ 59
def prefixEnd_784829 : Nat := 4983230072969 + 3 ^ 40 * 784829 * 2
def baseEnd_784829 : Nat := 134331502862538362209381

theorem tailTrace_784829 : CollatzResearch.WordTrace tailWord_784829 prefixEnd_784829 134331502862538362209381 := by
  unfold tailWord_784829
  simp only [CollatzResearch.WordTrace]
  refine ⟨28625065273706045966989541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19083376849137363977993027 28625065273706045966989541)
  ·
    refine ⟨5367199738819883618810539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28625065273706045966989541 5367199738819883618810539)
    ·
      refine ⟨8050799608229825428215809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5367199738819883618810539 8050799608229825428215809)
      ·
        refine ⟨6038099706172369071161857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8050799608229825428215809 6038099706172369071161857)
        ·
          refine ⟨4528574779629276803371393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6038099706172369071161857 4528574779629276803371393)
          ·
            refine ⟨3396431084721957602528545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4528574779629276803371393 3396431084721957602528545)
            ·
              refine ⟨2547323313541468201896409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3396431084721957602528545 2547323313541468201896409)
              ·
                refine ⟨1910492485156101151422307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2547323313541468201896409 1910492485156101151422307)
                ·
                  refine ⟨2865738727734151727133461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1910492485156101151422307 2865738727734151727133461)
                  ·
                    refine ⟨134331502862538362209381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2865738727734151727133461 134331502862538362209381)
                    ·
                      rfl

theorem cell23_784829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_784829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784829 prefixEnd_784829 := by exact prefixLift 784829
  have htrace : WordTrace (prefixWord ++ tailWord_784829) baseStart_784829 baseEnd_784829 := by
    simpa [prefixWord, tailWord_784829, baseEnd_784829] using wordTrace_append hprefix tailTrace_784829
  have hstable : (prefixWord ++ tailWord_784829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784829).length < 2 ^ (prefixWord ++ tailWord_784829).sum := by decide
  have hdescent : baseEnd_784829 < baseStart_784829 := by decide
  rcases family_descends (prefixWord ++ tailWord_784829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784832 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 6]
def baseStart_784832 : Nat := 118140960795 + 784832 * 2 ^ 59
def prefixEnd_784832 : Nat := 4983230072969 + 3 ^ 40 * 784832 * 2
def baseEnd_784832 : Nat := 402996049029578574890629

theorem tailTrace_784832 : CollatzResearch.WordTrace tailWord_784832 prefixEnd_784832 402996049029578574890629 := by
  unfold tailWord_784832
  simp only [CollatzResearch.WordTrace]
  refine ⟨14312587346347588739674375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19083449795130118319565833 14312587346347588739674375)
  ·
    refine ⟨21468881019521383109511563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14312587346347588739674375 21468881019521383109511563)
    ·
      refine ⟨32203321529282074664267345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21468881019521383109511563 32203321529282074664267345)
      ·
        refine ⟨24152491146961555998200509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32203321529282074664267345 24152491146961555998200509)
        ·
          refine ⟨9057184180110583499325191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24152491146961555998200509 9057184180110583499325191)
          ·
            refine ⟨13585776270165875248987787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9057184180110583499325191 13585776270165875248987787)
            ·
              refine ⟨20378664405248812873481681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13585776270165875248987787 20378664405248812873481681)
              ·
                refine ⟨15283998303936609655111261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20378664405248812873481681 15283998303936609655111261)
                ·
                  refine ⟨5731499363976228620666723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15283998303936609655111261 5731499363976228620666723)
                  ·
                    refine ⟨8597249045964342931000085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5731499363976228620666723 8597249045964342931000085)
                    ·
                      refine ⟨402996049029578574890629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8597249045964342931000085 402996049029578574890629)
                      ·
                        rfl

theorem cell23_784832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_784832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784832 prefixEnd_784832 := by exact prefixLift 784832
  have htrace : WordTrace (prefixWord ++ tailWord_784832) baseStart_784832 baseEnd_784832 := by
    simpa [prefixWord, tailWord_784832, baseEnd_784832] using wordTrace_append hprefix tailTrace_784832
  have hstable : (prefixWord ++ tailWord_784832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784832).length < 2 ^ (prefixWord ++ tailWord_784832).sum := by decide
  have hdescent : baseEnd_784832 < baseStart_784832 := by decide
  rcases family_descends (prefixWord ++ tailWord_784832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784842 : List Nat := [3, 1, 2, 1, 2, 2, 12]
def baseStart_784842 : Nat := 118140960795 + 784842 * 2 ^ 59
def prefixEnd_784842 : Nat := 4983230072969 + 3 ^ 40 * 784842 * 2
def baseEnd_784842 : Nat := 4975323257236093034143

theorem tailTrace_784842 : CollatzResearch.WordTrace tailWord_784842 prefixEnd_784842 4975323257236093034143 := by
  unfold tailWord_784842
  simp only [CollatzResearch.WordTrace]
  refine ⟨7156384855664737296803195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19083692948439299458141853 7156384855664737296803195)
  ·
    refine ⟨10734577283497105945204793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7156384855664737296803195 10734577283497105945204793)
    ·
      refine ⟨8050932962622829458903595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10734577283497105945204793 8050932962622829458903595)
      ·
        refine ⟨12076399443934244188355393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8050932962622829458903595 12076399443934244188355393)
        ·
          refine ⟨9057299582950683141266545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12076399443934244188355393 9057299582950683141266545)
          ·
            refine ⟨6792974687213012355949909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9057299582950683141266545 6792974687213012355949909)
            ·
              refine ⟨4975323257236093034143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 6792974687213012355949909 4975323257236093034143)
              ·
                rfl

theorem cell23_784842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 12].length) (baseStart_784842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784842 prefixEnd_784842 := by exact prefixLift 784842
  have htrace : WordTrace (prefixWord ++ tailWord_784842) baseStart_784842 baseEnd_784842 := by
    simpa [prefixWord, tailWord_784842, baseEnd_784842] using wordTrace_append hprefix tailTrace_784842
  have hstable : (prefixWord ++ tailWord_784842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784842).length < 2 ^ (prefixWord ++ tailWord_784842).sum := by decide
  have hdescent : baseEnd_784842 < baseStart_784842 := by decide
  rcases family_descends (prefixWord ++ tailWord_784842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784853 : List Nat := [1, 3, 2, 3, 1, 2, 1, 3, 3, 2, 2]
def baseStart_784853 : Nat := 118140960795 + 784853 * 2 ^ 59
def prefixEnd_784853 : Nat := 4983230072969 + 3 ^ 40 * 784853 * 2
def baseEnd_784853 : Nat := 403006832123322992728033

theorem tailTrace_784853 : CollatzResearch.WordTrace tailWord_784853 prefixEnd_784853 403006832123322992728033 := by
  unfold tailWord_784853
  simp only [CollatzResearch.WordTrace]
  refine ⟨28625940625619098065863213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19083960417079398710575475 28625940625619098065863213)
  ·
    refine ⟨10734727734607161774698705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28625940625619098065863213 10734727734607161774698705)
    ·
      refine ⟨8051045800955371331024029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10734727734607161774698705 8051045800955371331024029)
      ·
        refine ⟨3019142175358264249134011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8051045800955371331024029 3019142175358264249134011)
        ·
          refine ⟨4528713263037396373701017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3019142175358264249134011 4528713263037396373701017)
          ·
            refine ⟨3396534947278047280275763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4528713263037396373701017 3396534947278047280275763)
            ·
              refine ⟨5094802420917070920413645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3396534947278047280275763 5094802420917070920413645)
              ·
                refine ⟨1910550907843901595155117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5094802420917070920413645 1910550907843901595155117)
                ·
                  refine ⟨716456590441463098183169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1910550907843901595155117 716456590441463098183169)
                  ·
                    refine ⟨537342442831097323637377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 716456590441463098183169 537342442831097323637377)
                    ·
                      refine ⟨403006832123322992728033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 537342442831097323637377 403006832123322992728033)
                      ·
                        rfl

theorem cell23_784853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_784853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784853 prefixEnd_784853 := by exact prefixLift 784853
  have htrace : WordTrace (prefixWord ++ tailWord_784853) baseStart_784853 baseEnd_784853 := by
    simpa [prefixWord, tailWord_784853, baseEnd_784853] using wordTrace_append hprefix tailTrace_784853
  have hstable : (prefixWord ++ tailWord_784853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784853).length < 2 ^ (prefixWord ++ tailWord_784853).sum := by decide
  have hdescent : baseEnd_784853 < baseStart_784853 := by decide
  rcases family_descends (prefixWord ++ tailWord_784853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784863 : List Nat := [1, 1, 2, 3, 3, 3, 3, 1, 2, 4]
def baseStart_784863 : Nat := 118140960795 + 784863 * 2 ^ 59
def prefixEnd_784863 : Nat := 4983230072969 + 3 ^ 40 * 784863 * 2
def baseEnd_784863 : Nat := 134337322309955984534329

theorem tailTrace_784863 : CollatzResearch.WordTrace tailWord_784863 prefixEnd_784863 134337322309955984534329 := by
  unfold tailWord_784863
  simp only [CollatzResearch.WordTrace]
  refine ⟨28626305355582869773727243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19084203570388579849151495 28626305355582869773727243)
  ·
    refine ⟨42939458033374304660590865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28626305355582869773727243 42939458033374304660590865)
    ·
      refine ⟨32204593525030728495443149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42939458033374304660590865 32204593525030728495443149)
      ·
        refine ⟨12076722571886523185791181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32204593525030728495443149 12076722571886523185791181)
        ·
          refine ⟨4528770964457446194671693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12076722571886523185791181 4528770964457446194671693)
          ·
            refine ⟨1698289111671542323001885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4528770964457446194671693 1698289111671542323001885)
            ·
              refine ⟨636858416876828371125707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1698289111671542323001885 636858416876828371125707)
              ·
                refine ⟨955287625315242556688561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636858416876828371125707 955287625315242556688561)
                ·
                  refine ⟨716465718986431917516421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 955287625315242556688561 716465718986431917516421)
                  ·
                    refine ⟨134337322309955984534329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 716465718986431917516421 134337322309955984534329)
                    ·
                      rfl

theorem cell23_784863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 2, 4].length) (baseStart_784863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784863 prefixEnd_784863 := by exact prefixLift 784863
  have htrace : WordTrace (prefixWord ++ tailWord_784863) baseStart_784863 baseEnd_784863 := by
    simpa [prefixWord, tailWord_784863, baseEnd_784863] using wordTrace_append hprefix tailTrace_784863
  have hstable : (prefixWord ++ tailWord_784863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784863).length < 2 ^ (prefixWord ++ tailWord_784863).sum := by decide
  have hdescent : baseEnd_784863 < baseStart_784863 := by decide
  rcases family_descends (prefixWord ++ tailWord_784863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784886 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3]
def baseStart_784886 : Nat := 118140960795 + 784886 * 2 ^ 59
def prefixEnd_784886 : Nat := 4983230072969 + 3 ^ 40 * 784886 * 2
def baseEnd_784886 : Nat := 403023776984921363615381

theorem tailTrace_784886 : CollatzResearch.WordTrace tailWord_784886 prefixEnd_784886 403023776984921363615381 := by
  unfold tailWord_784886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1789196514656221543863407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19084762822999696467876341 1789196514656221543863407)
  ·
    refine ⟨2683794771984332315795111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1789196514656221543863407 2683794771984332315795111)
    ·
      refine ⟨4025692157976498473692667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2683794771984332315795111 4025692157976498473692667)
      ·
        refine ⟨6038538236964747710539001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4025692157976498473692667 6038538236964747710539001)
        ·
          refine ⟨4528903677723560782904251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6038538236964747710539001 4528903677723560782904251)
          ·
            refine ⟨6793355516585341174356377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4528903677723560782904251 6793355516585341174356377)
            ·
              refine ⟨5095016637439005880767283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6793355516585341174356377 5095016637439005880767283)
              ·
                refine ⟨7642524956158508821150925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5095016637439005880767283 7642524956158508821150925)
                ·
                  refine ⟨2865946858559440807931597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7642524956158508821150925 2865946858559440807931597)
                  ·
                    refine ⟨1074730071959790302974349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2865946858559440807931597 1074730071959790302974349)
                    ·
                      refine ⟨403023776984921363615381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1074730071959790302974349 403023776984921363615381)
                      ·
                        rfl

theorem cell23_784886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_784886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784886 prefixEnd_784886 := by exact prefixLift 784886
  have htrace : WordTrace (prefixWord ++ tailWord_784886) baseStart_784886 baseEnd_784886 := by
    simpa [prefixWord, tailWord_784886, baseEnd_784886] using wordTrace_append hprefix tailTrace_784886
  have hstable : (prefixWord ++ tailWord_784886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784886).length < 2 ^ (prefixWord ++ tailWord_784886).sum := by decide
  have hdescent : baseEnd_784886 < baseStart_784886 := by decide
  rcases family_descends (prefixWord ++ tailWord_784886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784920 : List Nat := [2, 1, 2, 3, 3, 1, 4, 1, 2, 1, 3]
def baseStart_784920 : Nat := 118140960795 + 784920 * 2 ^ 59
def prefixEnd_784920 : Nat := 4983230072969 + 3 ^ 40 * 784920 * 2
def baseEnd_784920 : Nat := 403041235327174230590225

theorem tailTrace_784920 : CollatzResearch.WordTrace tailWord_784920 prefixEnd_784920 403041235327174230590225 := by
  unfold tailWord_784920
  simp only [CollatzResearch.WordTrace]
  refine ⟨14314192158188184254276107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19085589544250912339034809 14314192158188184254276107)
  ·
    refine ⟨21471288237282276381414161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14314192158188184254276107 21471288237282276381414161)
    ·
      refine ⟨16103466177961707286060621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21471288237282276381414161 16103466177961707286060621)
      ·
        refine ⟨6038799816735640232272733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16103466177961707286060621 6038799816735640232272733)
        ·
          refine ⟨2264549931275865087102275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6038799816735640232272733 2264549931275865087102275)
          ·
            refine ⟨3396824896913797630653413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2264549931275865087102275 3396824896913797630653413)
            ·
              refine ⟨636904668171337055747515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3396824896913797630653413 636904668171337055747515)
              ·
                refine ⟨955357002257005583621273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636904668171337055747515 955357002257005583621273)
                ·
                  refine ⟨716517751692754187715955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 955357002257005583621273 716517751692754187715955)
                  ·
                    refine ⟨1074776627539131281573933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 716517751692754187715955 1074776627539131281573933)
                    ·
                      refine ⟨403041235327174230590225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1074776627539131281573933 403041235327174230590225)
                      ·
                        rfl

theorem cell23_784920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_784920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784920 prefixEnd_784920 := by exact prefixLift 784920
  have htrace : WordTrace (prefixWord ++ tailWord_784920) baseStart_784920 baseEnd_784920 := by
    simpa [prefixWord, tailWord_784920, baseEnd_784920] using wordTrace_append hprefix tailTrace_784920
  have hstable : (prefixWord ++ tailWord_784920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784920).length < 2 ^ (prefixWord ++ tailWord_784920).sum := by decide
  have hdescent : baseEnd_784920 < baseStart_784920 := by decide
  rcases family_descends (prefixWord ++ tailWord_784920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784929 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 4, 1, 5]
def baseStart_784929 : Nat := 118140960795 + 784929 * 2 ^ 59
def prefixEnd_784929 : Nat := 4983230072969 + 3 ^ 40 * 784929 * 2
def baseEnd_784929 : Nat := 403045856653064695377683

theorem tailTrace_784929 : CollatzResearch.WordTrace tailWord_784929 prefixEnd_784929 403045856653064695377683 := by
  unfold tailWord_784929
  simp only [CollatzResearch.WordTrace]
  refine ⟨28628712573343763045629841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19085808382229175363753227 28628712573343763045629841)
  ·
    refine ⟨21471534430007822284222381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28628712573343763045629841 21471534430007822284222381)
    ·
      refine ⟨8051825411252933356583393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21471534430007822284222381 8051825411252933356583393)
      ·
        refine ⟨6038869058439700017437545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8051825411252933356583393 6038869058439700017437545)
        ·
          refine ⟨4529151793829775013078159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6038869058439700017437545 4529151793829775013078159)
          ·
            refine ⟨6793727690744662519617239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4529151793829775013078159 6793727690744662519617239)
            ·
              refine ⟨10190591536116993779425859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6793727690744662519617239 10190591536116993779425859)
              ·
                refine ⟨15285887304175490669138789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10190591536116993779425859 15285887304175490669138789)
                ·
                  refine ⟨2866103869532904500463523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15285887304175490669138789 2866103869532904500463523)
                  ·
                    refine ⟨4299155804299356750695285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2866103869532904500463523 4299155804299356750695285)
                    ·
                      refine ⟨403045856653064695377683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4299155804299356750695285 403045856653064695377683)
                      ·
                        rfl

theorem cell23_784929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_784929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784929 prefixEnd_784929 := by exact prefixLift 784929
  have htrace : WordTrace (prefixWord ++ tailWord_784929) baseStart_784929 baseEnd_784929 := by
    simpa [prefixWord, tailWord_784929, baseEnd_784929] using wordTrace_append hprefix tailTrace_784929
  have hstable : (prefixWord ++ tailWord_784929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784929).length < 2 ^ (prefixWord ++ tailWord_784929).sum := by decide
  have hdescent : baseEnd_784929 < baseStart_784929 := by decide
  rcases family_descends (prefixWord ++ tailWord_784929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784973 : List Nat := [1, 6, 1, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_784973 : Nat := 118140960795 + 784973 * 2 ^ 59
def prefixEnd_784973 : Nat := 4983230072969 + 3 ^ 40 * 784973 * 2
def baseEnd_784973 : Nat := 403068449801862523227481

theorem tailTrace_784973 : CollatzResearch.WordTrace tailWord_784973 prefixEnd_784973 403068449801862523227481 := by
  unfold tailWord_784973
  simp only [CollatzResearch.WordTrace]
  refine ⟨28630317385184358560231573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19086878256789572373487715 28630317385184358560231573)
  ·
    refine ⟨1342046127430516807510855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28630317385184358560231573 1342046127430516807510855)
    ·
      refine ⟨2013069191145775211266283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1342046127430516807510855 2013069191145775211266283)
      ·
        refine ⟨3019603786718662816899425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2013069191145775211266283 3019603786718662816899425)
        ·
          refine ⟨2264702840038997112674569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3019603786718662816899425 2264702840038997112674569)
          ·
            refine ⟨1698527130029247834505927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2264702840038997112674569 1698527130029247834505927)
            ·
              refine ⟨2547790695043871751758891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1698527130029247834505927 2547790695043871751758891)
              ·
                refine ⟨3821686042565807627638337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2547790695043871751758891 3821686042565807627638337)
                ·
                  refine ⟨2866264531924355720728753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3821686042565807627638337 2866264531924355720728753)
                  ·
                    refine ⟨2149698398943266790546565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2866264531924355720728753 2149698398943266790546565)
                    ·
                      refine ⟨403068449801862523227481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2149698398943266790546565 403068449801862523227481)
                      ·
                        rfl

theorem cell23_784973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_784973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_784973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_784973 prefixEnd_784973 := by exact prefixLift 784973
  have htrace : WordTrace (prefixWord ++ tailWord_784973) baseStart_784973 baseEnd_784973 := by
    simpa [prefixWord, tailWord_784973, baseEnd_784973] using wordTrace_append hprefix tailTrace_784973
  have hstable : (prefixWord ++ tailWord_784973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784973).length < 2 ^ (prefixWord ++ tailWord_784973).sum := by decide
  have hdescent : baseEnd_784973 < baseStart_784973 := by decide
  rcases family_descends (prefixWord ++ tailWord_784973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785000 : List Nat := [2, 1, 4, 3, 2, 1, 2, 3, 5]
def baseStart_785000 : Nat := 118140960795 + 785000 * 2 ^ 59
def prefixEnd_785000 : Nat := 4983230072969 + 3 ^ 40 * 785000 * 2
def baseEnd_785000 : Nat := 44786923753281546398873

theorem tailTrace_785000 : CollatzResearch.WordTrace tailWord_785000 prefixEnd_785000 44786923753281546398873 := by
  unfold tailWord_785000
  simp only [CollatzResearch.WordTrace]
  refine ⟨14315651078043271085732227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19087534770724361447642969 14315651078043271085732227)
  ·
    refine ⟨21473476617064906628598341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14315651078043271085732227 21473476617064906628598341)
    ·
      refine ⟨4026276865699669992862189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21473476617064906628598341 4026276865699669992862189)
      ·
        refine ⟨1509853824637376247323321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4026276865699669992862189 1509853824637376247323321)
        ·
          refine ⟨1132390368478032185492491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1509853824637376247323321 1132390368478032185492491)
          ·
            refine ⟨1698585552717048278238737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1132390368478032185492491 1698585552717048278238737)
            ·
              refine ⟨1273939164537786208679053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1698585552717048278238737 1273939164537786208679053)
              ·
                refine ⟨477727186701669828254645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1273939164537786208679053 477727186701669828254645)
                ·
                  refine ⟨44786923753281546398873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 477727186701669828254645 44786923753281546398873)
                  ·
                    rfl

theorem cell23_785000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3, 5].length) (baseStart_785000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785000 prefixEnd_785000 := by exact prefixLift 785000
  have htrace : WordTrace (prefixWord ++ tailWord_785000) baseStart_785000 baseEnd_785000 := by
    simpa [prefixWord, tailWord_785000, baseEnd_785000] using wordTrace_append hprefix tailTrace_785000
  have hstable : (prefixWord ++ tailWord_785000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785000).length < 2 ^ (prefixWord ++ tailWord_785000).sum := by decide
  have hdescent : baseEnd_785000 < baseStart_785000 := by decide
  rcases family_descends (prefixWord ++ tailWord_785000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785016 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 3, 6, 2]
def baseStart_785016 : Nat := 118140960795 + 785016 * 2 ^ 59
def prefixEnd_785016 : Nat := 4983230072969 + 3 ^ 40 * 785016 * 2
def baseEnd_785016 : Nat := 403090529470005854989783

theorem tailTrace_785016 : CollatzResearch.WordTrace tailWord_785016 prefixEnd_785016 403090529470005854989783 := by
  unfold tailWord_785016
  simp only [CollatzResearch.WordTrace]
  refine ⟨14315942862014288452023451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19087923816019051269364601 14315942862014288452023451)
  ·
    refine ⟨21473914293021432678035177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14315942862014288452023451 21473914293021432678035177)
    ·
      refine ⟨16105435719766074508526383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21473914293021432678035177 16105435719766074508526383)
      ·
        refine ⟨24158153579649111762789575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16105435719766074508526383 24158153579649111762789575)
        ·
          refine ⟨36237230369473667644184363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24158153579649111762789575 36237230369473667644184363)
          ·
            refine ⟨54355845554210501466276545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36237230369473667644184363 54355845554210501466276545)
            ·
              refine ⟨40766884165657876099707409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54355845554210501466276545 40766884165657876099707409)
              ·
                refine ⟨30575163124243407074780557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40766884165657876099707409 30575163124243407074780557)
                ·
                  refine ⟨11465686171591277653042709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30575163124243407074780557 11465686171591277653042709)
                  ·
                    refine ⟨537454039293341139986377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11465686171591277653042709 537454039293341139986377)
                    ·
                      refine ⟨403090529470005854989783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 537454039293341139986377 403090529470005854989783)
                      ·
                        rfl

theorem cell23_785016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 6, 2].length) (baseStart_785016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785016 prefixEnd_785016 := by exact prefixLift 785016
  have htrace : WordTrace (prefixWord ++ tailWord_785016) baseStart_785016 baseEnd_785016 := by
    simpa [prefixWord, tailWord_785016, baseEnd_785016] using wordTrace_append hprefix tailTrace_785016
  have hstable : (prefixWord ++ tailWord_785016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785016).length < 2 ^ (prefixWord ++ tailWord_785016).sum := by decide
  have hdescent : baseEnd_785016 < baseStart_785016 := by decide
  rcases family_descends (prefixWord ++ tailWord_785016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785036 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 6, 2, 3]
def baseStart_785036 : Nat := 118140960795 + 785036 * 2 ^ 59
def prefixEnd_785036 : Nat := 4983230072969 + 3 ^ 40 * 785036 * 2
def baseEnd_785036 : Nat := 403100799083095776739691

theorem tailTrace_785036 : CollatzResearch.WordTrace tailWord_785036 prefixEnd_785036 403100799083095776739691 := by
  unfold tailWord_785036
  simp only [CollatzResearch.WordTrace]
  refine ⟨14316307591978060159887481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19088410122637413546516641 14316307591978060159887481)
  ·
    refine ⟨10737230693983545119915611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14316307591978060159887481 10737230693983545119915611)
    ·
      refine ⟨16105846040975317679873417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10737230693983545119915611 16105846040975317679873417)
      ·
        refine ⟨12079384530731488259905063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16105846040975317679873417 12079384530731488259905063)
        ·
          refine ⟨18119076796097232389857595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12079384530731488259905063 18119076796097232389857595)
          ·
            refine ⟨27178615194145848584786393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18119076796097232389857595 27178615194145848584786393)
            ·
              refine ⟨20383961395609386438589795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27178615194145848584786393 20383961395609386438589795)
              ·
                refine ⟨30575942093414079657884693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20383961395609386438589795 30575942093414079657884693)
                ·
                  refine ⟨1433247285628784983963345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30575942093414079657884693 1433247285628784983963345)
                  ·
                    refine ⟨1074935464221588737972509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1433247285628784983963345 1074935464221588737972509)
                    ·
                      refine ⟨403100799083095776739691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1074935464221588737972509 403100799083095776739691)
                      ·
                        rfl

theorem cell23_785036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_785036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785036 prefixEnd_785036 := by exact prefixLift 785036
  have htrace : WordTrace (prefixWord ++ tailWord_785036) baseStart_785036 baseEnd_785036 := by
    simpa [prefixWord, tailWord_785036, baseEnd_785036] using wordTrace_append hprefix tailTrace_785036
  have hstable : (prefixWord ++ tailWord_785036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785036).length < 2 ^ (prefixWord ++ tailWord_785036).sum := by decide
  have hdescent : baseEnd_785036 < baseStart_785036 := by decide
  rcases family_descends (prefixWord ++ tailWord_785036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785059 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 8]
def baseStart_785059 : Nat := 118140960795 + 785059 * 2 ^ 59
def prefixEnd_785059 : Nat := 4983230072969 + 3 ^ 40 * 785059 * 2
def baseEnd_785059 : Nat := 403112609138149186752085

theorem tailTrace_785059 : CollatzResearch.WordTrace tailWord_785059 prefixEnd_785059 403112609138149186752085 := by
  unfold tailWord_785059
  simp only [CollatzResearch.WordTrace]
  refine ⟨28633454062872795247862231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19088969375248530165241487 28633454062872795247862231)
  ·
    refine ⟨42950181094309192871793347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28633454062872795247862231 42950181094309192871793347)
    ·
      refine ⟨64425271641463789307690021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42950181094309192871793347 64425271641463789307690021)
      ·
        refine ⟨12079738432774460495191879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64425271641463789307690021 12079738432774460495191879)
        ·
          refine ⟨18119607649161690742787819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12079738432774460495191879 18119607649161690742787819)
          ·
            refine ⟨27179411473742536114181729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18119607649161690742787819 27179411473742536114181729)
            ·
              refine ⟨20384558605306902085636297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27179411473742536114181729 20384558605306902085636297)
              ·
                refine ⟨15288418953980176564227223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20384558605306902085636297 15288418953980176564227223)
                ·
                  refine ⟨22932628430970264846340835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15288418953980176564227223 22932628430970264846340835)
                  ·
                    refine ⟨34398942646455397269511253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22932628430970264846340835 34398942646455397269511253)
                    ·
                      refine ⟨403112609138149186752085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 34398942646455397269511253 403112609138149186752085)
                      ·
                        rfl

theorem cell23_785059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_785059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785059 prefixEnd_785059 := by exact prefixLift 785059
  have htrace : WordTrace (prefixWord ++ tailWord_785059) baseStart_785059 baseEnd_785059 := by
    simpa [prefixWord, tailWord_785059, baseEnd_785059] using wordTrace_append hprefix tailTrace_785059
  have hstable : (prefixWord ++ tailWord_785059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785059).length < 2 ^ (prefixWord ++ tailWord_785059).sum := by decide
  have hdescent : baseEnd_785059 < baseStart_785059 := by decide
  rcases family_descends (prefixWord ++ tailWord_785059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785070 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_785070 : Nat := 118140960795 + 785070 * 2 ^ 59
def prefixEnd_785070 : Nat := 4983230072969 + 3 ^ 40 * 785070 * 2
def baseEnd_785070 : Nat := 403118257425348643714535

theorem tailTrace_785070 : CollatzResearch.WordTrace tailWord_785070 prefixEnd_785070 403118257425348643714535 := by
  unfold tailWord_785070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3579231908229118015814083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19089236843888629417675109 3579231908229118015814083)
  ·
    refine ⟨5368847862343677023721125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3579231908229118015814083 5368847862343677023721125)
    ·
      refine ⟨1006658974189439441947711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5368847862343677023721125 1006658974189439441947711)
      ·
        refine ⟨1509988461284159162921567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1006658974189439441947711 1509988461284159162921567)
        ·
          refine ⟨2264982691926238744382351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1509988461284159162921567 2264982691926238744382351)
          ·
            refine ⟨3397474037889358116573527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2264982691926238744382351 3397474037889358116573527)
            ·
              refine ⟨5096211056834037174860291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3397474037889358116573527 5096211056834037174860291)
              ·
                refine ⟨7644316585251055762290437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5096211056834037174860291 7644316585251055762290437)
                ·
                  refine ⟨1433309359734572955429457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7644316585251055762290437 1433309359734572955429457)
                  ·
                    refine ⟨1074982019800929716572093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1433309359734572955429457 1074982019800929716572093)
                    ·
                      refine ⟨403118257425348643714535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1074982019800929716572093 403118257425348643714535)
                      ·
                        rfl

theorem cell23_785070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_785070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785070 prefixEnd_785070 := by exact prefixLift 785070
  have htrace : WordTrace (prefixWord ++ tailWord_785070) baseStart_785070 baseEnd_785070 := by
    simpa [prefixWord, tailWord_785070, baseEnd_785070] using wordTrace_append hprefix tailTrace_785070
  have hstable : (prefixWord ++ tailWord_785070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785070).length < 2 ^ (prefixWord ++ tailWord_785070).sum := by decide
  have hdescent : baseEnd_785070 < baseStart_785070 := by decide
  rcases family_descends (prefixWord ++ tailWord_785070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785134 : List Nat := [4, 1, 2, 1, 1, 3, 4, 2, 1, 1, 3]
def baseStart_785134 : Nat := 118140960795 + 785134 * 2 ^ 59
def prefixEnd_785134 : Nat := 4983230072969 + 3 ^ 40 * 785134 * 2
def baseEnd_785134 : Nat := 403151120187236393314241

theorem tailTrace_785134 : CollatzResearch.WordTrace tailWord_785134 prefixEnd_785134 403151120187236393314241 := by
  unfold tailWord_785134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3579523692200135382105307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19090793025067388704561637 3579523692200135382105307)
  ·
    refine ⟨5369285538300203073157961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3579523692200135382105307 5369285538300203073157961)
    ·
      refine ⟨4026964153725152304868471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5369285538300203073157961 4026964153725152304868471)
      ·
        refine ⟨6040446230587728457302707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4026964153725152304868471 6040446230587728457302707)
        ·
          refine ⟨9060669345881592685954061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6040446230587728457302707 9060669345881592685954061)
          ·
            refine ⟨3397751004705597257232773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9060669345881592685954061 3397751004705597257232773)
            ·
              refine ⟨637078313382299485731145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3397751004705597257232773 637078313382299485731145)
              ·
                refine ⟨477808735036724614298359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 637078313382299485731145 477808735036724614298359)
                ·
                  refine ⟨716713102555086921447539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 477808735036724614298359 716713102555086921447539)
                  ·
                    refine ⟨1075069653832630382171309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 716713102555086921447539 1075069653832630382171309)
                    ·
                      refine ⟨403151120187236393314241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1075069653832630382171309 403151120187236393314241)
                      ·
                        rfl

theorem cell23_785134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_785134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785134 prefixEnd_785134 := by exact prefixLift 785134
  have htrace : WordTrace (prefixWord ++ tailWord_785134) baseStart_785134 baseEnd_785134 := by
    simpa [prefixWord, tailWord_785134, baseEnd_785134] using wordTrace_append hprefix tailTrace_785134
  have hstable : (prefixWord ++ tailWord_785134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785134).length < 2 ^ (prefixWord ++ tailWord_785134).sum := by decide
  have hdescent : baseEnd_785134 < baseStart_785134 := by decide
  rcases family_descends (prefixWord ++ tailWord_785134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785136 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 4]
def baseStart_785136 : Nat := 118140960795 + 785136 * 2 ^ 59
def prefixEnd_785136 : Nat := 4983230072969 + 3 ^ 40 * 785136 * 2
def baseEnd_785136 : Nat := 403152147148545385489231

theorem tailTrace_785136 : CollatzResearch.WordTrace tailWord_785136 prefixEnd_785136 403152147148545385489231 := by
  unfold tailWord_785136
  simp only [CollatzResearch.WordTrace]
  refine ⟨14318131241796918699207631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19090841655729224932276841 14318131241796918699207631)
  ·
    refine ⟨21477196862695378048811447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14318131241796918699207631 21477196862695378048811447)
    ·
      refine ⟨32215795294043067073217171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21477196862695378048811447 32215795294043067073217171)
      ·
        refine ⟨48323692941064600609825757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32215795294043067073217171 48323692941064600609825757)
        ·
          refine ⟨18121384852899225228684659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48323692941064600609825757 18121384852899225228684659)
          ·
            refine ⟨27182077279348837843026989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18121384852899225228684659 27182077279348837843026989)
            ·
              refine ⟨10193278979755814191135121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27182077279348837843026989 10193278979755814191135121)
              ·
                refine ⟨7644959234816860643351341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10193278979755814191135121 7644959234816860643351341)
                ·
                  refine ⟨2866859713056322741256753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7644959234816860643351341 2866859713056322741256753)
                  ·
                    refine ⟨2150144784792242055942565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2866859713056322741256753 2150144784792242055942565)
                    ·
                      refine ⟨403152147148545385489231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2150144784792242055942565 403152147148545385489231)
                      ·
                        rfl

theorem cell23_785136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 4].length) (baseStart_785136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785136 prefixEnd_785136 := by exact prefixLift 785136
  have htrace : WordTrace (prefixWord ++ tailWord_785136) baseStart_785136 baseEnd_785136 := by
    simpa [prefixWord, tailWord_785136, baseEnd_785136] using wordTrace_append hprefix tailTrace_785136
  have hstable : (prefixWord ++ tailWord_785136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785136).length < 2 ^ (prefixWord ++ tailWord_785136).sum := by decide
  have hdescent : baseEnd_785136 < baseStart_785136 := by decide
  rcases family_descends (prefixWord ++ tailWord_785136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785146 : List Nat := [3, 1, 1, 1, 1, 3, 5, 8]
def baseStart_785146 : Nat := 118140960795 + 785146 * 2 ^ 59
def prefixEnd_785146 : Nat := 4983230072969 + 3 ^ 40 * 785146 * 2
def baseEnd_785146 : Nat := 14931751183521864680155

theorem tailTrace_785146 : CollatzResearch.WordTrace tailWord_785146 prefixEnd_785146 14931751183521864680155 := by
  unfold tailWord_785146
  simp only [CollatzResearch.WordTrace]
  refine ⟨7159156803389402276569823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19091084809038406070852861 7159156803389402276569823)
  ·
    refine ⟨10738735205084103414854735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7159156803389402276569823 10738735205084103414854735)
    ·
      refine ⟨16108102807626155122282103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10738735205084103414854735 16108102807626155122282103)
      ·
        refine ⟨24162154211439232683423155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16108102807626155122282103 24162154211439232683423155)
        ·
          refine ⟨36243231317158849025134733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24162154211439232683423155 36243231317158849025134733)
          ·
            refine ⟨13591211743934568384425525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36243231317158849025134733 13591211743934568384425525)
            ·
              refine ⟨1274176100993865786039893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13591211743934568384425525 1274176100993865786039893)
              ·
                refine ⟨14931751183521864680155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1274176100993865786039893 14931751183521864680155)
                ·
                  rfl

theorem cell23_785146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 8].length) (baseStart_785146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785146 prefixEnd_785146 := by exact prefixLift 785146
  have htrace : WordTrace (prefixWord ++ tailWord_785146) baseStart_785146 baseEnd_785146 := by
    simpa [prefixWord, tailWord_785146, baseEnd_785146] using wordTrace_append hprefix tailTrace_785146
  have hstable : (prefixWord ++ tailWord_785146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785146).length < 2 ^ (prefixWord ++ tailWord_785146).sum := by decide
  have hdescent : baseEnd_785146 < baseStart_785146 := by decide
  rcases family_descends (prefixWord ++ tailWord_785146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785150 : List Nat := [4, 2, 2, 1, 2, 2, 2, 1, 1, 6]
def baseStart_785150 : Nat := 118140960795 + 785150 * 2 ^ 59
def prefixEnd_785150 : Nat := 4983230072969 + 3 ^ 40 * 785150 * 2
def baseEnd_785150 : Nat := 134386445292569443571389

theorem tailTrace_785150 : CollatzResearch.WordTrace tailWord_785150 prefixEnd_785150 134386445292569443571389 := by
  unfold tailWord_785150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3579596638192889723678113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19091182070362078526283269 3579596638192889723678113)
  ·
    refine ⟨2684697478644667292758585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3579596638192889723678113 2684697478644667292758585)
    ·
      refine ⟨2013523108983500469568939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2684697478644667292758585 2013523108983500469568939)
      ·
        refine ⟨3020284663475250704353409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2013523108983500469568939 3020284663475250704353409)
        ·
          refine ⟨2265213497606438028265057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3020284663475250704353409 2265213497606438028265057)
          ·
            refine ⟨1698910123204828521198793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2265213497606438028265057 1698910123204828521198793)
            ·
              refine ⟨1274182592403621390899095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1698910123204828521198793 1274182592403621390899095)
              ·
                refine ⟨1911273888605432086348643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1274182592403621390899095 1911273888605432086348643)
                ·
                  refine ⟨2866910832908148129522965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1911273888605432086348643 2866910832908148129522965)
                  ·
                    refine ⟨134386445292569443571389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2866910832908148129522965 134386445292569443571389)
                    ·
                      rfl

theorem cell23_785150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_785150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785150 prefixEnd_785150 := by exact prefixLift 785150
  have htrace : WordTrace (prefixWord ++ tailWord_785150) baseStart_785150 baseEnd_785150 := by
    simpa [prefixWord, tailWord_785150, baseEnd_785150] using wordTrace_append hprefix tailTrace_785150
  have hstable : (prefixWord ++ tailWord_785150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785150).length < 2 ^ (prefixWord ++ tailWord_785150).sum := by decide
  have hdescent : baseEnd_785150 < baseStart_785150 := by decide
  rcases family_descends (prefixWord ++ tailWord_785150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785173 : List Nat := [1, 3, 2, 1, 2, 2, 1, 4, 1, 3, 3]
def baseStart_785173 : Nat := 118140960795 + 785173 * 2 ^ 59
def prefixEnd_785173 : Nat := 4983230072969 + 3 ^ 40 * 785173 * 2
def baseEnd_785173 : Nat := 403171145932761740726561

theorem tailTrace_785173 : CollatzResearch.WordTrace tailWord_785173 prefixEnd_785173 403171145932761740726561 := by
  unfold tailWord_785173
  simp only [CollatzResearch.WordTrace]
  refine ⟨28637611984459792717512173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19091741322973195145008115 28637611984459792717512173)
  ·
    refine ⟨10739104494172422269067065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28637611984459792717512173 10739104494172422269067065)
    ·
      refine ⟨8054328370629316701800299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10739104494172422269067065 8054328370629316701800299)
      ·
        refine ⟨12081492555943975052700449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8054328370629316701800299 12081492555943975052700449)
        ·
          refine ⟨9061119416957981289525337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12081492555943975052700449 9061119416957981289525337)
          ·
            refine ⟨6795839562718485967144003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9061119416957981289525337 6795839562718485967144003)
            ·
              refine ⟨10193759344077728950716005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6795839562718485967144003 10193759344077728950716005)
              ·
                refine ⟨1911329877014574178259251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10193759344077728950716005 1911329877014574178259251)
                ·
                  refine ⟨2866994815521861267388877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1911329877014574178259251 2866994815521861267388877)
                  ·
                    refine ⟨1075123055820697975270829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2866994815521861267388877 1075123055820697975270829)
                    ·
                      refine ⟨403171145932761740726561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1075123055820697975270829 403171145932761740726561)
                      ·
                        rfl

theorem cell23_785173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_785173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785173 prefixEnd_785173 := by exact prefixLift 785173
  have htrace : WordTrace (prefixWord ++ tailWord_785173) baseStart_785173 baseEnd_785173 := by
    simpa [prefixWord, tailWord_785173, baseEnd_785173] using wordTrace_append hprefix tailTrace_785173
  have hstable : (prefixWord ++ tailWord_785173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785173).length < 2 ^ (prefixWord ++ tailWord_785173).sum := by decide
  have hdescent : baseEnd_785173 < baseStart_785173 := by decide
  rcases family_descends (prefixWord ++ tailWord_785173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785204 : List Nat := [2, 5, 1, 1, 4, 1, 1, 1, 1, 2, 4]
def baseStart_785204 : Nat := 118140960795 + 785204 * 2 ^ 59
def prefixEnd_785204 : Nat := 4983230072969 + 3 ^ 40 * 785204 * 2
def baseEnd_785204 : Nat := 403187063833051119438919

theorem tailTrace_785204 : CollatzResearch.WordTrace tailWord_785204 prefixEnd_785204 403187063833051119438919 := by
  unfold tailWord_785204
  simp only [CollatzResearch.WordTrace]
  refine ⟨14319371323673742505945333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19092495098231656674593777 14319371323673742505945333)
  ·
    refine ⟨1342441061594413359932375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14319371323673742505945333 1342441061594413359932375)
    ·
      refine ⟨2013661592391620039898563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1342441061594413359932375 2013661592391620039898563)
      ·
        refine ⟨3020492388587430059847845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2013661592391620039898563 3020492388587430059847845)
        ·
          refine ⟨566342322860143136221471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3020492388587430059847845 566342322860143136221471)
          ·
            refine ⟨849513484290214704332207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566342322860143136221471 849513484290214704332207)
            ·
              refine ⟨1274270226435322056498311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849513484290214704332207 1274270226435322056498311)
              ·
                refine ⟨1911405339652983084747467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1274270226435322056498311 1911405339652983084747467)
                ·
                  refine ⟨2867108009479474627121201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1911405339652983084747467 2867108009479474627121201)
                  ·
                    refine ⟨2150331007109605970340901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2867108009479474627121201 2150331007109605970340901)
                    ·
                      refine ⟨403187063833051119438919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2150331007109605970340901 403187063833051119438919)
                      ·
                        rfl

theorem cell23_785204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_785204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785204 prefixEnd_785204 := by exact prefixLift 785204
  have htrace : WordTrace (prefixWord ++ tailWord_785204) baseStart_785204 baseEnd_785204 := by
    simpa [prefixWord, tailWord_785204, baseEnd_785204] using wordTrace_append hprefix tailTrace_785204
  have hstable : (prefixWord ++ tailWord_785204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785204).length < 2 ^ (prefixWord ++ tailWord_785204).sum := by decide
  have hdescent : baseEnd_785204 < baseStart_785204 := by decide
  rcases family_descends (prefixWord ++ tailWord_785204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785207 : List Nat := [1, 1, 3, 1, 2, 1, 7, 1, 2, 1, 3]
def baseStart_785207 : Nat := 118140960795 + 785207 * 2 ^ 59
def prefixEnd_785207 : Nat := 4983230072969 + 3 ^ 40 * 785207 * 2
def baseEnd_785207 : Nat := 403188604275014607701405

theorem tailTrace_785207 : CollatzResearch.WordTrace tailWord_785207 prefixEnd_785207 403188604275014607701405 := by
  unfold tailWord_785207
  simp only [CollatzResearch.WordTrace]
  refine ⟨28638852066336616524249875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19092568044224411016166583 28638852066336616524249875)
  ·
    refine ⟨42958278099504924786374813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28638852066336616524249875 42958278099504924786374813)
    ·
      refine ⟨16109354287314346794890555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42958278099504924786374813 16109354287314346794890555)
      ·
        refine ⟨24164031430971520192335833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16109354287314346794890555 24164031430971520192335833)
        ·
          refine ⟨18123023573228640144251875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24164031430971520192335833 18123023573228640144251875)
          ·
            refine ⟨27184535359842960216377813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18123023573228640144251875 27184535359842960216377813)
            ·
              refine ⟨637137547496319380071355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 27184535359842960216377813 637137547496319380071355)
              ·
                refine ⟨955706321244479070107033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 637137547496319380071355 955706321244479070107033)
                ·
                  refine ⟨716779740933359302580275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 955706321244479070107033 716779740933359302580275)
                  ·
                    refine ⟨1075169611400038953870413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 716779740933359302580275 1075169611400038953870413)
                    ·
                      refine ⟨403188604275014607701405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1075169611400038953870413 403188604275014607701405)
                      ·
                        rfl

theorem cell23_785207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 2, 1, 3].length) (baseStart_785207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785207 prefixEnd_785207 := by exact prefixLift 785207
  have htrace : WordTrace (prefixWord ++ tailWord_785207) baseStart_785207 baseEnd_785207 := by
    simpa [prefixWord, tailWord_785207, baseEnd_785207] using wordTrace_append hprefix tailTrace_785207
  have hstable : (prefixWord ++ tailWord_785207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785207).length < 2 ^ (prefixWord ++ tailWord_785207).sum := by decide
  have hdescent : baseEnd_785207 < baseStart_785207 := by decide
  rcases family_descends (prefixWord ++ tailWord_785207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785216 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 5]
def baseStart_785216 : Nat := 118140960795 + 785216 * 2 ^ 59
def prefixEnd_785216 : Nat := 4983230072969 + 3 ^ 40 * 785216 * 2
def baseEnd_785216 : Nat := 403193225600905072488863

theorem tailTrace_785216 : CollatzResearch.WordTrace tailWord_785216 prefixEnd_785216 403193225600905072488863 := by
  unfold tailWord_785216
  simp only [CollatzResearch.WordTrace]
  refine ⟨14319590161652005530663751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19092786882202674040885001 14319590161652005530663751)
  ·
    refine ⟨21479385242478008295995627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14319590161652005530663751 21479385242478008295995627)
    ·
      refine ⟨32219077863717012443993441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21479385242478008295995627 32219077863717012443993441)
      ·
        refine ⟨24164308397787759332995081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32219077863717012443993441 24164308397787759332995081)
        ·
          refine ⟨18123231298340819499746311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24164308397787759332995081 18123231298340819499746311)
          ·
            refine ⟨27184846947511229249619467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18123231298340819499746311 27184846947511229249619467)
            ·
              refine ⟨40777270421266843874429201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27184846947511229249619467 40777270421266843874429201)
              ·
                refine ⟨30582952815950132905821901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40777270421266843874429201 30582952815950132905821901)
                ·
                  refine ⟨11468607305981299839683213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30582952815950132905821901 11468607305981299839683213)
                  ·
                    refine ⟨4300727739742987439881205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11468607305981299839683213 4300727739742987439881205)
                    ·
                      refine ⟨403193225600905072488863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4300727739742987439881205 403193225600905072488863)
                      ·
                        rfl

theorem cell23_785216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_785216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785216 prefixEnd_785216 := by exact prefixLift 785216
  have htrace : WordTrace (prefixWord ++ tailWord_785216) baseStart_785216 baseEnd_785216 := by
    simpa [prefixWord, tailWord_785216, baseEnd_785216] using wordTrace_append hprefix tailTrace_785216
  have hstable : (prefixWord ++ tailWord_785216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785216).length < 2 ^ (prefixWord ++ tailWord_785216).sum := by decide
  have hdescent : baseEnd_785216 < baseStart_785216 := by decide
  rcases family_descends (prefixWord ++ tailWord_785216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785230 : List Nat := [4, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2]
def baseStart_785230 : Nat := 118140960795 + 785230 * 2 ^ 59
def prefixEnd_785230 : Nat := 4983230072969 + 3 ^ 40 * 785230 * 2
def baseEnd_785230 : Nat := 403200414330068017713799

theorem tailTrace_785230 : CollatzResearch.WordTrace tailWord_785230 prefixEnd_785230 403200414330068017713799 := by
  unfold tailWord_785230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3579961368156661431542143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19093127296835527634891429 3579961368156661431542143)
  ·
    refine ⟨5369942052234992147313215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3579961368156661431542143 5369942052234992147313215)
    ·
      refine ⟨8054913078352488220969823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5369942052234992147313215 8054913078352488220969823)
      ·
        refine ⟨12082369617528732331454735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8054913078352488220969823 12082369617528732331454735)
        ·
          refine ⟨18123554426293098497182103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12082369617528732331454735 18123554426293098497182103)
          ·
            refine ⟨27185331639439647745773155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18123554426293098497182103 27185331639439647745773155)
            ·
              refine ⟨40777997459159471618659733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27185331639439647745773155 40777997459159471618659733)
              ·
                refine ⟨1911468630898100232124675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40777997459159471618659733 1911468630898100232124675)
                ·
                  refine ⟨2867202946347150348187013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1911468630898100232124675 2867202946347150348187013)
                  ·
                    refine ⟨537600552440090690285065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2867202946347150348187013 537600552440090690285065)
                    ·
                      refine ⟨403200414330068017713799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 537600552440090690285065 403200414330068017713799)
                      ·
                        rfl

theorem cell23_785230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2].length) (baseStart_785230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785230 prefixEnd_785230 := by exact prefixLift 785230
  have htrace : WordTrace (prefixWord ++ tailWord_785230) baseStart_785230 baseEnd_785230 := by
    simpa [prefixWord, tailWord_785230, baseEnd_785230] using wordTrace_append hprefix tailTrace_785230
  have hstable : (prefixWord ++ tailWord_785230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785230).length < 2 ^ (prefixWord ++ tailWord_785230).sum := by decide
  have hdescent : baseEnd_785230 < baseStart_785230 := by decide
  rcases family_descends (prefixWord ++ tailWord_785230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785247 : List Nat := [1, 1, 2, 3, 1, 3, 2, 4, 2, 2, 2]
def baseStart_785247 : Nat := 118140960795 + 785247 * 2 ^ 59
def prefixEnd_785247 : Nat := 4983230072969 + 3 ^ 40 * 785247 * 2
def baseEnd_785247 : Nat := 403209143501194451201221

theorem tailTrace_785247 : CollatzResearch.WordTrace tailWord_785247 prefixEnd_785247 403209143501194451201221 := by
  unfold tailWord_785247
  simp only [CollatzResearch.WordTrace]
  refine ⟨28640310986191703355705995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19093540657461135570470663 28640310986191703355705995)
  ·
    refine ⟨42960466479287555033558993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28640310986191703355705995 42960466479287555033558993)
    ·
      refine ⟨32220349859465666275169245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42960466479287555033558993 32220349859465666275169245)
      ·
        refine ⟨12082631197299624853188467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32220349859465666275169245 12082631197299624853188467)
        ·
          refine ⟨18123946795949437279782701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12082631197299624853188467 18123946795949437279782701)
          ·
            refine ⟨6796480048481038979918513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18123946795949437279782701 6796480048481038979918513)
            ·
              refine ⟨5097360036360779234938885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6796480048481038979918513 5097360036360779234938885)
              ·
                refine ⟨955755006817646106551041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5097360036360779234938885 955755006817646106551041)
                ·
                  refine ⟨716816255113234579913281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 955755006817646106551041 716816255113234579913281)
                  ·
                    refine ⟨537612191334925934934961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 716816255113234579913281 537612191334925934934961)
                    ·
                      refine ⟨403209143501194451201221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 537612191334925934934961 403209143501194451201221)
                      ·
                        rfl

theorem cell23_785247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2, 2, 2].length) (baseStart_785247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785247 prefixEnd_785247 := by exact prefixLift 785247
  have htrace : WordTrace (prefixWord ++ tailWord_785247) baseStart_785247 baseEnd_785247 := by
    simpa [prefixWord, tailWord_785247, baseEnd_785247] using wordTrace_append hprefix tailTrace_785247
  have hstable : (prefixWord ++ tailWord_785247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785247).length < 2 ^ (prefixWord ++ tailWord_785247).sum := by decide
  have hdescent : baseEnd_785247 < baseStart_785247 := by decide
  rcases family_descends (prefixWord ++ tailWord_785247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785253 : List Nat := [1, 3, 1, 3, 1, 1, 5, 1, 7]
def baseStart_785253 : Nat := 118140960795 + 785253 * 2 ^ 59
def prefixEnd_785253 : Nat := 4983230072969 + 3 ^ 40 * 785253 * 2
def baseEnd_785253 : Nat := 44801358265013491969577

theorem tailTrace_785253 : CollatzResearch.WordTrace tailWord_785253 prefixEnd_785253 44801358265013491969577 := by
  unfold tailWord_785253
  simp only [CollatzResearch.WordTrace]
  refine ⟨28640529824169966380424413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19093686549446644253616275 28640529824169966380424413)
  ·
    refine ⟨10740198684063737392659155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28640529824169966380424413 10740198684063737392659155)
    ·
      refine ⟨16110298026095606088988733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10740198684063737392659155 16110298026095606088988733)
      ·
        refine ⟨6041361759785852283370775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16110298026095606088988733 6041361759785852283370775)
        ·
          refine ⟨9062042639678778425056163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6041361759785852283370775 9062042639678778425056163)
          ·
            refine ⟨13593063959518167637584245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9062042639678778425056163 13593063959518167637584245)
            ·
              refine ⟨1274349746204828216023523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13593063959518167637584245 1274349746204828216023523)
              ·
                refine ⟨1911524619307242324035285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1274349746204828216023523 1911524619307242324035285)
                ·
                  refine ⟨44801358265013491969577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1911524619307242324035285 44801358265013491969577)
                  ·
                    rfl

theorem cell23_785253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 7].length) (baseStart_785253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785253 prefixEnd_785253 := by exact prefixLift 785253
  have htrace : WordTrace (prefixWord ++ tailWord_785253) baseStart_785253 baseEnd_785253 := by
    simpa [prefixWord, tailWord_785253, baseEnd_785253] using wordTrace_append hprefix tailTrace_785253
  have hstable : (prefixWord ++ tailWord_785253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785253).length < 2 ^ (prefixWord ++ tailWord_785253).sum := by decide
  have hdescent : baseEnd_785253 < baseStart_785253 := by decide
  rcases family_descends (prefixWord ++ tailWord_785253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785263 : List Nat := [1, 1, 2, 1, 3, 1, 1, 5, 2, 3, 3]
def baseStart_785263 : Nat := 118140960795 + 785263 * 2 ^ 59
def prefixEnd_785263 : Nat := 4983230072969 + 3 ^ 40 * 785263 * 2
def baseEnd_785263 : Nat := 403217359191666388601147

theorem tailTrace_785263 : CollatzResearch.WordTrace tailWord_785263 prefixEnd_785263 403217359191666388601147 := by
  unfold tailWord_785263
  simp only [CollatzResearch.WordTrace]
  refine ⟨28640894554133738088288443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19093929702755825392192295 28640894554133738088288443)
  ·
    refine ⟨42961341831200607132432665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28640894554133738088288443 42961341831200607132432665)
    ·
      refine ⟨32221006373400455349324499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42961341831200607132432665 32221006373400455349324499)
      ·
        refine ⟨48331509560100683023986749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32221006373400455349324499 48331509560100683023986749)
        ·
          refine ⟨18124316085037756133995031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48331509560100683023986749 18124316085037756133995031)
          ·
            refine ⟨27186474127556634200992547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18124316085037756133995031 27186474127556634200992547)
            ·
              refine ⟨40779711191334951301488821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27186474127556634200992547 40779711191334951301488821)
              ·
                refine ⟨3823097924187651684514577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40779711191334951301488821 3823097924187651684514577)
                ·
                  refine ⟨2867323443140738763385933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3823097924187651684514577 2867323443140738763385933)
                  ·
                    refine ⟨1075246291177777036269725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2867323443140738763385933 1075246291177777036269725)
                    ·
                      refine ⟨403217359191666388601147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1075246291177777036269725 403217359191666388601147)
                      ·
                        rfl

theorem cell23_785263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3, 3].length) (baseStart_785263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785263 prefixEnd_785263 := by exact prefixLift 785263
  have htrace : WordTrace (prefixWord ++ tailWord_785263) baseStart_785263 baseEnd_785263 := by
    simpa [prefixWord, tailWord_785263, baseEnd_785263] using wordTrace_append hprefix tailTrace_785263
  have hstable : (prefixWord ++ tailWord_785263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785263).length < 2 ^ (prefixWord ++ tailWord_785263).sum := by decide
  have hdescent : baseEnd_785263 < baseStart_785263 := by decide
  rcases family_descends (prefixWord ++ tailWord_785263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785264 : List Nat := [2, 1, 1, 1, 4, 1, 6, 1, 2, 2, 2]
def baseStart_785264 : Nat := 118140960795 + 785264 * 2 ^ 59
def prefixEnd_785264 : Nat := 4983230072969 + 3 ^ 40 * 785264 * 2
def baseEnd_785264 : Nat := 403217872672320884688643

theorem tailTrace_785264 : CollatzResearch.WordTrace tailWord_785264 prefixEnd_785264 403217872672320884688643 := by
  unfold tailWord_785264
  simp only [CollatzResearch.WordTrace]
  refine ⟨14320465513565057629537423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19093954018086743506049897 14320465513565057629537423)
  ·
    refine ⟨21480698270347586444306135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14320465513565057629537423 21480698270347586444306135)
    ·
      refine ⟨32221047405521379666459203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21480698270347586444306135 32221047405521379666459203)
      ·
        refine ⟨48331571108282069499688805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32221047405521379666459203 48331571108282069499688805)
        ·
          refine ⟨9062169582802888031191651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48331571108282069499688805 9062169582802888031191651)
          ·
            refine ⟨13593254374204332046787477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9062169582802888031191651 13593254374204332046787477)
            ·
              refine ⟨637183798790828064693163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13593254374204332046787477 637183798790828064693163)
              ·
                refine ⟨955775698186242097039745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 637183798790828064693163 955775698186242097039745)
                ·
                  refine ⟨716831773639681572779809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 955775698186242097039745 716831773639681572779809)
                  ·
                    refine ⟨537623830229761179584857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 716831773639681572779809 537623830229761179584857)
                    ·
                      refine ⟨403217872672320884688643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 537623830229761179584857 403217872672320884688643)
                      ·
                        rfl

theorem cell23_785264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 2, 2, 2].length) (baseStart_785264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785264 prefixEnd_785264 := by exact prefixLift 785264
  have htrace : WordTrace (prefixWord ++ tailWord_785264) baseStart_785264 baseEnd_785264 := by
    simpa [prefixWord, tailWord_785264, baseEnd_785264] using wordTrace_append hprefix tailTrace_785264
  have hstable : (prefixWord ++ tailWord_785264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785264).length < 2 ^ (prefixWord ++ tailWord_785264).sum := by decide
  have hdescent : baseEnd_785264 < baseStart_785264 := by decide
  rcases family_descends (prefixWord ++ tailWord_785264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785300 : List Nat := [2, 4, 2, 1, 1, 1, 1, 4, 2, 5]
def baseStart_785300 : Nat := 118140960795 + 785300 * 2 ^ 59
def prefixEnd_785300 : Nat := 4983230072969 + 3 ^ 40 * 785300 * 2
def baseEnd_785300 : Nat := 134412119325294247946159

theorem tailTrace_785300 : CollatzResearch.WordTrace tailWord_785300 prefixEnd_785300 134412119325294247946159 := by
  unfold tailWord_785300
  simp only [CollatzResearch.WordTrace]
  refine ⟨14321122027499846703692677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19094829369999795604923569 14321122027499846703692677)
  ·
    refine ⟨2685210380156221256942377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14321122027499846703692677 2685210380156221256942377)
    ·
      refine ⟨2013907785117165942706783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2685210380156221256942377 2013907785117165942706783)
      ·
        refine ⟨3020861677675748914060175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2013907785117165942706783 3020861677675748914060175)
        ·
          refine ⟨4531292516513623371090263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3020861677675748914060175 4531292516513623371090263)
          ·
            refine ⟨6796938774770435056635395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4531292516513623371090263 6796938774770435056635395)
            ·
              refine ⟨10195408162155652584953093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6796938774770435056635395 10195408162155652584953093)
              ·
                refine ⟨1911639030404184859678705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10195408162155652584953093 1911639030404184859678705)
                ·
                  refine ⟨1433729272803138644759029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1911639030404184859678705 1433729272803138644759029)
                  ·
                    refine ⟨134412119325294247946159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1433729272803138644759029 134412119325294247946159)
                    ·
                      rfl

theorem cell23_785300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_785300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785300 prefixEnd_785300 := by exact prefixLift 785300
  have htrace : WordTrace (prefixWord ++ tailWord_785300) baseStart_785300 baseEnd_785300 := by
    simpa [prefixWord, tailWord_785300, baseEnd_785300] using wordTrace_append hprefix tailTrace_785300
  have hstable : (prefixWord ++ tailWord_785300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785300).length < 2 ^ (prefixWord ++ tailWord_785300).sum := by decide
  have hdescent : baseEnd_785300 < baseStart_785300 := by decide
  rcases family_descends (prefixWord ++ tailWord_785300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785323 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 3, 4, 3]
def baseStart_785323 : Nat := 118140960795 + 785323 * 2 ^ 59
def prefixEnd_785323 : Nat := 4983230072969 + 3 ^ 40 * 785323 * 2
def baseEnd_785323 : Nat := 403248168030936153850871

theorem tailTrace_785323 : CollatzResearch.WordTrace tailWord_785323 prefixEnd_785323 403248168030936153850871 := by
  unfold tailWord_785323
  simp only [CollatzResearch.WordTrace]
  refine ⟨28643082933916368335472623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19095388622610912223648415 28643082933916368335472623)
  ·
    refine ⟨42964624400874552503208935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28643082933916368335472623 42964624400874552503208935)
    ·
      refine ⟨64446936601311828754813403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42964624400874552503208935 64446936601311828754813403)
      ·
        refine ⟨96670404901967743132220105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64446936601311828754813403 96670404901967743132220105)
        ·
          refine ⟨72502803676475807349165079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96670404901967743132220105 72502803676475807349165079)
          ·
            refine ⟨108754205514713711023747619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72502803676475807349165079 108754205514713711023747619)
            ·
              refine ⟨163131308272070566535621429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108754205514713711023747619 163131308272070566535621429)
              ·
                refine ⟨15293560150506615612714509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 163131308272070566535621429 15293560150506615612714509)
                ·
                  refine ⟨5735085056439980854767941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15293560150506615612714509 5735085056439980854767941)
                  ·
                    refine ⟨1075328448082496410268989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5735085056439980854767941 1075328448082496410268989)
                    ·
                      refine ⟨403248168030936153850871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1075328448082496410268989 403248168030936153850871)
                      ·
                        rfl

theorem cell23_785323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4, 3].length) (baseStart_785323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785323 prefixEnd_785323 := by exact prefixLift 785323
  have htrace : WordTrace (prefixWord ++ tailWord_785323) baseStart_785323 baseEnd_785323 := by
    simpa [prefixWord, tailWord_785323, baseEnd_785323] using wordTrace_append hprefix tailTrace_785323
  have hstable : (prefixWord ++ tailWord_785323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785323).length < 2 ^ (prefixWord ++ tailWord_785323).sum := by decide
  have hdescent : baseEnd_785323 < baseStart_785323 := by decide
  rcases family_descends (prefixWord ++ tailWord_785323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785337 : List Nat := [1, 2, 1, 4, 2, 4, 1, 1, 2, 1, 4]
def baseStart_785337 : Nat := 118140960795 + 785337 * 2 ^ 59
def prefixEnd_785337 : Nat := 4983230072969 + 3 ^ 40 * 785337 * 2
def baseEnd_785337 : Nat := 403255356760099099075807

theorem tailTrace_785337 : CollatzResearch.WordTrace tailWord_785337 prefixEnd_785337 403255356760099099075807 := by
  unfold tailWord_785337
  simp only [CollatzResearch.WordTrace]
  refine ⟨28643593555865648726482265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19095729037243765817654843 28643593555865648726482265)
  ·
    refine ⟨21482695166899236544861699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28643593555865648726482265 21482695166899236544861699)
    ·
      refine ⟨32224042750348854817292549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21482695166899236544861699 32224042750348854817292549)
      ·
        refine ⟨6042008015690410278242353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32224042750348854817292549 6042008015690410278242353)
        ·
          refine ⟨4531506011767807708681765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6042008015690410278242353 4531506011767807708681765)
          ·
            refine ⟨849657377206463945377831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4531506011767807708681765 849657377206463945377831)
            ·
              refine ⟨1274486065809695918066747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849657377206463945377831 1274486065809695918066747)
              ·
                refine ⟨1911729098714543877100121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1274486065809695918066747 1911729098714543877100121)
                ·
                  refine ⟨1433796824035907907825091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1911729098714543877100121 1433796824035907907825091)
                  ·
                    refine ⟨2150695236053861861737637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1433796824035907907825091 2150695236053861861737637)
                    ·
                      refine ⟨403255356760099099075807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2150695236053861861737637 403255356760099099075807)
                      ·
                        rfl

theorem cell23_785337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_785337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785337 prefixEnd_785337 := by exact prefixLift 785337
  have htrace : WordTrace (prefixWord ++ tailWord_785337) baseStart_785337 baseEnd_785337 := by
    simpa [prefixWord, tailWord_785337, baseEnd_785337] using wordTrace_append hprefix tailTrace_785337
  have hstable : (prefixWord ++ tailWord_785337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785337).length < 2 ^ (prefixWord ++ tailWord_785337).sum := by decide
  have hdescent : baseEnd_785337 < baseStart_785337 := by decide
  rcases family_descends (prefixWord ++ tailWord_785337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785364 : List Nat := [2, 4, 1, 2, 1, 2, 2, 4, 1, 4]
def baseStart_785364 : Nat := 118140960795 + 785364 * 2 ^ 59
def prefixEnd_785364 : Nat := 4983230072969 + 3 ^ 40 * 785364 * 2
def baseEnd_785364 : Nat := 134423073579256831146061

theorem tailTrace_785364 : CollatzResearch.WordTrace tailWord_785364 prefixEnd_785364 134423073579256831146061 := by
  unfold tailWord_785364
  simp only [CollatzResearch.WordTrace]
  refine ⟨14322289163383916168857573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19096385551178554891810097 14322289163383916168857573)
  ·
    refine ⟨2685429218134484281660795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14322289163383916168857573 2685429218134484281660795)
    ·
      refine ⟨4028143827201726422491193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2685429218134484281660795 4028143827201726422491193)
      ·
        refine ⟨3021107870401294816868395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4028143827201726422491193 3021107870401294816868395)
        ·
          refine ⟨4531661805601942225302593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3021107870401294816868395 4531661805601942225302593)
          ·
            refine ⟨3398746354201456668976945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4531661805601942225302593 3398746354201456668976945)
            ·
              refine ⟨2549059765651092501732709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3398746354201456668976945 2549059765651092501732709)
              ·
                refine ⟨477948706059579844074883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2549059765651092501732709 477948706059579844074883)
                ·
                  refine ⟨716923059089369766112325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 477948706059579844074883 716923059089369766112325)
                  ·
                    refine ⟨134423073579256831146061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 716923059089369766112325 134423073579256831146061)
                    ·
                      rfl

theorem cell23_785364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_785364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785364 prefixEnd_785364 := by exact prefixLift 785364
  have htrace : WordTrace (prefixWord ++ tailWord_785364) baseStart_785364 baseEnd_785364 := by
    simpa [prefixWord, tailWord_785364, baseEnd_785364] using wordTrace_append hprefix tailTrace_785364
  have hstable : (prefixWord ++ tailWord_785364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785364).length < 2 ^ (prefixWord ++ tailWord_785364).sum := by decide
  have hdescent : baseEnd_785364 < baseStart_785364 := by decide
  rcases family_descends (prefixWord ++ tailWord_785364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785403 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 3, 6]
def baseStart_785403 : Nat := 118140960795 + 785403 * 2 ^ 59
def prefixEnd_785403 : Nat := 4983230072969 + 3 ^ 40 * 785403 * 2
def baseEnd_785403 : Nat := 134429748827765280283501

theorem tailTrace_785403 : CollatzResearch.WordTrace tailWord_785403 prefixEnd_785403 134429748827765280283501 := by
  unfold tailWord_785403
  simp only [CollatzResearch.WordTrace]
  refine ⟨28646000773626541998384863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19097333849084361332256575 28646000773626541998384863)
  ·
    refine ⟨42969001160439812997577295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28646000773626541998384863 42969001160439812997577295)
    ·
      refine ⟨64453501740659719496365943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42969001160439812997577295 64453501740659719496365943)
      ·
        refine ⟨96680252610989579244548915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64453501740659719496365943 96680252610989579244548915)
        ·
          refine ⟨145020378916484368866823373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96680252610989579244548915 145020378916484368866823373)
          ·
            refine ⟨54382642093681638325058765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145020378916484368866823373 54382642093681638325058765)
            ·
              refine ⟨20393490785130614371897037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54382642093681638325058765 20393490785130614371897037)
              ·
                refine ⟨7647559044423980389461389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20393490785130614371897037 7647559044423980389461389)
                ·
                  refine ⟨2867834641658992646048021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7647559044423980389461389 2867834641658992646048021)
                  ·
                    refine ⟨134429748827765280283501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2867834641658992646048021 134429748827765280283501)
                    ·
                      rfl

theorem cell23_785403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 6].length) (baseStart_785403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785403 prefixEnd_785403 := by exact prefixLift 785403
  have htrace : WordTrace (prefixWord ++ tailWord_785403) baseStart_785403 baseEnd_785403 := by
    simpa [prefixWord, tailWord_785403, baseEnd_785403] using wordTrace_append hprefix tailTrace_785403
  have hstable : (prefixWord ++ tailWord_785403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785403).length < 2 ^ (prefixWord ++ tailWord_785403).sum := by decide
  have hdescent : baseEnd_785403 < baseStart_785403 := by decide
  rcases family_descends (prefixWord ++ tailWord_785403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785433 : List Nat := [1, 2, 1, 2, 1, 1, 5, 10]
def baseStart_785433 : Nat := 118140960795 + 785433 * 2 ^ 59
def prefixEnd_785433 : Nat := 4983230072969 + 3 ^ 40 * 785433 * 2
def baseEnd_785433 : Nat := 14937209292701137906495

theorem tailTrace_785433 : CollatzResearch.WordTrace tailWord_785433 prefixEnd_785433 14937209292701137906495 := by
  unfold tailWord_785433
  simp only [CollatzResearch.WordTrace]
  refine ⟨28647094963517857121976953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19098063309011904747984635 28647094963517857121976953)
  ·
    refine ⟨21485321222638392841482715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28647094963517857121976953 21485321222638392841482715)
    ·
      refine ⟨32227981833957589262224073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21485321222638392841482715 32227981833957589262224073)
      ·
        refine ⟨24170986375468191946668055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32227981833957589262224073 24170986375468191946668055)
        ·
          refine ⟨36256479563202287920002083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24170986375468191946668055 36256479563202287920002083)
          ·
            refine ⟨54384719344803431880003125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36256479563202287920002083 54384719344803431880003125)
            ·
              refine ⟨5098567438575321738750293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54384719344803431880003125 5098567438575321738750293)
              ·
                refine ⟨14937209292701137906495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5098567438575321738750293 14937209292701137906495)
                ·
                  rfl

theorem cell23_785433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 10].length) (baseStart_785433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785433 prefixEnd_785433 := by exact prefixLift 785433
  have htrace : WordTrace (prefixWord ++ tailWord_785433) baseStart_785433 baseEnd_785433 := by
    simpa [prefixWord, tailWord_785433, baseEnd_785433] using wordTrace_append hprefix tailTrace_785433
  have hstable : (prefixWord ++ tailWord_785433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785433).length < 2 ^ (prefixWord ++ tailWord_785433).sum := by decide
  have hdescent : baseEnd_785433 < baseStart_785433 := by decide
  rcases family_descends (prefixWord ++ tailWord_785433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785444 : List Nat := [2, 3, 1, 4, 1, 1, 3, 2, 1, 1, 4]
def baseStart_785444 : Nat := 118140960795 + 785444 * 2 ^ 59
def prefixEnd_785444 : Nat := 4983230072969 + 3 ^ 40 * 785444 * 2
def baseEnd_785444 : Nat := 403310299190130180437815

theorem tailTrace_785444 : CollatzResearch.WordTrace tailWord_785444 prefixEnd_785444 403310299190130180437815 := by
  unfold tailWord_785444
  simp only [CollatzResearch.WordTrace]
  refine ⟨14323748083239003000313693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19098330777652004000418257 14323748083239003000313693)
  ·
    refine ⟨5371405531214626125117635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14323748083239003000313693 5371405531214626125117635)
    ·
      refine ⟨8057108296821939187676453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5371405531214626125117635 8057108296821939187676453)
      ·
        refine ⟨1510707805654113597689335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8057108296821939187676453 1510707805654113597689335)
        ·
          refine ⟨2266061708481170396534003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1510707805654113597689335 2266061708481170396534003)
          ·
            refine ⟨3399092562721755594801005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2266061708481170396534003 3399092562721755594801005)
            ·
              refine ⟨1274659711020658348050377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3399092562721755594801005 1274659711020658348050377)
              ·
                refine ⟨955994783265493761037783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1274659711020658348050377 955994783265493761037783)
                ·
                  refine ⟨1433992174898240641556675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 955994783265493761037783 1433992174898240641556675)
                  ·
                    refine ⟨2150988262347360962335013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1433992174898240641556675 2150988262347360962335013)
                    ·
                      refine ⟨403310299190130180437815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2150988262347360962335013 403310299190130180437815)
                      ·
                        rfl

theorem cell23_785444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_785444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785444 prefixEnd_785444 := by exact prefixLift 785444
  have htrace : WordTrace (prefixWord ++ tailWord_785444) baseStart_785444 baseEnd_785444 := by
    simpa [prefixWord, tailWord_785444, baseEnd_785444] using wordTrace_append hprefix tailTrace_785444
  have hstable : (prefixWord ++ tailWord_785444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785444).length < 2 ^ (prefixWord ++ tailWord_785444).sum := by decide
  have hdescent : baseEnd_785444 < baseStart_785444 := by decide
  rcases family_descends (prefixWord ++ tailWord_785444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785461 : List Nat := [1, 3, 3, 1, 1, 1, 1, 7, 1, 2, 2]
def baseStart_785461 : Nat := 118140960795 + 785461 * 2 ^ 59
def prefixEnd_785461 : Nat := 4983230072969 + 3 ^ 40 * 785461 * 2
def baseEnd_785461 : Nat := 403319028361256613925237

theorem tailTrace_785461 : CollatzResearch.WordTrace tailWord_785461 prefixEnd_785461 403319028361256613925237 := by
  unfold tailWord_785461
  simp only [CollatzResearch.WordTrace]
  refine ⟨28648116207416417903996237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19098744138277611935997491 28648116207416417903996237)
  ·
    refine ⟨10743043577781156713998589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28648116207416417903996237 10743043577781156713998589)
    ·
      refine ⟨4028641341667933767749471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10743043577781156713998589 4028641341667933767749471)
      ·
        refine ⟨6042962012501900651624207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4028641341667933767749471 6042962012501900651624207)
        ·
          refine ⟨9064443018752850977436311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6042962012501900651624207 9064443018752850977436311)
          ·
            refine ⟨13596664528129276466154467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9064443018752850977436311 13596664528129276466154467)
            ·
              refine ⟨20394996792193914699231701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13596664528129276466154467 20394996792193914699231701)
              ·
                refine ⟨478007737317044875763243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20394996792193914699231701 478007737317044875763243)
                ·
                  refine ⟨717011605975567313644865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 478007737317044875763243 717011605975567313644865)
                  ·
                    refine ⟨537758704481675485233649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 717011605975567313644865 537758704481675485233649)
                    ·
                      refine ⟨403319028361256613925237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 537758704481675485233649 403319028361256613925237)
                      ·
                        rfl

theorem cell23_785461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_785461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785461 prefixEnd_785461 := by exact prefixLift 785461
  have htrace : WordTrace (prefixWord ++ tailWord_785461) baseStart_785461 baseEnd_785461 := by
    simpa [prefixWord, tailWord_785461, baseEnd_785461] using wordTrace_append hprefix tailTrace_785461
  have hstable : (prefixWord ++ tailWord_785461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785461).length < 2 ^ (prefixWord ++ tailWord_785461).sum := by decide
  have hdescent : baseEnd_785461 < baseStart_785461 := by decide
  rcases family_descends (prefixWord ++ tailWord_785461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785477 : List Nat := [1, 3, 1, 1, 1, 3, 2, 3, 4, 1, 3]
def baseStart_785477 : Nat := 118140960795 + 785477 * 2 ^ 59
def prefixEnd_785477 : Nat := 4983230072969 + 3 ^ 40 * 785477 * 2
def baseEnd_785477 : Nat := 403327244051728551325163

theorem tailTrace_785477 : CollatzResearch.WordTrace tailWord_785477 prefixEnd_785477 403327244051728551325163 := by
  unfold tailWord_785477
  simp only [CollatzResearch.WordTrace]
  refine ⟨28648699775358452636578685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19099133183572301757719123 28648699775358452636578685)
  ·
    refine ⟨10743262415759419738717007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28648699775358452636578685 10743262415759419738717007)
    ·
      refine ⟨16114893623639129608075511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10743262415759419738717007 16114893623639129608075511)
      ·
        refine ⟨24172340435458694412113267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16114893623639129608075511 24172340435458694412113267)
        ·
          refine ⟨36258510653188041618169901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24172340435458694412113267 36258510653188041618169901)
          ·
            refine ⟨13596941494945515606813713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36258510653188041618169901 13596941494945515606813713)
            ·
              refine ⟨10197706121209136705110285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13596941494945515606813713 10197706121209136705110285)
              ·
                refine ⟨3824139795453426264416357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10197706121209136705110285 3824139795453426264416357)
                ·
                  refine ⟨717026211647517424578067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3824139795453426264416357 717026211647517424578067)
                  ·
                    refine ⟨1075539317471276136867101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 717026211647517424578067 1075539317471276136867101)
                    ·
                      refine ⟨403327244051728551325163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1075539317471276136867101 403327244051728551325163)
                      ·
                        rfl

theorem cell23_785477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4, 1, 3].length) (baseStart_785477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785477 prefixEnd_785477 := by exact prefixLift 785477
  have htrace : WordTrace (prefixWord ++ tailWord_785477) baseStart_785477 baseEnd_785477 := by
    simpa [prefixWord, tailWord_785477, baseEnd_785477] using wordTrace_append hprefix tailTrace_785477
  have hstable : (prefixWord ++ tailWord_785477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785477).length < 2 ^ (prefixWord ++ tailWord_785477).sum := by decide
  have hdescent : baseEnd_785477 < baseStart_785477 := by decide
  rcases family_descends (prefixWord ++ tailWord_785477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785504 : List Nat := [2, 1, 1, 3, 2, 2, 2, 4, 1, 3, 2]
def baseStart_785504 : Nat := 118140960795 + 785504 * 2 ^ 59
def prefixEnd_785504 : Nat := 4983230072969 + 3 ^ 40 * 785504 * 2
def baseEnd_785504 : Nat := 403341108029399945687539

theorem tailTrace_785504 : CollatzResearch.WordTrace tailWord_785504 prefixEnd_785504 403341108029399945687539 := by
  unfold tailWord_785504
  simp only [CollatzResearch.WordTrace]
  refine ⟨14324842273130318123905783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19099789697507090831874377 14324842273130318123905783)
  ·
    refine ⟨21487263409695477185858675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14324842273130318123905783 21487263409695477185858675)
    ·
      refine ⟨32230895114543215778788013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21487263409695477185858675 32230895114543215778788013)
      ·
        refine ⟨12086585667953705917045505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32230895114543215778788013 12086585667953705917045505)
        ·
          refine ⟨9064939250965279437784129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12086585667953705917045505 9064939250965279437784129)
          ·
            refine ⟨6798704438223959578338097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9064939250965279437784129 6798704438223959578338097)
            ·
              refine ⟨5099028328667969683753573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6798704438223959578338097 5099028328667969683753573)
              ·
                refine ⟨956067811625244315703795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5099028328667969683753573 956067811625244315703795)
                ·
                  refine ⟨1434101717437866473555693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 956067811625244315703795 1434101717437866473555693)
                  ·
                    refine ⟨537788144039199927583385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1434101717437866473555693 537788144039199927583385)
                    ·
                      refine ⟨403341108029399945687539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 537788144039199927583385 403341108029399945687539)
                      ·
                        rfl

theorem cell23_785504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 1, 3, 2].length) (baseStart_785504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785504 prefixEnd_785504 := by exact prefixLift 785504
  have htrace : WordTrace (prefixWord ++ tailWord_785504) baseStart_785504 baseEnd_785504 := by
    simpa [prefixWord, tailWord_785504, baseEnd_785504] using wordTrace_append hprefix tailTrace_785504
  have hstable : (prefixWord ++ tailWord_785504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785504).length < 2 ^ (prefixWord ++ tailWord_785504).sum := by decide
  have hdescent : baseEnd_785504 < baseStart_785504 := by decide
  rcases family_descends (prefixWord ++ tailWord_785504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785520 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 5]
def baseStart_785520 : Nat := 118140960795 + 785520 * 2 ^ 59
def prefixEnd_785520 : Nat := 4983230072969 + 3 ^ 40 * 785520 * 2
def baseEnd_785520 : Nat := 403349323719871883087465

theorem tailTrace_785520 : CollatzResearch.WordTrace tailWord_785520 prefixEnd_785520 403349323719871883087465 := by
  unfold tailWord_785520
  simp only [CollatzResearch.WordTrace]
  refine ⟨14325134057101335490197007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19100178742801780653596009 14325134057101335490197007)
  ·
    refine ⟨21487701085652003235295511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14325134057101335490197007 21487701085652003235295511)
    ·
      refine ⟨32231551628478004852943267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21487701085652003235295511 32231551628478004852943267)
      ·
        refine ⟨48347327442717007279414901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32231551628478004852943267 48347327442717007279414901)
        ·
          refine ⟨4532561947754719432445147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48347327442717007279414901 4532561947754719432445147)
          ·
            refine ⟨6798842921632079148667721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4532561947754719432445147 6798842921632079148667721)
            ·
              refine ⟨5099132191224059361500791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6798842921632079148667721 5099132191224059361500791)
              ·
                refine ⟨7648698286836089042251187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5099132191224059361500791 7648698286836089042251187)
                ·
                  refine ⟨11473047430254133563376781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7648698286836089042251187 11473047430254133563376781)
                  ·
                    refine ⟨4302392786345300086266293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11473047430254133563376781 4302392786345300086266293)
                    ·
                      refine ⟨403349323719871883087465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4302392786345300086266293 403349323719871883087465)
                      ·
                        rfl

theorem cell23_785520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 5].length) (baseStart_785520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785520 prefixEnd_785520 := by exact prefixLift 785520
  have htrace : WordTrace (prefixWord ++ tailWord_785520) baseStart_785520 baseEnd_785520 := by
    simpa [prefixWord, tailWord_785520, baseEnd_785520] using wordTrace_append hprefix tailTrace_785520
  have hstable : (prefixWord ++ tailWord_785520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785520).length < 2 ^ (prefixWord ++ tailWord_785520).sum := by decide
  have hdescent : baseEnd_785520 < baseStart_785520 := by decide
  rcases family_descends (prefixWord ++ tailWord_785520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785577 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 6, 5, 2]
def baseStart_785577 : Nat := 118140960795 + 785577 * 2 ^ 59
def prefixEnd_785577 : Nat := 4983230072969 + 3 ^ 40 * 785577 * 2
def baseEnd_785577 : Nat := 403378592117178160074703

theorem tailTrace_785577 : CollatzResearch.WordTrace tailWord_785577 prefixEnd_785577 403378592117178160074703 := by
  unfold tailWord_785577
  simp only [CollatzResearch.WordTrace]
  refine ⟨28652347074996169715218985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19101564716664113143479323 28652347074996169715218985)
  ·
    refine ⟨21489260306247127286414239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28652347074996169715218985 21489260306247127286414239)
    ·
      refine ⟨32233890459370690929621359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21489260306247127286414239 32233890459370690929621359)
      ·
        refine ⟨48350835689056036394432039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32233890459370690929621359 48350835689056036394432039)
        ·
          refine ⟨72526253533584054591648059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48350835689056036394432039 72526253533584054591648059)
          ·
            refine ⟨108789380300376081887472089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72526253533584054591648059 108789380300376081887472089)
            ·
              refine ⟨81592035225282061415604067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108789380300376081887472089 81592035225282061415604067)
              ·
                refine ⟨122388052837923092123406101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81592035225282061415604067 122388052837923092123406101)
                ·
                  refine ⟨5736939976777644943284661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 122388052837923092123406101 5736939976777644943284661)
                  ·
                    refine ⟨537838122822904213432937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5736939976777644943284661 537838122822904213432937)
                    ·
                      refine ⟨403378592117178160074703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 537838122822904213432937 403378592117178160074703)
                      ·
                        rfl

theorem cell23_785577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 5, 2].length) (baseStart_785577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785577 prefixEnd_785577 := by exact prefixLift 785577
  have htrace : WordTrace (prefixWord ++ tailWord_785577) baseStart_785577 baseEnd_785577 := by
    simpa [prefixWord, tailWord_785577, baseEnd_785577] using wordTrace_append hprefix tailTrace_785577
  have hstable : (prefixWord ++ tailWord_785577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785577).length < 2 ^ (prefixWord ++ tailWord_785577).sum := by decide
  have hdescent : baseEnd_785577 < baseStart_785577 := by decide
  rcases family_descends (prefixWord ++ tailWord_785577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785602 : List Nat := [3, 5, 1, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_785602 : Nat := 118140960795 + 785602 * 2 ^ 59
def prefixEnd_785602 : Nat := 4983230072969 + 3 ^ 40 * 785602 * 2
def baseEnd_785602 : Nat := 403391429133540562262089

theorem tailTrace_785602 : CollatzResearch.WordTrace tailWord_785602 prefixEnd_785602 403391429133540562262089 := by
  unfold tailWord_785602
  simp only [CollatzResearch.WordTrace]
  refine ⟨7163314724976399746219765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19102172599937065989919373 7163314724976399746219765)
  ·
    refine ⟨671560755466537476208103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7163314724976399746219765 671560755466537476208103)
    ·
      refine ⟨1007341133199806214312155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 671560755466537476208103 1007341133199806214312155)
      ·
        refine ⟨1511011699799709321468233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1007341133199806214312155 1511011699799709321468233)
        ·
          refine ⟨1133258774849781991101175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1511011699799709321468233 1133258774849781991101175)
          ·
            refine ⟨1699888162274672986651763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1133258774849781991101175 1699888162274672986651763)
            ·
              refine ⟨2549832243412009479977645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1699888162274672986651763 2549832243412009479977645)
              ·
                refine ⟨956187091279503554991617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2549832243412009479977645 956187091279503554991617)
                ·
                  refine ⟨717140318459627666243713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 956187091279503554991617 717140318459627666243713)
                  ·
                    refine ⟨537855238844720749682785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 717140318459627666243713 537855238844720749682785)
                    ·
                      refine ⟨403391429133540562262089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 537855238844720749682785 403391429133540562262089)
                      ·
                        rfl

theorem cell23_785602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_785602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785602 prefixEnd_785602 := by exact prefixLift 785602
  have htrace : WordTrace (prefixWord ++ tailWord_785602) baseStart_785602 baseEnd_785602 := by
    simpa [prefixWord, tailWord_785602, baseEnd_785602] using wordTrace_append hprefix tailTrace_785602
  have hstable : (prefixWord ++ tailWord_785602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785602).length < 2 ^ (prefixWord ++ tailWord_785602).sum := by decide
  have hdescent : baseEnd_785602 < baseStart_785602 := by decide
  rcases family_descends (prefixWord ++ tailWord_785602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785617 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 5, 4]
def baseStart_785617 : Nat := 118140960795 + 785617 * 2 ^ 59
def prefixEnd_785617 : Nat := 4983230072969 + 3 ^ 40 * 785617 * 2
def baseEnd_785617 : Nat := 134466377114452667858173

theorem tailTrace_785617 : CollatzResearch.WordTrace tailWord_785617 prefixEnd_785617 134466377114452667858173 := by
  unfold tailWord_785617
  simp only [CollatzResearch.WordTrace]
  refine ⟨28653805994851256546675105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19102537329900837697783403 28653805994851256546675105)
  ·
    refine ⟨21490354496138442410006329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28653805994851256546675105 21490354496138442410006329)
    ·
      refine ⟨16117765872103831807504747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21490354496138442410006329 16117765872103831807504747)
      ·
        refine ⟨24176648808155747711257121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16117765872103831807504747 24176648808155747711257121)
        ·
          refine ⟨18132486606116810783442841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24176648808155747711257121 18132486606116810783442841)
          ·
            refine ⟨13599364954587608087582131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18132486606116810783442841 13599364954587608087582131)
            ·
              refine ⟨20399047431881412131373197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13599364954587608087582131 20399047431881412131373197)
              ·
                refine ⟨7649642786955529549264949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20399047431881412131373197 7649642786955529549264949)
                ·
                  refine ⟨717154011277080895243589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7649642786955529549264949 717154011277080895243589)
                  ·
                    refine ⟨134466377114452667858173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 717154011277080895243589 134466377114452667858173)
                    ·
                      rfl

theorem cell23_785617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5, 4].length) (baseStart_785617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785617 prefixEnd_785617 := by exact prefixLift 785617
  have htrace : WordTrace (prefixWord ++ tailWord_785617) baseStart_785617 baseEnd_785617 := by
    simpa [prefixWord, tailWord_785617, baseEnd_785617] using wordTrace_append hprefix tailTrace_785617
  have hstable : (prefixWord ++ tailWord_785617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785617).length < 2 ^ (prefixWord ++ tailWord_785617).sum := by decide
  have hdescent : baseEnd_785617 < baseStart_785617 := by decide
  rcases family_descends (prefixWord ++ tailWord_785617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785644 : List Nat := [2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 3]
def baseStart_785644 : Nat := 118140960795 + 785644 * 2 ^ 59
def prefixEnd_785644 : Nat := 4983230072969 + 3 ^ 40 * 785644 * 2
def baseEnd_785644 : Nat := 403412995321029397936895

theorem tailTrace_785644 : CollatzResearch.WordTrace tailWord_785644 prefixEnd_785644 403412995321029397936895 := by
  unfold tailWord_785644
  simp only [CollatzResearch.WordTrace]
  refine ⟨14327395382876720078953993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19103193843835626771938657 14327395382876720078953993)
  ·
    refine ⟨10745546537157540059215495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14327395382876720078953993 10745546537157540059215495)
    ·
      refine ⟨16118319805736310088823243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10745546537157540059215495 16118319805736310088823243)
      ·
        refine ⟨24177479708604465133234865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16118319805736310088823243 24177479708604465133234865)
        ·
          refine ⟨18133109781453348849926149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24177479708604465133234865 18133109781453348849926149)
          ·
            refine ⟨3399958084022502909361153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18133109781453348849926149 3399958084022502909361153)
            ·
              refine ⟨2549968563016877182020865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3399958084022502909361153 2549968563016877182020865)
              ·
                refine ⟨1912476422262657886515649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2549968563016877182020865 1912476422262657886515649)
                ·
                  refine ⟨1434357316696993414886737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1912476422262657886515649 1434357316696993414886737)
                  ·
                    refine ⟨1075767987522745061165053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1434357316696993414886737 1075767987522745061165053)
                    ·
                      refine ⟨403412995321029397936895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1075767987522745061165053 403412995321029397936895)
                      ·
                        rfl

theorem cell23_785644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 3].length) (baseStart_785644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785644 prefixEnd_785644 := by exact prefixLift 785644
  have htrace : WordTrace (prefixWord ++ tailWord_785644) baseStart_785644 baseEnd_785644 := by
    simpa [prefixWord, tailWord_785644, baseEnd_785644] using wordTrace_append hprefix tailTrace_785644
  have hstable : (prefixWord ++ tailWord_785644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785644).length < 2 ^ (prefixWord ++ tailWord_785644).sum := by decide
  have hdescent : baseEnd_785644 < baseStart_785644 := by decide
  rcases family_descends (prefixWord ++ tailWord_785644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785651 : List Nat := [1, 1, 1, 2, 2, 6, 1, 4, 1, 4]
def baseStart_785651 : Nat := 118140960795 + 785651 * 2 ^ 59
def prefixEnd_785651 : Nat := 4983230072969 + 3 ^ 40 * 785651 * 2
def baseEnd_785651 : Nat := 134472196561870290183121

theorem tailTrace_785651 : CollatzResearch.WordTrace tailWord_785651 prefixEnd_785651 134472196561870290183121 := by
  unfold tailWord_785651
  simp only [CollatzResearch.WordTrace]
  refine ⟨28655046076728080353412807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19103364051152053568941871 28655046076728080353412807)
  ·
    refine ⟨42982569115092120530119211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28655046076728080353412807 42982569115092120530119211)
    ·
      refine ⟨64473853672638180795178817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42982569115092120530119211 64473853672638180795178817)
      ·
        refine ⟨48355390254478635596384113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64473853672638180795178817 48355390254478635596384113)
        ·
          refine ⟨36266542690858976697288085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48355390254478635596384113 36266542690858976697288085)
          ·
            refine ⟨1699994188634014532685379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 36266542690858976697288085 1699994188634014532685379)
            ·
              refine ⟨2549991282951021799028069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1699994188634014532685379 2549991282951021799028069)
              ·
                refine ⟨478123365553316587317763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2549991282951021799028069 478123365553316587317763)
                ·
                  refine ⟨717185048329974880976645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 478123365553316587317763 717185048329974880976645)
                  ·
                    refine ⟨134472196561870290183121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 717185048329974880976645 134472196561870290183121)
                    ·
                      rfl

theorem cell23_785651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4, 1, 4].length) (baseStart_785651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785651 prefixEnd_785651 := by exact prefixLift 785651
  have htrace : WordTrace (prefixWord ++ tailWord_785651) baseStart_785651 baseEnd_785651 := by
    simpa [prefixWord, tailWord_785651, baseEnd_785651] using wordTrace_append hprefix tailTrace_785651
  have hstable : (prefixWord ++ tailWord_785651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785651).length < 2 ^ (prefixWord ++ tailWord_785651).sum := by decide
  have hdescent : baseEnd_785651 < baseStart_785651 := by decide
  rcases family_descends (prefixWord ++ tailWord_785651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785698 : List Nat := [3, 3, 1, 1, 5, 1, 1, 2, 6]
def baseStart_785698 : Nat := 118140960795 + 785698 * 2 ^ 59
def prefixEnd_785698 : Nat := 4983230072969 + 3 ^ 40 * 785698 * 2
def baseEnd_785698 : Nat := 44826747030708020740183

theorem tailTrace_785698 : CollatzResearch.WordTrace tailWord_785698 prefixEnd_785698 44826747030708020740183 := by
  unfold tailWord_785698
  simp only [CollatzResearch.WordTrace]
  refine ⟨7164190076889451845093437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19104506871705204920249165 7164190076889451845093437)
  ·
    refine ⟨2686571278833544441910039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7164190076889451845093437 2686571278833544441910039)
    ·
      refine ⟨4029856918250316662865059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2686571278833544441910039 4029856918250316662865059)
      ·
        refine ⟨6044785377375474994297589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4029856918250316662865059 6044785377375474994297589)
        ·
          refine ⟨566698629128950780715399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6044785377375474994297589 566698629128950780715399)
          ·
            refine ⟨850047943693426171073099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566698629128950780715399 850047943693426171073099)
            ·
              refine ⟨1275071915540139256609649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 850047943693426171073099 1275071915540139256609649)
              ·
                refine ⟨956303936655104442457237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1275071915540139256609649 956303936655104442457237)
                ·
                  refine ⟨44826747030708020740183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 956303936655104442457237 44826747030708020740183)
                  ·
                    rfl

theorem cell23_785698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_785698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785698 prefixEnd_785698 := by exact prefixLift 785698
  have htrace : WordTrace (prefixWord ++ tailWord_785698) baseStart_785698 baseEnd_785698 := by
    simpa [prefixWord, tailWord_785698, baseEnd_785698] using wordTrace_append hprefix tailTrace_785698
  have hstable : (prefixWord ++ tailWord_785698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785698).length < 2 ^ (prefixWord ++ tailWord_785698).sum := by decide
  have hdescent : baseEnd_785698 < baseStart_785698 := by decide
  rcases family_descends (prefixWord ++ tailWord_785698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785724 : List Nat := [2, 2, 2, 2, 1, 3, 3, 1, 1, 6]
def baseStart_785724 : Nat := 118140960795 + 785724 * 2 ^ 59
def prefixEnd_785724 : Nat := 4983230072969 + 3 ^ 40 * 785724 * 2
def baseEnd_785724 : Nat := 134484691257796361645509

theorem tailTrace_785724 : CollatzResearch.WordTrace tailWord_785724 prefixEnd_785724 134484691257796361645509 := by
  unfold tailWord_785724
  simp only [CollatzResearch.WordTrace]
  refine ⟨14328854302731806910410113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19105139070309075880546817 14328854302731806910410113)
  ·
    refine ⟨10746640727048855182807585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14328854302731806910410113 10746640727048855182807585)
    ·
      refine ⟨8059980545286641387105689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10746640727048855182807585 8059980545286641387105689)
      ·
        refine ⟨6044985408964981040329267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8059980545286641387105689 6044985408964981040329267)
        ·
          refine ⟨9067478113447471560493901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6044985408964981040329267 9067478113447471560493901)
          ·
            refine ⟨3400304292542801835185213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9067478113447471560493901 3400304292542801835185213)
            ·
              refine ⟨1275114109703550688194455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3400304292542801835185213 1275114109703550688194455)
              ·
                refine ⟨1912671164555326032291683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1275114109703550688194455 1912671164555326032291683)
                ·
                  refine ⟨2869006746832989048437525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1912671164555326032291683 2869006746832989048437525)
                  ·
                    refine ⟨134484691257796361645509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2869006746832989048437525 134484691257796361645509)
                    ·
                      rfl

theorem cell23_785724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_785724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785724 prefixEnd_785724 := by exact prefixLift 785724
  have htrace : WordTrace (prefixWord ++ tailWord_785724) baseStart_785724 baseEnd_785724 := by
    simpa [prefixWord, tailWord_785724, baseEnd_785724] using wordTrace_append hprefix tailTrace_785724
  have hstable : (prefixWord ++ tailWord_785724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785724).length < 2 ^ (prefixWord ++ tailWord_785724).sum := by decide
  have hdescent : baseEnd_785724 < baseStart_785724 := by decide
  rcases family_descends (prefixWord ++ tailWord_785724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785751 : List Nat := [1, 1, 3, 2, 3, 2, 2, 3, 1, 2, 3]
def baseStart_785751 : Nat := 118140960795 + 785751 * 2 ^ 59
def prefixEnd_785751 : Nat := 4983230072969 + 3 ^ 40 * 785751 * 2
def baseEnd_785751 : Nat := 403467937751060479298903

theorem tailTrace_785751 : CollatzResearch.WordTrace tailWord_785751 prefixEnd_785751 403467937751060479298903 := by
  unfold tailWord_785751
  simp only [CollatzResearch.WordTrace]
  refine ⟨28658693376365797432053107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19105795584243864954702071 28658693376365797432053107)
  ·
    refine ⟨42988040064548696148079661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28658693376365797432053107 42988040064548696148079661)
    ·
      refine ⟨16120515024205761055529873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42988040064548696148079661 16120515024205761055529873)
      ·
        refine ⟨12090386268154320791647405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16120515024205761055529873 12090386268154320791647405)
        ·
          refine ⟨4533894850557870296867777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12090386268154320791647405 4533894850557870296867777)
          ·
            refine ⟨3400421137918402722650833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4533894850557870296867777 3400421137918402722650833)
            ·
              refine ⟨2550315853438802041988125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3400421137918402722650833 2550315853438802041988125)
              ·
                refine ⟨956368445039550765745547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2550315853438802041988125 956368445039550765745547)
                ·
                  refine ⟨1434552667559326148618321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 956368445039550765745547 1434552667559326148618321)
                  ·
                    refine ⟨1075914500669494611463741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1434552667559326148618321 1075914500669494611463741)
                    ·
                      refine ⟨403467937751060479298903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1075914500669494611463741 403467937751060479298903)
                      ·
                        rfl

theorem cell23_785751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_785751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785751 prefixEnd_785751 := by exact prefixLift 785751
  have htrace : WordTrace (prefixWord ++ tailWord_785751) baseStart_785751 baseEnd_785751 := by
    simpa [prefixWord, tailWord_785751, baseEnd_785751] using wordTrace_append hprefix tailTrace_785751
  have hstable : (prefixWord ++ tailWord_785751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785751).length < 2 ^ (prefixWord ++ tailWord_785751).sum := by decide
  have hdescent : baseEnd_785751 < baseStart_785751 := by decide
  rcases family_descends (prefixWord ++ tailWord_785751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785816 : List Nat := [2, 1, 2, 5, 3, 1, 2, 2, 1, 2, 2]
def baseStart_785816 : Nat := 118140960795 + 785816 * 2 ^ 59
def prefixEnd_785816 : Nat := 4983230072969 + 3 ^ 40 * 785816 * 2
def baseEnd_785816 : Nat := 403501313993602724986105

theorem tailTrace_785816 : CollatzResearch.WordTrace tailWord_785816 prefixEnd_785816 403501313993602724986105 := by
  unfold tailWord_785816
  simp only [CollatzResearch.WordTrace]
  refine ⟨14330532060565156766584651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19107376080753542355446201 14330532060565156766584651)
  ·
    refine ⟨21495798090847735149876977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14330532060565156766584651 21495798090847735149876977)
    ·
      refine ⟨16121848568135801362407733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21495798090847735149876977 16121848568135801362407733)
      ·
        refine ⟨1511423303262731377725725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16121848568135801362407733 1511423303262731377725725)
        ·
          refine ⟨566783738723524266647147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1511423303262731377725725 566783738723524266647147)
          ·
            refine ⟨850175608085286399970721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566783738723524266647147 850175608085286399970721)
            ·
              refine ⟨637631706063964799978041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 850175608085286399970721 637631706063964799978041)
              ·
                refine ⟨478223779547973599983531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 637631706063964799978041 478223779547973599983531)
                ·
                  refine ⟨717335669321960399975297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 478223779547973599983531 717335669321960399975297)
                  ·
                    refine ⟨538001751991470299981473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 717335669321960399975297 538001751991470299981473)
                    ·
                      refine ⟨403501313993602724986105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 538001751991470299981473 403501313993602724986105)
                      ·
                        rfl

theorem cell23_785816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_785816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785816 prefixEnd_785816 := by exact prefixLift 785816
  have htrace : WordTrace (prefixWord ++ tailWord_785816) baseStart_785816 baseEnd_785816 := by
    simpa [prefixWord, tailWord_785816, baseEnd_785816] using wordTrace_append hprefix tailTrace_785816
  have hstable : (prefixWord ++ tailWord_785816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785816).length < 2 ^ (prefixWord ++ tailWord_785816).sum := by decide
  have hdescent : baseEnd_785816 < baseStart_785816 := by decide
  rcases family_descends (prefixWord ++ tailWord_785816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785824 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 3]
def baseStart_785824 : Nat := 118140960795 + 785824 * 2 ^ 59
def prefixEnd_785824 : Nat := 4983230072969 + 3 ^ 40 * 785824 * 2
def baseEnd_785824 : Nat := 403505421838838693686067

theorem tailTrace_785824 : CollatzResearch.WordTrace tailWord_785824 prefixEnd_785824 403505421838838693686067 := by
  unfold tailWord_785824
  simp only [CollatzResearch.WordTrace]
  refine ⟨14330677952550665449730263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19107570603400887266307017 14330677952550665449730263)
  ·
    refine ⟨21496016928825998174595395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14330677952550665449730263 21496016928825998174595395)
    ·
      refine ⟨32244025393238997261893093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21496016928825998174595395 32244025393238997261893093)
      ·
        refine ⟨6045754761232311986604955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32244025393238997261893093 6045754761232311986604955)
        ·
          refine ⟨9068632141848467979907433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6045754761232311986604955 9068632141848467979907433)
          ·
            refine ⟨6801474106386350984930575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9068632141848467979907433 6801474106386350984930575)
            ·
              refine ⟨10202211159579526477395863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6801474106386350984930575 10202211159579526477395863)
              ·
                refine ⟨15303316739369289716093795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10202211159579526477395863 15303316739369289716093795)
                ·
                  refine ⟨22954975109053934574140693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15303316739369289716093795 22954975109053934574140693)
                  ·
                    refine ⟨1076014458236903183162845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22954975109053934574140693 1076014458236903183162845)
                    ·
                      refine ⟨403505421838838693686067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1076014458236903183162845 403505421838838693686067)
                      ·
                        rfl

theorem cell23_785824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_785824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785824 prefixEnd_785824 := by exact prefixLift 785824
  have htrace : WordTrace (prefixWord ++ tailWord_785824) baseStart_785824 baseEnd_785824 := by
    simpa [prefixWord, tailWord_785824, baseEnd_785824] using wordTrace_append hprefix tailTrace_785824
  have hstable : (prefixWord ++ tailWord_785824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785824).length < 2 ^ (prefixWord ++ tailWord_785824).sum := by decide
  have hdescent : baseEnd_785824 < baseStart_785824 := by decide
  rcases family_descends (prefixWord ++ tailWord_785824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785854 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_785854 : Nat := 118140960795 + 785854 * 2 ^ 59
def prefixEnd_785854 : Nat := 4983230072969 + 3 ^ 40 * 785854 * 2
def baseEnd_785854 : Nat := 403520826258473576310929

theorem tailTrace_785854 : CollatzResearch.WordTrace tailWord_785854 prefixEnd_785854 403520826258473576310929 := by
  unfold tailWord_785854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3582806261874080752881577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19108300063328430682035077 3582806261874080752881577)
  ·
    refine ⟨2687104696405560564661183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3582806261874080752881577 2687104696405560564661183)
    ·
      refine ⟨4030657044608340846991775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2687104696405560564661183 4030657044608340846991775)
      ·
        refine ⟨6045985566912511270487663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4030657044608340846991775 6045985566912511270487663)
        ·
          refine ⟨9068978350368766905731495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6045985566912511270487663 9068978350368766905731495)
          ·
            refine ⟨13603467525553150358597243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9068978350368766905731495 13603467525553150358597243)
            ·
              refine ⟨20405201288329725537895865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13603467525553150358597243 20405201288329725537895865)
              ·
                refine ⟨15303900966247294153421899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20405201288329725537895865 15303900966247294153421899)
                ·
                  refine ⟨22955851449370941230132849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15303900966247294153421899 22955851449370941230132849)
                  ·
                    refine ⟨17216888587028205922599637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22955851449370941230132849 17216888587028205922599637)
                    ·
                      refine ⟨403520826258473576310929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 17216888587028205922599637 403520826258473576310929)
                      ·
                        rfl

theorem cell23_785854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_785854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785854 prefixEnd_785854 := by exact prefixLift 785854
  have htrace : WordTrace (prefixWord ++ tailWord_785854) baseStart_785854 baseEnd_785854 := by
    simpa [prefixWord, tailWord_785854, baseEnd_785854] using wordTrace_append hprefix tailTrace_785854
  have hstable : (prefixWord ++ tailWord_785854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785854).length < 2 ^ (prefixWord ++ tailWord_785854).sum := by decide
  have hdescent : baseEnd_785854 < baseStart_785854 := by decide
  rcases family_descends (prefixWord ++ tailWord_785854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785878 : List Nat := [5, 2, 1, 1, 1, 3, 2, 1, 7]
def baseStart_785878 : Nat := 118140960795 + 785878 * 2 ^ 59
def prefixEnd_785878 : Nat := 4983230072969 + 3 ^ 40 * 785878 * 2
def baseEnd_785878 : Nat := 44837016643797942490091

theorem tailTrace_785878 : CollatzResearch.WordTrace tailWord_785878 prefixEnd_785878 44837016643797942490091 := by
  unfold tailWord_785878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1791457840431606132620393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19108883631270465414617525 1791457840431606132620393)
  ·
    refine ⟨1343593380323704599465295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1791457840431606132620393 1343593380323704599465295)
    ·
      refine ⟨2015390070485556899197943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1343593380323704599465295 2015390070485556899197943)
      ·
        refine ⟨3023085105728335348796915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2015390070485556899197943 3023085105728335348796915)
        ·
          refine ⟨4534627658592503023195373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3023085105728335348796915 4534627658592503023195373)
          ·
            refine ⟨1700485371972188633698265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4534627658592503023195373 1700485371972188633698265)
            ·
              refine ⟨1275364028979141475273699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1700485371972188633698265 1275364028979141475273699)
              ·
                refine ⟨1913046043468712212910549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1275364028979141475273699 1913046043468712212910549)
                ·
                  refine ⟨44837016643797942490091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1913046043468712212910549 44837016643797942490091)
                  ·
                    rfl

theorem cell23_785878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_785878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785878 prefixEnd_785878 := by exact prefixLift 785878
  have htrace : WordTrace (prefixWord ++ tailWord_785878) baseStart_785878 baseEnd_785878 := by
    simpa [prefixWord, tailWord_785878, baseEnd_785878] using wordTrace_append hprefix tailTrace_785878
  have hstable : (prefixWord ++ tailWord_785878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785878).length < 2 ^ (prefixWord ++ tailWord_785878).sum := by decide
  have hdescent : baseEnd_785878 < baseStart_785878 := by decide
  rcases family_descends (prefixWord ++ tailWord_785878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785911 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 4, 4, 2]
def baseStart_785911 : Nat := 118140960795 + 785911 * 2 ^ 59
def prefixEnd_785911 : Nat := 4983230072969 + 3 ^ 40 * 785911 * 2
def baseEnd_785911 : Nat := 403550094655779853298167

theorem tailTrace_785911 : CollatzResearch.WordTrace tailWord_785911 prefixEnd_785911 403550094655779853298167 := by
  unfold tailWord_785911
  simp only [CollatzResearch.WordTrace]
  refine ⟨28664529055786144757877587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19109686037190763171918391 28664529055786144757877587)
  ·
    refine ⟨42996793583679217136816381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28664529055786144757877587 42996793583679217136816381)
    ·
      refine ⟨16123797593879706426306143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42996793583679217136816381 16123797593879706426306143)
      ·
        refine ⟨24185696390819559639459215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16123797593879706426306143 24185696390819559639459215)
        ·
          refine ⟨36278544586229339459188823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24185696390819559639459215 36278544586229339459188823)
          ·
            refine ⟨54417816879344009188783235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36278544586229339459188823 54417816879344009188783235)
            ·
              refine ⟨81626725319016013783174853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54417816879344009188783235 81626725319016013783174853)
              ·
                refine ⟨15305010997315502584345285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81626725319016013783174853 15305010997315502584345285)
                ·
                  refine ⟨2869689561996656734564741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15305010997315502584345285 2869689561996656734564741)
                  ·
                    refine ⟨538066792874373137730889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2869689561996656734564741 538066792874373137730889)
                    ·
                      refine ⟨403550094655779853298167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 538066792874373137730889 403550094655779853298167)
                      ·
                        rfl

theorem cell23_785911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 4, 2].length) (baseStart_785911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_785911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_785911 prefixEnd_785911 := by exact prefixLift 785911
  have htrace : WordTrace (prefixWord ++ tailWord_785911) baseStart_785911 baseEnd_785911 := by
    simpa [prefixWord, tailWord_785911, baseEnd_785911] using wordTrace_append hprefix tailTrace_785911
  have hstable : (prefixWord ++ tailWord_785911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785911).length < 2 ^ (prefixWord ++ tailWord_785911).sum := by decide
  have hdescent : baseEnd_785911 < baseStart_785911 := by decide
  rcases family_descends (prefixWord ++ tailWord_785911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786001 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 5, 1, 4]
def baseStart_786001 : Nat := 118140960795 + 786001 * 2 ^ 59
def prefixEnd_786001 : Nat := 4983230072969 + 3 ^ 40 * 786001 * 2
def baseEnd_786001 : Nat := 403596307914684501172753

theorem tailTrace_786001 : CollatzResearch.WordTrace tailWord_786001 prefixEnd_786001 403596307914684501172753 := by
  unfold tailWord_786001
  simp only [CollatzResearch.WordTrace]
  refine ⟨28667811625460090128653857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19111874416973393419102571 28667811625460090128653857)
  ·
    refine ⟨21500858719095067596490393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28667811625460090128653857 21500858719095067596490393)
    ·
      refine ⟨16125644039321300697367795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21500858719095067596490393 16125644039321300697367795)
      ·
        refine ⟨24188466058981951046051693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16125644039321300697367795 24188466058981951046051693)
        ·
          refine ⟨9070674772118231642269385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24188466058981951046051693 9070674772118231642269385)
          ·
            refine ⟨6803006079088673731702039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9070674772118231642269385 6803006079088673731702039)
            ·
              refine ⟨10204509118633010597553059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6803006079088673731702039 10204509118633010597553059)
              ·
                refine ⟨15306763677949515896329589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10204509118633010597553059 15306763677949515896329589)
                ·
                  refine ⟨1435009094807767115280899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15306763677949515896329589 1435009094807767115280899)
                  ·
                    refine ⟨2152513642211650672921349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1435009094807767115280899 2152513642211650672921349)
                    ·
                      refine ⟨403596307914684501172753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2152513642211650672921349 403596307914684501172753)
                      ·
                        rfl

theorem cell23_786001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_786001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786001 prefixEnd_786001 := by exact prefixLift 786001
  have htrace : WordTrace (prefixWord ++ tailWord_786001) baseStart_786001 baseEnd_786001 := by
    simpa [prefixWord, tailWord_786001, baseEnd_786001] using wordTrace_append hprefix tailTrace_786001
  have hstable : (prefixWord ++ tailWord_786001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786001).length < 2 ^ (prefixWord ++ tailWord_786001).sum := by decide
  have hdescent : baseEnd_786001 < baseStart_786001 := by decide
  rcases family_descends (prefixWord ++ tailWord_786001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786029 : List Nat := [1, 5, 1, 1, 4, 1, 2, 3, 1, 1, 3]
def baseStart_786029 : Nat := 118140960795 + 786029 * 2 ^ 59
def prefixEnd_786029 : Nat := 4983230072969 + 3 ^ 40 * 786029 * 2
def baseEnd_786029 : Nat := 403610685373010391622625

theorem tailTrace_786029 : CollatzResearch.WordTrace tailWord_786029 prefixEnd_786029 403610685373010391622625 := by
  unfold tailWord_786029
  simp only [CollatzResearch.WordTrace]
  refine ⟨28668832869358650910673141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19112555246239100607115427 28668832869358650910673141)
  ·
    refine ⟨2687703081502373522875607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28668832869358650910673141 2687703081502373522875607)
    ·
      refine ⟨4031554622253560284313411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2687703081502373522875607 4031554622253560284313411)
      ·
        refine ⟨6047331933380340426470117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4031554622253560284313411 6047331933380340426470117)
        ·
          refine ⟨1133874737508813829963147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6047331933380340426470117 1133874737508813829963147)
          ·
            refine ⟨1700812106263220744944721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1133874737508813829963147 1700812106263220744944721)
            ·
              refine ⟨1275609079697415558708541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1700812106263220744944721 1275609079697415558708541)
              ·
                refine ⟨478353404886530834515703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1275609079697415558708541 478353404886530834515703)
                ·
                  refine ⟨717530107329796251773555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 478353404886530834515703 717530107329796251773555)
                  ·
                    refine ⟨1076295160994694377660333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 717530107329796251773555 1076295160994694377660333)
                    ·
                      refine ⟨403610685373010391622625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1076295160994694377660333 403610685373010391622625)
                      ·
                        rfl

theorem cell23_786029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_786029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786029 prefixEnd_786029 := by exact prefixLift 786029
  have htrace : WordTrace (prefixWord ++ tailWord_786029) baseStart_786029 baseEnd_786029 := by
    simpa [prefixWord, tailWord_786029, baseEnd_786029] using wordTrace_append hprefix tailTrace_786029
  have hstable : (prefixWord ++ tailWord_786029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786029).length < 2 ^ (prefixWord ++ tailWord_786029).sum := by decide
  have hdescent : baseEnd_786029 < baseStart_786029 := by decide
  rcases family_descends (prefixWord ++ tailWord_786029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786045 : List Nat := [1, 4, 1, 1, 4, 1, 3, 2, 2, 4]
def baseStart_786045 : Nat := 118140960795 + 786045 * 2 ^ 59
def prefixEnd_786045 : Nat := 4983230072969 + 3 ^ 40 * 786045 * 2
def baseEnd_786045 : Nat := 134539633687827443007517

theorem tailTrace_786045 : CollatzResearch.WordTrace tailWord_786045 prefixEnd_786045 134539633687827443007517 := by
  unfold tailWord_786045
  simp only [CollatzResearch.WordTrace]
  refine ⟨28669416437300685643255589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19112944291533790428837059 28669416437300685643255589)
  ·
    refine ⟨5375515581993878558110423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28669416437300685643255589 5375515581993878558110423)
    ·
      refine ⟨8063273372990817837165635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5375515581993878558110423 8063273372990817837165635)
      ·
        refine ⟨12094910059486226755748453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8063273372990817837165635 12094910059486226755748453)
        ·
          refine ⟨2267795636153667516702835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12094910059486226755748453 2267795636153667516702835)
          ·
            refine ⟨3401693454230501275054253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2267795636153667516702835 3401693454230501275054253)
            ·
              refine ⟨1275635045336437978145345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3401693454230501275054253 1275635045336437978145345)
              ·
                refine ⟨956726284002328483609009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1275635045336437978145345 956726284002328483609009)
                ·
                  refine ⟨717544713001746362706757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 956726284002328483609009 717544713001746362706757)
                  ·
                    refine ⟨134539633687827443007517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 717544713001746362706757 134539633687827443007517)
                    ·
                      rfl

theorem cell23_786045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_786045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786045 prefixEnd_786045 := by exact prefixLift 786045
  have htrace : WordTrace (prefixWord ++ tailWord_786045) baseStart_786045 baseEnd_786045 := by
    simpa [prefixWord, tailWord_786045, baseEnd_786045] using wordTrace_append hprefix tailTrace_786045
  have hstable : (prefixWord ++ tailWord_786045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786045).length < 2 ^ (prefixWord ++ tailWord_786045).sum := by decide
  have hdescent : baseEnd_786045 < baseStart_786045 := by decide
  rcases family_descends (prefixWord ++ tailWord_786045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786062 : List Nat := [4, 1, 1, 3, 1, 3, 3, 1, 2, 4]
def baseStart_786062 : Nat := 118140960795 + 786062 * 2 ^ 59
def prefixEnd_786062 : Nat := 4983230072969 + 3 ^ 40 * 786062 * 2
def baseEnd_786062 : Nat := 134542543411536254169991

theorem tailTrace_786062 : CollatzResearch.WordTrace tailWord_786062 prefixEnd_786062 134542543411536254169991 := by
  unfold tailWord_786062
  simp only [CollatzResearch.WordTrace]
  refine ⟨3583754559779887193328055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19113357652159398364416293 3583754559779887193328055)
  ·
    refine ⟨5375631839669830789992083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3583754559779887193328055 5375631839669830789992083)
    ·
      refine ⟨8063447759504746184988125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5375631839669830789992083 8063447759504746184988125)
      ·
        refine ⟨3023792909814279819370547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8063447759504746184988125 3023792909814279819370547)
        ·
          refine ⟨4535689364721419729055821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3023792909814279819370547 4535689364721419729055821)
          ·
            refine ⟨1700883511770532398395933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4535689364721419729055821 1700883511770532398395933)
            ·
              refine ⟨637831316913949649398475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1700883511770532398395933 637831316913949649398475)
              ·
                refine ⟨956746975370924474097713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 637831316913949649398475 956746975370924474097713)
                ·
                  refine ⟨717560231528193355573285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 956746975370924474097713 717560231528193355573285)
                  ·
                    refine ⟨134542543411536254169991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 717560231528193355573285 134542543411536254169991)
                    ·
                      rfl

theorem cell23_786062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_786062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786062 prefixEnd_786062 := by exact prefixLift 786062
  have htrace : WordTrace (prefixWord ++ tailWord_786062) baseStart_786062 baseEnd_786062 := by
    simpa [prefixWord, tailWord_786062, baseEnd_786062] using wordTrace_append hprefix tailTrace_786062
  have hstable : (prefixWord ++ tailWord_786062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786062).length < 2 ^ (prefixWord ++ tailWord_786062).sum := by decide
  have hdescent : baseEnd_786062 < baseStart_786062 := by decide
  rcases family_descends (prefixWord ++ tailWord_786062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786095 : List Nat := [1, 1, 2, 1, 2, 4, 1, 5, 1, 3, 2]
def baseStart_786095 : Nat := 118140960795 + 786095 * 2 ^ 59
def prefixEnd_786095 : Nat := 4983230072969 + 3 ^ 40 * 786095 * 2
def baseEnd_786095 : Nat := 403644575096207133397321

theorem tailTrace_786095 : CollatzResearch.WordTrace tailWord_786095 prefixEnd_786095 403644575096207133397321 := by
  unfold tailWord_786095
  simp only [CollatzResearch.WordTrace]
  refine ⟨28671240087119544182575739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19114160058079696121717159 28671240087119544182575739)
  ·
    refine ⟨43006860130679316273863609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28671240087119544182575739 43006860130679316273863609)
    ·
      refine ⟨32255145098009487205397707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43006860130679316273863609 32255145098009487205397707)
      ·
        refine ⟨48382717647014230808096561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32255145098009487205397707 48382717647014230808096561)
        ·
          refine ⟨36287038235260673106072421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48382717647014230808096561 36287038235260673106072421)
          ·
            refine ⟨6803819669111376207388579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36287038235260673106072421 6803819669111376207388579)
            ·
              refine ⟨10205729503667064311082869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6803819669111376207388579 10205729503667064311082869)
              ·
                refine ⟨956787140968787279164019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10205729503667064311082869 956787140968787279164019)
                ·
                  refine ⟨1435180711453180918746029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 956787140968787279164019 1435180711453180918746029)
                  ·
                    refine ⟨538192766794942844529761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1435180711453180918746029 538192766794942844529761)
                    ·
                      refine ⟨403644575096207133397321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 538192766794942844529761 403644575096207133397321)
                      ·
                        rfl

theorem cell23_786095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 3, 2].length) (baseStart_786095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786095 prefixEnd_786095 := by exact prefixLift 786095
  have htrace : WordTrace (prefixWord ++ tailWord_786095) baseStart_786095 baseEnd_786095 := by
    simpa [prefixWord, tailWord_786095, baseEnd_786095] using wordTrace_append hprefix tailTrace_786095
  have hstable : (prefixWord ++ tailWord_786095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786095).length < 2 ^ (prefixWord ++ tailWord_786095).sum := by decide
  have hdescent : baseEnd_786095 < baseStart_786095 := by decide
  rcases family_descends (prefixWord ++ tailWord_786095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786111 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 5]
def baseStart_786111 : Nat := 118140960795 + 786111 * 2 ^ 59
def prefixEnd_786111 : Nat := 4983230072969 + 3 ^ 40 * 786111 * 2
def baseEnd_786111 : Nat := 403652790786679070797247

theorem tailTrace_786111 : CollatzResearch.WordTrace tailWord_786111 prefixEnd_786111 403652790786679070797247 := by
  unfold tailWord_786111
  simp only [CollatzResearch.WordTrace]
  refine ⟨28671823655061578915158187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19114549103374385943438791 28671823655061578915158187)
  ·
    refine ⟨43007735482592368372737281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28671823655061578915158187 43007735482592368372737281)
    ·
      refine ⟨32255801611944276279552961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43007735482592368372737281 32255801611944276279552961)
      ·
        refine ⟨24191851208958207209664721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32255801611944276279552961 24191851208958207209664721)
        ·
          refine ⟨18143888406718655407248541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24191851208958207209664721 18143888406718655407248541)
          ·
            refine ⟨6803958152519495777718203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18143888406718655407248541 6803958152519495777718203)
            ·
              refine ⟨10205937228779243666577305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6803958152519495777718203 10205937228779243666577305)
              ·
                refine ⟨7654452921584432749932979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10205937228779243666577305 7654452921584432749932979)
                ·
                  refine ⟨11481679382376649124899469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7654452921584432749932979 11481679382376649124899469)
                  ·
                    refine ⟨4305629768391243421837301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11481679382376649124899469 4305629768391243421837301)
                    ·
                      refine ⟨403652790786679070797247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4305629768391243421837301 403652790786679070797247)
                      ·
                        rfl

theorem cell23_786111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_786111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786111 prefixEnd_786111 := by exact prefixLift 786111
  have htrace : WordTrace (prefixWord ++ tailWord_786111) baseStart_786111 baseEnd_786111 := by
    simpa [prefixWord, tailWord_786111, baseEnd_786111] using wordTrace_append hprefix tailTrace_786111
  have hstable : (prefixWord ++ tailWord_786111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786111).length < 2 ^ (prefixWord ++ tailWord_786111).sum := by decide
  have hdescent : baseEnd_786111 < baseStart_786111 := by decide
  rcases family_descends (prefixWord ++ tailWord_786111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786171 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 7]
def baseStart_786171 : Nat := 118140960795 + 786171 * 2 ^ 59
def prefixEnd_786171 : Nat := 4983230072969 + 3 ^ 40 * 786171 * 2
def baseEnd_786171 : Nat := 403683599625948836046971

theorem tailTrace_786171 : CollatzResearch.WordTrace tailWord_786171 prefixEnd_786171 403683599625948836046971 := by
  unfold tailWord_786171
  simp only [CollatzResearch.WordTrace]
  refine ⟨28674012034844209162342367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19116008023229472774894911 28674012034844209162342367)
  ·
    refine ⟨43011018052266313743513551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28674012034844209162342367 43011018052266313743513551)
    ·
      refine ⟨64516527078399470615270327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43011018052266313743513551 64516527078399470615270327)
      ·
        refine ⟨96774790617599205922905491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64516527078399470615270327 96774790617599205922905491)
        ·
          refine ⟨145162185926398808884358237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96774790617599205922905491 145162185926398808884358237)
          ·
            refine ⟨54435819722399553331634339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145162185926398808884358237 54435819722399553331634339)
            ·
              refine ⟨81653729583599329997451509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54435819722399553331634339 81653729583599329997451509)
              ·
                refine ⟨7655037148462437187261079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81653729583599329997451509 7655037148462437187261079)
                ·
                  refine ⟨11482555722693655780891619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7655037148462437187261079 11482555722693655780891619)
                  ·
                    refine ⟨17223833584040483671337429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11482555722693655780891619 17223833584040483671337429)
                    ·
                      refine ⟨403683599625948836046971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 17223833584040483671337429 403683599625948836046971)
                      ·
                        rfl

theorem cell23_786171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 7].length) (baseStart_786171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786171 prefixEnd_786171 := by exact prefixLift 786171
  have htrace : WordTrace (prefixWord ++ tailWord_786171) baseStart_786171 baseEnd_786171 := by
    simpa [prefixWord, tailWord_786171, baseEnd_786171] using wordTrace_append hprefix tailTrace_786171
  have hstable : (prefixWord ++ tailWord_786171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786171).length < 2 ^ (prefixWord ++ tailWord_786171).sum := by decide
  have hdescent : baseEnd_786171 < baseStart_786171 := by decide
  rcases family_descends (prefixWord ++ tailWord_786171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786191 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 1, 10]
def baseStart_786191 : Nat := 118140960795 + 786191 * 2 ^ 59
def prefixEnd_786191 : Nat := 4983230072969 + 3 ^ 40 * 786191 * 2
def baseEnd_786191 : Nat := 134564623079679585932293

theorem tailTrace_786191 : CollatzResearch.WordTrace tailWord_786191 prefixEnd_786191 134564623079679585932293 := by
  unfold tailWord_786191
  simp only [CollatzResearch.WordTrace]
  refine ⟨28674741494771752578070427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19116494329847835052046951 28674741494771752578070427)
  ·
    refine ⟨43012112242157628867105641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28674741494771752578070427 43012112242157628867105641)
    ·
      refine ⟨32259084181618221650329231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43012112242157628867105641 32259084181618221650329231)
      ·
        refine ⟨48388626272427332475493847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32259084181618221650329231 48388626272427332475493847)
        ·
          refine ⟨72582939408640998713240771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48388626272427332475493847 72582939408640998713240771)
          ·
            refine ⟨108874409112961498069861157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72582939408640998713240771 108874409112961498069861157)
            ·
              refine ⟨20413951708680280888098967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108874409112961498069861157 20413951708680280888098967)
              ·
                refine ⟨30620927563020421332148451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20413951708680280888098967 30620927563020421332148451)
                ·
                  refine ⟨45931391344530631998222677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30620927563020421332148451 45931391344530631998222677)
                  ·
                    refine ⟨134564623079679585932293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 45931391344530631998222677 134564623079679585932293)
                    ·
                      rfl

theorem cell23_786191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 10].length) (baseStart_786191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786191 prefixEnd_786191 := by exact prefixLift 786191
  have htrace : WordTrace (prefixWord ++ tailWord_786191) baseStart_786191 baseEnd_786191 := by
    simpa [prefixWord, tailWord_786191, baseEnd_786191] using wordTrace_append hprefix tailTrace_786191
  have hstable : (prefixWord ++ tailWord_786191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786191).length < 2 ^ (prefixWord ++ tailWord_786191).sum := by decide
  have hdescent : baseEnd_786191 < baseStart_786191 := by decide
  rcases family_descends (prefixWord ++ tailWord_786191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786225 : List Nat := [1, 2, 2, 3, 2, 2, 1, 3, 3, 4]
def baseStart_786225 : Nat := 118140960795 + 786225 * 2 ^ 59
def prefixEnd_786225 : Nat := 4983230072969 + 3 ^ 40 * 786225 * 2
def baseEnd_786225 : Nat := 134570442527097208257241

theorem tailTrace_786225 : CollatzResearch.WordTrace tailWord_786225 prefixEnd_786225 134570442527097208257241 := by
  unfold tailWord_786225
  simp only [CollatzResearch.WordTrace]
  refine ⟨28675981576648576384808129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19117321051099050923205419 28675981576648576384808129)
  ·
    refine ⟨21506986182486432288606097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28675981576648576384808129 21506986182486432288606097)
    ·
      refine ⟨16130239636864824216454573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21506986182486432288606097 16130239636864824216454573)
      ·
        refine ⟨6048839863824309081170465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16130239636864824216454573 6048839863824309081170465)
        ·
          refine ⟨4536629897868231810877849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6048839863824309081170465 4536629897868231810877849)
          ·
            refine ⟨3402472423401173858158387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4536629897868231810877849 3402472423401173858158387)
            ·
              refine ⟨5103708635101760787237581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3402472423401173858158387 5103708635101760787237581)
              ·
                refine ⟨1913890738163160295214093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5103708635101760787237581 1913890738163160295214093)
                ·
                  refine ⟨717709026811185110705285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1913890738163160295214093 717709026811185110705285)
                  ·
                    refine ⟨134570442527097208257241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 717709026811185110705285 134570442527097208257241)
                    ·
                      rfl

theorem cell23_786225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 4].length) (baseStart_786225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786225 prefixEnd_786225 := by exact prefixLift 786225
  have htrace : WordTrace (prefixWord ++ tailWord_786225) baseStart_786225 baseEnd_786225 := by
    simpa [prefixWord, tailWord_786225, baseEnd_786225] using wordTrace_append hprefix tailTrace_786225
  have hstable : (prefixWord ++ tailWord_786225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786225).length < 2 ^ (prefixWord ++ tailWord_786225).sum := by decide
  have hdescent : baseEnd_786225 < baseStart_786225 := by decide
  rcases family_descends (prefixWord ++ tailWord_786225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786276 : List Nat := [2, 3, 1, 1, 5, 1, 3, 2, 1, 4]
def baseStart_786276 : Nat := 118140960795 + 786276 * 2 ^ 59
def prefixEnd_786276 : Nat := 4983230072969 + 3 ^ 40 * 786276 * 2
def baseEnd_786276 : Nat := 134579171698223641744663

theorem tailTrace_786276 : CollatzResearch.WordTrace tailWord_786276 prefixEnd_786276 134579171698223641744663 := by
  unfold tailWord_786276
  simp only [CollatzResearch.WordTrace]
  refine ⟨14338920849731906047457341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19118561132975874729943121 14338920849731906047457341)
  ·
    refine ⟨5377095318649464767796503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14338920849731906047457341 5377095318649464767796503)
    ·
      refine ⟨8065642977974197151694755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5377095318649464767796503 8065642977974197151694755)
      ·
        refine ⟨12098464466961295727542133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8065642977974197151694755 12098464466961295727542133)
        ·
          refine ⟨1134231043777621474457075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12098464466961295727542133 1134231043777621474457075)
          ·
            refine ⟨1701346565666432211685613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1134231043777621474457075 1701346565666432211685613)
            ·
              refine ⟨638004962124912079382105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1701346565666432211685613 638004962124912079382105)
              ·
                refine ⟨478503721593684059536579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 638004962124912079382105 478503721593684059536579)
                ·
                  refine ⟨717755582390526089304869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 478503721593684059536579 717755582390526089304869)
                  ·
                    refine ⟨134579171698223641744663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 717755582390526089304869 134579171698223641744663)
                    ·
                      rfl

theorem cell23_786276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_786276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786276 prefixEnd_786276 := by exact prefixLift 786276
  have htrace : WordTrace (prefixWord ++ tailWord_786276) baseStart_786276 baseEnd_786276 := by
    simpa [prefixWord, tailWord_786276, baseEnd_786276] using wordTrace_append hprefix tailTrace_786276
  have hstable : (prefixWord ++ tailWord_786276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786276).length < 2 ^ (prefixWord ++ tailWord_786276).sum := by decide
  have hdescent : baseEnd_786276 < baseStart_786276 := by decide
  rcases family_descends (prefixWord ++ tailWord_786276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786288 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 4]
def baseStart_786288 : Nat := 118140960795 + 786288 * 2 ^ 59
def prefixEnd_786288 : Nat := 4983230072969 + 3 ^ 40 * 786288 * 2
def baseEnd_786288 : Nat := 403743676862524878283933

theorem tailTrace_786288 : CollatzResearch.WordTrace tailWord_786288 prefixEnd_786288 403743676862524878283933 := by
  unfold tailWord_786288
  simp only [CollatzResearch.WordTrace]
  refine ⟨14339139687710169072175759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19118852916946892096234345 14339139687710169072175759)
  ·
    refine ⟨21508709531565253608263639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14339139687710169072175759 21508709531565253608263639)
    ·
      refine ⟨32263064297347880412395459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21508709531565253608263639 32263064297347880412395459)
      ·
        refine ⟨48394596446021820618593189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32263064297347880412395459 48394596446021820618593189)
        ·
          refine ⟨9073986833629091365986223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48394596446021820618593189 9073986833629091365986223)
          ·
            refine ⟨13610980250443637048979335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9073986833629091365986223 13610980250443637048979335)
            ·
              refine ⟨20416470375665455573469003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13610980250443637048979335 20416470375665455573469003)
              ·
                refine ⟨30624705563498183360203505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20416470375665455573469003 30624705563498183360203505)
                ·
                  refine ⟨22968529172623637520152629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30624705563498183360203505 22968529172623637520152629)
                  ·
                    refine ⟨2153299609933466017514309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22968529172623637520152629 2153299609933466017514309)
                    ·
                      refine ⟨403743676862524878283933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2153299609933466017514309 403743676862524878283933)
                      ·
                        rfl

theorem cell23_786288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 4].length) (baseStart_786288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786288 prefixEnd_786288 := by exact prefixLift 786288
  have htrace : WordTrace (prefixWord ++ tailWord_786288) baseStart_786288 baseEnd_786288 := by
    simpa [prefixWord, tailWord_786288, baseEnd_786288] using wordTrace_append hprefix tailTrace_786288
  have hstable : (prefixWord ++ tailWord_786288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786288).length < 2 ^ (prefixWord ++ tailWord_786288).sum := by decide
  have hdescent : baseEnd_786288 < baseStart_786288 := by decide
  rcases family_descends (prefixWord ++ tailWord_786288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786333 : List Nat := [1, 4, 2, 1, 2, 4, 2, 2, 1, 1, 3]
def baseStart_786333 : Nat := 118140960795 + 786333 * 2 ^ 59
def prefixEnd_786333 : Nat := 4983230072969 + 3 ^ 40 * 786333 * 2
def baseEnd_786333 : Nat := 403766783491977202221227

theorem tailTrace_786333 : CollatzResearch.WordTrace tailWord_786333 prefixEnd_786333 403766783491977202221227 := by
  unfold tailWord_786333
  simp only [CollatzResearch.WordTrace]
  refine ⟨28679920660257310829739653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19119947106838207219826435 28679920660257310829739653)
  ·
    refine ⟨5377485123798245780576185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28679920660257310829739653 5377485123798245780576185)
    ·
      refine ⟨4033113842848684335432139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5377485123798245780576185 4033113842848684335432139)
      ·
        refine ⟨6049670764273026503148209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4033113842848684335432139 6049670764273026503148209)
        ·
          refine ⟨4537253073204769877361157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6049670764273026503148209 4537253073204769877361157)
          ·
            refine ⟨850734951225894352005217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4537253073204769877361157 850734951225894352005217)
            ·
              refine ⟨638051213419420764003913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 850734951225894352005217 638051213419420764003913)
              ·
                refine ⟨478538410064565573002935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 638051213419420764003913 478538410064565573002935)
                ·
                  refine ⟨717807615096848359504403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 478538410064565573002935 717807615096848359504403)
                  ·
                    refine ⟨1076711422645272539256605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 717807615096848359504403 1076711422645272539256605)
                    ·
                      refine ⟨403766783491977202221227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1076711422645272539256605 403766783491977202221227)
                      ·
                        rfl

theorem cell23_786333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_786333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786333 prefixEnd_786333 := by exact prefixLift 786333
  have htrace : WordTrace (prefixWord ++ tailWord_786333) baseStart_786333 baseEnd_786333 := by
    simpa [prefixWord, tailWord_786333, baseEnd_786333] using wordTrace_append hprefix tailTrace_786333
  have hstable : (prefixWord ++ tailWord_786333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786333).length < 2 ^ (prefixWord ++ tailWord_786333).sum := by decide
  have hdescent : baseEnd_786333 < baseStart_786333 := by decide
  rcases family_descends (prefixWord ++ tailWord_786333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786376 : List Nat := [2, 1, 3, 1, 4, 3, 2, 1, 1, 2, 3]
def baseStart_786376 : Nat := 118140960795 + 786376 * 2 ^ 59
def prefixEnd_786376 : Nat := 4983230072969 + 3 ^ 40 * 786376 * 2
def baseEnd_786376 : Nat := 403788863160120533983529

theorem tailTrace_786376 : CollatzResearch.WordTrace tailWord_786376 prefixEnd_786376 403788863160120533983529 := by
  unfold tailWord_786376
  simp only [CollatzResearch.WordTrace]
  refine ⟨14340744499550764586777491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19120992666067686115703321 14340744499550764586777491)
  ·
    refine ⟨21511116749326146880166237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14340744499550764586777491 21511116749326146880166237)
    ·
      refine ⟨8066668780997305080062339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21511116749326146880166237 8066668780997305080062339)
      ·
        refine ⟨12100003171495957620093509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8066668780997305080062339 12100003171495957620093509)
        ·
          refine ⟨2268750594655492053767533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12100003171495957620093509 2268750594655492053767533)
          ·
            refine ⟨850781472995809520162825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2268750594655492053767533 850781472995809520162825)
            ·
              refine ⟨638086104746857140122119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 850781472995809520162825 638086104746857140122119)
              ·
                refine ⟨957129157120285710183179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 638086104746857140122119 957129157120285710183179)
                ·
                  refine ⟨1435693735680428565274769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 957129157120285710183179 1435693735680428565274769)
                  ·
                    refine ⟨1076770301760321423956077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1435693735680428565274769 1076770301760321423956077)
                    ·
                      refine ⟨403788863160120533983529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1076770301760321423956077 403788863160120533983529)
                      ·
                        rfl

theorem cell23_786376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 1, 2, 3].length) (baseStart_786376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786376 prefixEnd_786376 := by exact prefixLift 786376
  have htrace : WordTrace (prefixWord ++ tailWord_786376) baseStart_786376 baseEnd_786376 := by
    simpa [prefixWord, tailWord_786376, baseEnd_786376] using wordTrace_append hprefix tailTrace_786376
  have hstable : (prefixWord ++ tailWord_786376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786376).length < 2 ^ (prefixWord ++ tailWord_786376).sum := by decide
  have hdescent : baseEnd_786376 < baseStart_786376 := by decide
  rcases family_descends (prefixWord ++ tailWord_786376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786389 : List Nat := [1, 3, 2, 3, 2, 2, 1, 1, 4, 1, 3]
def baseStart_786389 : Nat := 118140960795 + 786389 * 2 ^ 59
def prefixEnd_786389 : Nat := 4983230072969 + 3 ^ 40 * 786389 * 2
def baseEnd_786389 : Nat := 403795538408628983120969

theorem tailTrace_786389 : CollatzResearch.WordTrace tailWord_786389 prefixEnd_786389 403795538408628983120969 := by
  unfold tailWord_786389
  simp only [CollatzResearch.WordTrace]
  refine ⟨28681963148054432393778221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19121308765369621595852147 28681963148054432393778221)
  ·
    refine ⟨10755736180520412147666833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28681963148054432393778221 10755736180520412147666833)
    ·
      refine ⟨8066802135390309110750125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10755736180520412147666833 8066802135390309110750125)
      ·
        refine ⟨3025050800771365916531297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8066802135390309110750125 3025050800771365916531297)
        ·
          refine ⟨2268788100578524437398473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3025050800771365916531297 2268788100578524437398473)
          ·
            refine ⟨1701591075433893328048855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2268788100578524437398473 1701591075433893328048855)
            ·
              refine ⟨2552386613150839992073283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1701591075433893328048855 2552386613150839992073283)
              ·
                refine ⟨3828579919726259988109925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2552386613150839992073283 3828579919726259988109925)
                ·
                  refine ⟨717858734948673747770611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3828579919726259988109925 717858734948673747770611)
                  ·
                    refine ⟨1076788102423010621655917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 717858734948673747770611 1076788102423010621655917)
                    ·
                      refine ⟨403795538408628983120969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1076788102423010621655917 403795538408628983120969)
                      ·
                        rfl

theorem cell23_786389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_786389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786389 prefixEnd_786389 := by exact prefixLift 786389
  have htrace : WordTrace (prefixWord ++ tailWord_786389) baseStart_786389 baseEnd_786389 := by
    simpa [prefixWord, tailWord_786389, baseEnd_786389] using wordTrace_append hprefix tailTrace_786389
  have hstable : (prefixWord ++ tailWord_786389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786389).length < 2 ^ (prefixWord ++ tailWord_786389).sum := by decide
  have hdescent : baseEnd_786389 < baseStart_786389 := by decide
  rcases family_descends (prefixWord ++ tailWord_786389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786415 : List Nat := [1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 5]
def baseStart_786415 : Nat := 118140960795 + 786415 * 2 ^ 59
def prefixEnd_786415 : Nat := 4983230072969 + 3 ^ 40 * 786415 * 2
def baseEnd_786415 : Nat := 403808888905645881395849

theorem tailTrace_786415 : CollatzResearch.WordTrace tailWord_786415 prefixEnd_786415 403808888905645881395849 := by
  unfold tailWord_786415
  simp only [CollatzResearch.WordTrace]
  refine ⟨28682911445960238834224699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19121940963973492556149799 28682911445960238834224699)
  ·
    refine ⟨43024367168940358251337049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28682911445960238834224699 43024367168940358251337049)
    ·
      refine ⟨32268275376705268688502787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43024367168940358251337049 32268275376705268688502787)
      ·
        refine ⟨48402413065057903032754181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32268275376705268688502787 48402413065057903032754181)
        ·
          refine ⟨9075452449698356818641409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48402413065057903032754181 9075452449698356818641409)
          ·
            refine ⟨6806589337273767613981057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9075452449698356818641409 6806589337273767613981057)
            ·
              refine ⟨5104942002955325710485793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6806589337273767613981057 5104942002955325710485793)
              ·
                refine ⟨3828706502216494282864345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5104942002955325710485793 3828706502216494282864345)
                ·
                  refine ⟨2871529876662370712148259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3828706502216494282864345 2871529876662370712148259)
                  ·
                    refine ⟨4307294814993556068222389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2871529876662370712148259 4307294814993556068222389)
                    ·
                      refine ⟨403808888905645881395849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4307294814993556068222389 403808888905645881395849)
                      ·
                        rfl

theorem cell23_786415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 5].length) (baseStart_786415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786415 prefixEnd_786415 := by exact prefixLift 786415
  have htrace : WordTrace (prefixWord ++ tailWord_786415) baseStart_786415 baseEnd_786415 := by
    simpa [prefixWord, tailWord_786415, baseEnd_786415] using wordTrace_append hprefix tailTrace_786415
  have hstable : (prefixWord ++ tailWord_786415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786415).length < 2 ^ (prefixWord ++ tailWord_786415).sum := by decide
  have hdescent : baseEnd_786415 < baseStart_786415 := by decide
  rcases family_descends (prefixWord ++ tailWord_786415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786429 : List Nat := [1, 4, 1, 1, 1, 2, 3, 2, 4, 2, 2]
def baseStart_786429 : Nat := 118140960795 + 786429 * 2 ^ 59
def prefixEnd_786429 : Nat := 4983230072969 + 3 ^ 40 * 786429 * 2
def baseEnd_786429 : Nat := 403816077634808826620785

theorem tailTrace_786429 : CollatzResearch.WordTrace tailWord_786429 prefixEnd_786429 403816077634808826620785 := by
  unfold tailWord_786429
  simp only [CollatzResearch.WordTrace]
  refine ⟨28683422067909519225234341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19122281378606346150156227 28683422067909519225234341)
  ·
    refine ⟨5378141637733034854731439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28683422067909519225234341 5378141637733034854731439)
    ·
      refine ⟨8067212456599552282097159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5378141637733034854731439 8067212456599552282097159)
      ·
        refine ⟨12100818684899328423145739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8067212456599552282097159 12100818684899328423145739)
        ·
          refine ⟨18151228027348992634718609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12100818684899328423145739 18151228027348992634718609)
          ·
            refine ⟨13613421020511744476038957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18151228027348992634718609 13613421020511744476038957)
            ·
              refine ⟨5105032882691904178514609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13613421020511744476038957 5105032882691904178514609)
              ·
                refine ⟨3828774662018928133885957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5105032882691904178514609 3828774662018928133885957)
                ·
                  refine ⟨717895249128549025103617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3828774662018928133885957 717895249128549025103617)
                  ·
                    refine ⟨538421436846411768827713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 717895249128549025103617 538421436846411768827713)
                    ·
                      refine ⟨403816077634808826620785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 538421436846411768827713 403816077634808826620785)
                      ·
                        rfl

theorem cell23_786429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4, 2, 2].length) (baseStart_786429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786429 prefixEnd_786429 := by exact prefixLift 786429
  have htrace : WordTrace (prefixWord ++ tailWord_786429) baseStart_786429 baseEnd_786429 := by
    simpa [prefixWord, tailWord_786429, baseEnd_786429] using wordTrace_append hprefix tailTrace_786429
  have hstable : (prefixWord ++ tailWord_786429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786429).length < 2 ^ (prefixWord ++ tailWord_786429).sum := by decide
  have hdescent : baseEnd_786429 < baseStart_786429 := by decide
  rcases family_descends (prefixWord ++ tailWord_786429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786446 : List Nat := [4, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2]
def baseStart_786446 : Nat := 118140960795 + 786446 * 2 ^ 59
def prefixEnd_786446 : Nat := 4983230072969 + 3 ^ 40 * 786446 * 2
def baseEnd_786446 : Nat := 403824806805935260108207

theorem tailTrace_786446 : CollatzResearch.WordTrace tailWord_786446 prefixEnd_786446 403824806805935260108207 := by
  unfold tailWord_786446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3585505263605991391075399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19122694739231954085735461 3585505263605991391075399)
  ·
    refine ⟨5378257895408987086613099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3585505263605991391075399 5378257895408987086613099)
    ·
      refine ⟨8067386843113480629919649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5378257895408987086613099 8067386843113480629919649)
      ·
        refine ⟨6050540132335110472439737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8067386843113480629919649 6050540132335110472439737)
        ·
          refine ⟨4537905099251332854329803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6050540132335110472439737 4537905099251332854329803)
          ·
            refine ⟨6806857648876999281494705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4537905099251332854329803 6806857648876999281494705)
            ·
              refine ⟨5105143236657749461121029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6806857648876999281494705 5105143236657749461121029)
              ·
                refine ⟨957214356873328023960193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5105143236657749461121029 957214356873328023960193)
                ·
                  refine ⟨717910767654996017970145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 957214356873328023960193 717910767654996017970145)
                  ·
                    refine ⟨538433075741247013477609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 717910767654996017970145 538433075741247013477609)
                    ·
                      refine ⟨403824806805935260108207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 538433075741247013477609 403824806805935260108207)
                      ·
                        rfl

theorem cell23_786446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_786446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786446 prefixEnd_786446 := by exact prefixLift 786446
  have htrace : WordTrace (prefixWord ++ tailWord_786446) baseStart_786446 baseEnd_786446 := by
    simpa [prefixWord, tailWord_786446, baseEnd_786446] using wordTrace_append hprefix tailTrace_786446
  have hstable : (prefixWord ++ tailWord_786446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786446).length < 2 ^ (prefixWord ++ tailWord_786446).sum := by decide
  have hdescent : baseEnd_786446 < baseStart_786446 := by decide
  rcases family_descends (prefixWord ++ tailWord_786446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786482 : List Nat := [3, 2, 1, 1, 2, 3, 1, 3, 2, 5]
def baseStart_786482 : Nat := 118140960795 + 786482 * 2 ^ 59
def prefixEnd_786482 : Nat := 4983230072969 + 3 ^ 40 * 786482 * 2
def baseEnd_786482 : Nat := 134614430703165706419347

theorem tailTrace_786482 : CollatzResearch.WordTrace tailWord_786482 prefixEnd_786482 134614430703165706419347 := by
  unfold tailWord_786482
  simp only [CollatzResearch.WordTrace]
  refine ⟨7171338784179377319228425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19123570091145006184609133 7171338784179377319228425)
  ·
    refine ⟨5378504088134532989421319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7171338784179377319228425 5378504088134532989421319)
    ·
      refine ⟨8067756132201799484131979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5378504088134532989421319 8067756132201799484131979)
      ·
        refine ⟨12101634198302699226197969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8067756132201799484131979 12101634198302699226197969)
        ·
          refine ⟨9076225648727024419648477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12101634198302699226197969 9076225648727024419648477)
          ·
            refine ⟨3403584618272634157368179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9076225648727024419648477 3403584618272634157368179)
            ·
              refine ⟨5105376927408951236052269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3403584618272634157368179 5105376927408951236052269)
              ·
                refine ⟨1914516347778356713519601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5105376927408951236052269 1914516347778356713519601)
                ·
                  refine ⟨1435887260833767535139701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1914516347778356713519601 1435887260833767535139701)
                  ·
                    refine ⟨134614430703165706419347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1435887260833767535139701 134614430703165706419347)
                    ·
                      rfl

theorem cell23_786482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_786482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786482 prefixEnd_786482 := by exact prefixLift 786482
  have htrace : WordTrace (prefixWord ++ tailWord_786482) baseStart_786482 baseEnd_786482 := by
    simpa [prefixWord, tailWord_786482, baseEnd_786482] using wordTrace_append hprefix tailTrace_786482
  have hstable : (prefixWord ++ tailWord_786482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786482).length < 2 ^ (prefixWord ++ tailWord_786482).sum := by decide
  have hdescent : baseEnd_786482 < baseStart_786482 := by decide
  rcases family_descends (prefixWord ++ tailWord_786482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786505 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 2, 3, 5]
def baseStart_786505 : Nat := 118140960795 + 786505 * 2 ^ 59
def prefixEnd_786505 : Nat := 4983230072969 + 3 ^ 40 * 786505 * 2
def baseEnd_786505 : Nat := 403855102164550529270435

theorem tailTrace_786505 : CollatzResearch.WordTrace tailWord_786505 prefixEnd_786505 403855102164550529270435 := by
  unfold tailWord_786505
  simp only [CollatzResearch.WordTrace]
  refine ⟨28686194015634184205000969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19124129343756122803333979 28686194015634184205000969)
  ·
    refine ⟨21514645511725638153750727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28686194015634184205000969 21514645511725638153750727)
    ·
      refine ⟨32271968267588457230626091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21514645511725638153750727 32271968267588457230626091)
      ·
        refine ⟨48407952401382685845939137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32271968267588457230626091 48407952401382685845939137)
        ·
          refine ⟨36305964301037014384454353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48407952401382685845939137 36305964301037014384454353)
          ·
            refine ⟨27229473225777760788340765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36305964301037014384454353 27229473225777760788340765)
            ·
              refine ⟨10211052459666660295627787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27229473225777760788340765 10211052459666660295627787)
              ·
                refine ⟨15316578689499990443441681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10211052459666660295627787 15316578689499990443441681)
                ·
                  refine ⟨11487434017124992832581261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15316578689499990443441681 11487434017124992832581261)
                  ·
                    refine ⟨4307787756421872312217973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11487434017124992832581261 4307787756421872312217973)
                    ·
                      refine ⟨403855102164550529270435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4307787756421872312217973 403855102164550529270435)
                      ·
                        rfl

theorem cell23_786505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 3, 5].length) (baseStart_786505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786505 prefixEnd_786505 := by exact prefixLift 786505
  have htrace : WordTrace (prefixWord ++ tailWord_786505) baseStart_786505 baseEnd_786505 := by
    simpa [prefixWord, tailWord_786505, baseEnd_786505] using wordTrace_append hprefix tailTrace_786505
  have hstable : (prefixWord ++ tailWord_786505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786505).length < 2 ^ (prefixWord ++ tailWord_786505).sum := by decide
  have hdescent : baseEnd_786505 < baseStart_786505 := by decide
  rcases family_descends (prefixWord ++ tailWord_786505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786522 : List Nat := [3, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3]
def baseStart_786522 : Nat := 118140960795 + 786522 * 2 ^ 59
def prefixEnd_786522 : Nat := 4983230072969 + 3 ^ 40 * 786522 * 2
def baseEnd_786522 : Nat := 403863831335676962757857

theorem tailTrace_786522 : CollatzResearch.WordTrace tailWord_786522 prefixEnd_786522 403863831335676962757857 := by
  unfold tailWord_786522
  simp only [CollatzResearch.WordTrace]
  refine ⟨7171703514143149027092455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19124542704381730738913213 7171703514143149027092455)
  ·
    refine ⟨10757555271214723540638683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7171703514143149027092455 10757555271214723540638683)
    ·
      refine ⟨16136332906822085310958025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10757555271214723540638683 16136332906822085310958025)
      ·
        refine ⟨12102249680116563983218519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16136332906822085310958025 12102249680116563983218519)
        ·
          refine ⟨18153374520174845974827779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12102249680116563983218519 18153374520174845974827779)
          ·
            refine ⟨27230061780262268962241669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18153374520174845974827779 27230061780262268962241669)
            ·
              refine ⟨5105636583799175430420313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27230061780262268962241669 5105636583799175430420313)
              ·
                refine ⟨3829227437849381572815235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5105636583799175430420313 3829227437849381572815235)
                ·
                  refine ⟨5743841156774072359222853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3829227437849381572815235 5743841156774072359222853)
                  ·
                    refine ⟨1076970216895138567354285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5743841156774072359222853 1076970216895138567354285)
                    ·
                      refine ⟨403863831335676962757857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1076970216895138567354285 403863831335676962757857)
                      ·
                        rfl

theorem cell23_786522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_786522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786522 prefixEnd_786522 := by exact prefixLift 786522
  have htrace : WordTrace (prefixWord ++ tailWord_786522) baseStart_786522 baseEnd_786522 := by
    simpa [prefixWord, tailWord_786522, baseEnd_786522] using wordTrace_append hprefix tailTrace_786522
  have hstable : (prefixWord ++ tailWord_786522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786522).length < 2 ^ (prefixWord ++ tailWord_786522).sum := by decide
  have hdescent : baseEnd_786522 < baseStart_786522 := by decide
  rcases family_descends (prefixWord ++ tailWord_786522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786542 : List Nat := [4, 1, 2, 2, 1, 1, 2, 2, 8]
def baseStart_786542 : Nat := 118140960795 + 786542 * 2 ^ 59
def prefixEnd_786542 : Nat := 4983230072969 + 3 ^ 40 * 786542 * 2
def baseEnd_786542 : Nat := 44874900105418542723085

theorem tailTrace_786542 : CollatzResearch.WordTrace tailWord_786542 prefixEnd_786542 44874900105418542723085 := by
  unfold tailWord_786542
  simp only [CollatzResearch.WordTrace]
  refine ⟨3585942939562517440512235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19125029011000093016065253 3585942939562517440512235)
  ·
    refine ⟨5378914409343776160768353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3585942939562517440512235 5378914409343776160768353)
    ·
      refine ⟨4034185807007832120576265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5378914409343776160768353 4034185807007832120576265)
      ·
        refine ⟨3025639355255874090432199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4034185807007832120576265 3025639355255874090432199)
        ·
          refine ⟨4538459032883811135648299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3025639355255874090432199 4538459032883811135648299)
          ·
            refine ⟨6807688549325716703472449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4538459032883811135648299 6807688549325716703472449)
            ·
              refine ⟨5105766411994287527604337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6807688549325716703472449 5105766411994287527604337)
              ·
                refine ⟨3829324808995715645703253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5105766411994287527604337 3829324808995715645703253)
                ·
                  refine ⟨44874900105418542723085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3829324808995715645703253 44874900105418542723085)
                  ·
                    rfl

theorem cell23_786542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_786542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786542 prefixEnd_786542 := by exact prefixLift 786542
  have htrace : WordTrace (prefixWord ++ tailWord_786542) baseStart_786542 baseEnd_786542 := by
    simpa [prefixWord, tailWord_786542, baseEnd_786542] using wordTrace_append hprefix tailTrace_786542
  have hstable : (prefixWord ++ tailWord_786542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786542).length < 2 ^ (prefixWord ++ tailWord_786542).sum := by decide
  have hdescent : baseEnd_786542 < baseStart_786542 := by decide
  rcases family_descends (prefixWord ++ tailWord_786542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786546 : List Nat := [3, 2, 1, 2, 2, 2, 1, 5, 1, 4]
def baseStart_786546 : Nat := 118140960795 + 786546 * 2 ^ 59
def prefixEnd_786546 : Nat := 4983230072969 + 3 ^ 40 * 786546 * 2
def baseEnd_786546 : Nat := 134625384957128289619249

theorem tailTrace_786546 : CollatzResearch.WordTrace tailWord_786546 prefixEnd_786546 134625384957128289619249 := by
  unfold tailWord_786546
  simp only [CollatzResearch.WordTrace]
  refine ⟨7171922352121412051810873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19125126272323765471495661 7171922352121412051810873)
  ·
    refine ⟨5378941764091059038858155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7171922352121412051810873 5378941764091059038858155)
    ·
      refine ⟨8068412646136588558287233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5378941764091059038858155 8068412646136588558287233)
      ·
        refine ⟨6051309484602441418715425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8068412646136588558287233 6051309484602441418715425)
        ·
          refine ⟨4538482113451831064036569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6051309484602441418715425 4538482113451831064036569)
          ·
            refine ⟨3403861585088873298027427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4538482113451831064036569 3403861585088873298027427)
            ·
              refine ⟨5105792377633309947041141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3403861585088873298027427 5105792377633309947041141)
              ·
                refine ⟨478668035403122807535107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5105792377633309947041141 478668035403122807535107)
                ·
                  refine ⟨718002053104684211302661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 478668035403122807535107 718002053104684211302661)
                  ·
                    refine ⟨134625384957128289619249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 718002053104684211302661 134625384957128289619249)
                    ·
                      rfl

theorem cell23_786546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_786546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786546 prefixEnd_786546 := by exact prefixLift 786546
  have htrace : WordTrace (prefixWord ++ tailWord_786546) baseStart_786546 baseEnd_786546 := by
    simpa [prefixWord, tailWord_786546, baseEnd_786546] using wordTrace_append hprefix tailTrace_786546
  have hstable : (prefixWord ++ tailWord_786546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786546).length < 2 ^ (prefixWord ++ tailWord_786546).sum := by decide
  have hdescent : baseEnd_786546 < baseStart_786546 := by decide
  rcases family_descends (prefixWord ++ tailWord_786546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786589 : List Nat := [1, 4, 2, 1, 1, 3, 1, 4, 1, 5]
def baseStart_786589 : Nat := 118140960795 + 786589 * 2 ^ 59
def prefixEnd_786589 : Nat := 4983230072969 + 3 ^ 40 * 786589 * 2
def baseEnd_786589 : Nat := 134632744846509400206683

theorem tailTrace_786589 : CollatzResearch.WordTrace tailWord_786589 prefixEnd_786589 134632744846509400206683 := by
  unfold tailWord_786589
  simp only [CollatzResearch.WordTrace]
  refine ⟨28689257747329866551058821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19126171831553244367372547 28689257747329866551058821)
  ·
    refine ⟨5379235827624349978323529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28689257747329866551058821 5379235827624349978323529)
    ·
      refine ⟨4034426870718262483742647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5379235827624349978323529 4034426870718262483742647)
      ·
        refine ⟨6051640306077393725613971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4034426870718262483742647 6051640306077393725613971)
        ·
          refine ⟨9077460459116090588420957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6051640306077393725613971 9077460459116090588420957)
          ·
            refine ⟨3404047672168533970657859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9077460459116090588420957 3404047672168533970657859)
            ·
              refine ⟨5106071508252800955986789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3404047672168533970657859 5106071508252800955986789)
              ·
                refine ⟨957388407797400179247523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5106071508252800955986789 957388407797400179247523)
                ·
                  refine ⟨1436082611696100268871285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 957388407797400179247523 1436082611696100268871285)
                  ·
                    refine ⟨134632744846509400206683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1436082611696100268871285 134632744846509400206683)
                    ·
                      rfl

theorem cell23_786589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_786589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786589 prefixEnd_786589 := by exact prefixLift 786589
  have htrace : WordTrace (prefixWord ++ tailWord_786589) baseStart_786589 baseEnd_786589 := by
    simpa [prefixWord, tailWord_786589, baseEnd_786589] using wordTrace_append hprefix tailTrace_786589
  have hstable : (prefixWord ++ tailWord_786589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786589).length < 2 ^ (prefixWord ++ tailWord_786589).sum := by decide
  have hdescent : baseEnd_786589 < baseStart_786589 := by decide
  rcases family_descends (prefixWord ++ tailWord_786589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786619 : List Nat := [1, 1, 1, 1, 1, 2, 6, 4, 2, 4]
def baseStart_786619 : Nat := 118140960795 + 786619 * 2 ^ 59
def prefixEnd_786619 : Nat := 4983230072969 + 3 ^ 40 * 786619 * 2
def baseEnd_786619 : Nat := 134637879653054361081637

theorem tailTrace_786619 : CollatzResearch.WordTrace tailWord_786619 prefixEnd_786619 134637879653054361081637 := by
  unfold tailWord_786619
  simp only [CollatzResearch.WordTrace]
  refine ⟨28690351937221181674650911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19126901291480787783100607 28690351937221181674650911)
  ·
    refine ⟨43035527905831772511976367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28690351937221181674650911 43035527905831772511976367)
    ·
      refine ⟨64553291858747658767964551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43035527905831772511976367 64553291858747658767964551)
      ·
        refine ⟨96829937788121488151946827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64553291858747658767964551 96829937788121488151946827)
        ·
          refine ⟨145244906682182232227920241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96829937788121488151946827 145244906682182232227920241)
          ·
            refine ⟨108933680011636674170940181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145244906682182232227920241 108933680011636674170940181)
            ·
              refine ⟨5106266250545469101762821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 108933680011636674170940181 5106266250545469101762821)
              ·
                refine ⟨957424921977275456580529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5106266250545469101762821 957424921977275456580529)
                ·
                  refine ⟨718068691482956592435397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 957424921977275456580529 718068691482956592435397)
                  ·
                    refine ⟨134637879653054361081637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 718068691482956592435397 134637879653054361081637)
                    ·
                      rfl

theorem cell23_786619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2, 4].length) (baseStart_786619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786619 prefixEnd_786619 := by exact prefixLift 786619
  have htrace : WordTrace (prefixWord ++ tailWord_786619) baseStart_786619 baseEnd_786619 := by
    simpa [prefixWord, tailWord_786619, baseEnd_786619] using wordTrace_append hprefix tailTrace_786619
  have hstable : (prefixWord ++ tailWord_786619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786619).length < 2 ^ (prefixWord ++ tailWord_786619).sum := by decide
  have hdescent : baseEnd_786619 < baseStart_786619 := by decide
  rcases family_descends (prefixWord ++ tailWord_786619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786620 : List Nat := [2, 2, 2, 3, 4, 1, 1, 1, 3, 1, 3]
def baseStart_786620 : Nat := 118140960795 + 786620 * 2 ^ 59
def prefixEnd_786620 : Nat := 4983230072969 + 3 ^ 40 * 786620 * 2
def baseEnd_786620 : Nat := 403914152439817579332407

theorem tailTrace_786620 : CollatzResearch.WordTrace tailWord_786620 prefixEnd_786620 403914152439817579332407 := by
  unfold tailWord_786620
  simp only [CollatzResearch.WordTrace]
  refine ⟨14345194205108779422718657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19126925606811705896958209 14345194205108779422718657)
  ·
    refine ⟨10758895653831584567038993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14345194205108779422718657 10758895653831584567038993)
    ·
      refine ⟨8069171740373688425279245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10758895653831584567038993 8069171740373688425279245)
      ·
        refine ⟨3025939402640133159479717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8069171740373688425279245 3025939402640133159479717)
        ·
          refine ⟨567363637995024967402447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3025939402640133159479717 567363637995024967402447)
          ·
            refine ⟨851045456992537451103671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567363637995024967402447 851045456992537451103671)
            ·
              refine ⟨1276568185488806176655507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851045456992537451103671 1276568185488806176655507)
              ·
                refine ⟨1914852278233209264983261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1276568185488806176655507 1914852278233209264983261)
                ·
                  refine ⟨718069604337453474368723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1914852278233209264983261 718069604337453474368723)
                  ·
                    refine ⟨1077104406506180211553085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 718069604337453474368723 1077104406506180211553085)
                    ·
                      refine ⟨403914152439817579332407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1077104406506180211553085 403914152439817579332407)
                      ·
                        rfl

theorem cell23_786620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_786620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786620 prefixEnd_786620 := by exact prefixLift 786620
  have htrace : WordTrace (prefixWord ++ tailWord_786620) baseStart_786620 baseEnd_786620 := by
    simpa [prefixWord, tailWord_786620, baseEnd_786620] using wordTrace_append hprefix tailTrace_786620
  have hstable : (prefixWord ++ tailWord_786620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786620).length < 2 ^ (prefixWord ++ tailWord_786620).sum := by decide
  have hdescent : baseEnd_786620 < baseStart_786620 := by decide
  rcases family_descends (prefixWord ++ tailWord_786620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786672 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 5]
def baseStart_786672 : Nat := 118140960795 + 786672 * 2 ^ 59
def prefixEnd_786672 : Nat := 4983230072969 + 3 ^ 40 * 786672 * 2
def baseEnd_786672 : Nat := 403940853433851375882167

theorem tailTrace_786672 : CollatzResearch.WordTrace tailWord_786672 prefixEnd_786672 403940853433851375882167 := by
  unfold tailWord_786672
  simp only [CollatzResearch.WordTrace]
  refine ⟨14346142503014585863165135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19128190004019447817553513 14346142503014585863165135)
  ·
    refine ⟨21519213754521878794747703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14346142503014585863165135 21519213754521878794747703)
    ·
      refine ⟨32278820631782818192121555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21519213754521878794747703 32278820631782818192121555)
      ·
        refine ⟨48418230947674227288182333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32278820631782818192121555 48418230947674227288182333)
        ·
          refine ⟨18156836605377835233068375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48418230947674227288182333 18156836605377835233068375)
          ·
            refine ⟨27235254908066752849602563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18156836605377835233068375 27235254908066752849602563)
            ·
              refine ⟨40852882362100129274403845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27235254908066752849602563 40852882362100129274403845)
              ·
                refine ⟨7659915442893774238950721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40852882362100129274403845 7659915442893774238950721)
                ·
                  refine ⟨5744936582170330679213041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7659915442893774238950721 5744936582170330679213041)
                  ·
                    refine ⟨4308702436627748009409781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5744936582170330679213041 4308702436627748009409781)
                    ·
                      refine ⟨403940853433851375882167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4308702436627748009409781 403940853433851375882167)
                      ·
                        rfl

theorem cell23_786672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 5].length) (baseStart_786672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786672 prefixEnd_786672 := by exact prefixLift 786672
  have htrace : WordTrace (prefixWord ++ tailWord_786672) baseStart_786672 baseEnd_786672 := by
    simpa [prefixWord, tailWord_786672, baseEnd_786672] using wordTrace_append hprefix tailTrace_786672
  have hstable : (prefixWord ++ tailWord_786672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786672).length < 2 ^ (prefixWord ++ tailWord_786672).sum := by decide
  have hdescent : baseEnd_786672 < baseStart_786672 := by decide
  rcases family_descends (prefixWord ++ tailWord_786672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786720 : List Nat := [2, 1, 1, 5, 2, 1, 4, 1, 1, 3, 2]
def baseStart_786720 : Nat := 118140960795 + 786720 * 2 ^ 59
def prefixEnd_786720 : Nat := 4983230072969 + 3 ^ 40 * 786720 * 2
def baseEnd_786720 : Nat := 403965500505267188081947

theorem tailTrace_786720 : CollatzResearch.WordTrace tailWord_786720 prefixEnd_786720 403965500505267188081947 := by
  unfold tailWord_786720
  simp only [CollatzResearch.WordTrace]
  refine ⟨14347017854927637962038807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19129357139903517282718409 14347017854927637962038807)
  ·
    refine ⟨21520526782391456943058211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14347017854927637962038807 21520526782391456943058211)
    ·
      refine ⟨32280790173587185414587317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21520526782391456943058211 32280790173587185414587317)
      ·
        refine ⟨3026324078773798632617561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32280790173587185414587317 3026324078773798632617561)
        ·
          refine ⟨2269743059080348974463171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3026324078773798632617561 2269743059080348974463171)
          ·
            refine ⟨3404614588620523461694757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2269743059080348974463171 3404614588620523461694757)
            ·
              refine ⟨638365235366348149067767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3404614588620523461694757 638365235366348149067767)
              ·
                refine ⟨957547853049522223601651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 638365235366348149067767 957547853049522223601651)
                ·
                  refine ⟨1436321779574283335402477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 957547853049522223601651 1436321779574283335402477)
                  ·
                    refine ⟨538620667340356250775929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1436321779574283335402477 538620667340356250775929)
                    ·
                      refine ⟨403965500505267188081947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 538620667340356250775929 403965500505267188081947)
                      ·
                        rfl

theorem cell23_786720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_786720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786720 prefixEnd_786720 := by exact prefixLift 786720
  have htrace : WordTrace (prefixWord ++ tailWord_786720) baseStart_786720 baseEnd_786720 := by
    simpa [prefixWord, tailWord_786720, baseEnd_786720] using wordTrace_append hprefix tailTrace_786720
  have hstable : (prefixWord ++ tailWord_786720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786720).length < 2 ^ (prefixWord ++ tailWord_786720).sum := by decide
  have hdescent : baseEnd_786720 < baseStart_786720 := by decide
  rcases family_descends (prefixWord ++ tailWord_786720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786727 : List Nat := [1, 1, 8, 1, 1, 1, 1, 1, 4, 1, 3]
def baseStart_786727 : Nat := 118140960795 + 786727 * 2 ^ 59
def prefixEnd_786727 : Nat := 4983230072969 + 3 ^ 40 * 786727 * 2
def baseEnd_786727 : Nat := 403969094869848660694415

theorem tailTrace_786727 : CollatzResearch.WordTrace tailWord_786727 prefixEnd_786727 403969094869848660694415 := by
  unfold tailWord_786727
  simp only [CollatzResearch.WordTrace]
  refine ⟨28694291020829916119582435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19129527347219944079721623 28694291020829916119582435)
  ·
    refine ⟨43041436531244874179373653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28694291020829916119582435 43041436531244874179373653)
    ·
      refine ⟨504391834350525869289535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 43041436531244874179373653 504391834350525869289535)
      ·
        refine ⟨756587751525788803934303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504391834350525869289535 756587751525788803934303)
        ·
          refine ⟨1134881627288683205901455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 756587751525788803934303 1134881627288683205901455)
          ·
            refine ⟨1702322440933024808852183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1134881627288683205901455 1702322440933024808852183)
            ·
              refine ⟨2553483661399537213278275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1702322440933024808852183 2553483661399537213278275)
              ·
                refine ⟨3830225492099305819917413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2553483661399537213278275 3830225492099305819917413)
                ·
                  refine ⟨718167279768619841234515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3830225492099305819917413 718167279768619841234515)
                  ·
                    refine ⟨1077250919652929761851773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 718167279768619841234515 1077250919652929761851773)
                    ·
                      refine ⟨403969094869848660694415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1077250919652929761851773 403969094869848660694415)
                      ·
                        rfl

theorem cell23_786727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_786727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786727 prefixEnd_786727 := by exact prefixLift 786727
  have htrace : WordTrace (prefixWord ++ tailWord_786727) baseStart_786727 baseEnd_786727 := by
    simpa [prefixWord, tailWord_786727, baseEnd_786727] using wordTrace_append hprefix tailTrace_786727
  have hstable : (prefixWord ++ tailWord_786727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786727).length < 2 ^ (prefixWord ++ tailWord_786727).sum := by decide
  have hdescent : baseEnd_786727 < baseStart_786727 := by decide
  rcases family_descends (prefixWord ++ tailWord_786727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786739 : List Nat := [1, 1, 1, 2, 5, 1, 4, 1, 7]
def baseStart_786739 : Nat := 118140960795 + 786739 * 2 ^ 59
def prefixEnd_786739 : Nat := 4983230072969 + 3 ^ 40 * 786739 * 2
def baseEnd_786739 : Nat := 44886139626411401527151

theorem tailTrace_786739 : CollatzResearch.WordTrace tailWord_786739 prefixEnd_786739 44886139626411401527151 := by
  unfold tailWord_786739
  simp only [CollatzResearch.WordTrace]
  refine ⟨28694728696786442169019271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19129819131190961446012847 28694728696786442169019271)
  ·
    refine ⟨43042093045179663253528907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28694728696786442169019271 43042093045179663253528907)
    ·
      refine ⟨64563139567769494880293361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43042093045179663253528907 64563139567769494880293361)
      ·
        refine ⟨48422354675827121160220021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64563139567769494880293361 48422354675827121160220021)
        ·
          refine ⟨4539595750858792608770627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48422354675827121160220021 4539595750858792608770627)
          ·
            refine ⟨6809393626288188913155941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4539595750858792608770627 6809393626288188913155941)
            ·
              refine ⟨1276761304929035421216739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6809393626288188913155941 1276761304929035421216739)
              ·
                refine ⟨1915141957393553131825109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1276761304929035421216739 1915141957393553131825109)
                ·
                  refine ⟨44886139626411401527151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1915141957393553131825109 44886139626411401527151)
                  ·
                    rfl

theorem cell23_786739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 7].length) (baseStart_786739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786739 prefixEnd_786739 := by exact prefixLift 786739
  have htrace : WordTrace (prefixWord ++ tailWord_786739) baseStart_786739 baseEnd_786739 := by
    simpa [prefixWord, tailWord_786739, baseEnd_786739] using wordTrace_append hprefix tailTrace_786739
  have hstable : (prefixWord ++ tailWord_786739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786739).length < 2 ^ (prefixWord ++ tailWord_786739).sum := by decide
  have hdescent : baseEnd_786739 < baseStart_786739 := by decide
  rcases family_descends (prefixWord ++ tailWord_786739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786750 : List Nat := [4, 2, 1, 2, 1, 4, 1, 1, 1, 4, 2]
def baseStart_786750 : Nat := 118140960795 + 786750 * 2 ^ 59
def prefixEnd_786750 : Nat := 4983230072969 + 3 ^ 40 * 786750 * 2
def baseEnd_786750 : Nat := 403980904924902070706809

theorem tailTrace_786750 : CollatzResearch.WordTrace tailWord_786750 prefixEnd_786750 403980904924902070706809 := by
  unfold tailWord_786750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3586891237468323880958713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19130086599831060698446469 3586891237468323880958713)
  ·
    refine ⟨2690168428101242910719035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3586891237468323880958713 2690168428101242910719035)
    ·
      refine ⟨4035252642151864366078553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2690168428101242910719035 4035252642151864366078553)
      ·
        refine ⟨3026439481613898274558915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4035252642151864366078553 3026439481613898274558915)
        ·
          refine ⟨4539659222420847411838373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3026439481613898274558915 4539659222420847411838373)
          ·
            refine ⟨851186104203908889719695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4539659222420847411838373 851186104203908889719695)
            ·
              refine ⟨1276779156305863334579543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851186104203908889719695 1276779156305863334579543)
              ·
                refine ⟨1915168734458795001869315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1276779156305863334579543 1915168734458795001869315)
                ·
                  refine ⟨2872753101688192502803973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1915168734458795001869315 2872753101688192502803973)
                  ·
                    refine ⟨538641206566536094275745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2872753101688192502803973 538641206566536094275745)
                    ·
                      refine ⟨403980904924902070706809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 538641206566536094275745 403980904924902070706809)
                      ·
                        rfl

theorem cell23_786750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_786750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786750 prefixEnd_786750 := by exact prefixLift 786750
  have htrace : WordTrace (prefixWord ++ tailWord_786750) baseStart_786750 baseEnd_786750 := by
    simpa [prefixWord, tailWord_786750, baseEnd_786750] using wordTrace_append hprefix tailTrace_786750
  have hstable : (prefixWord ++ tailWord_786750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786750).length < 2 ^ (prefixWord ++ tailWord_786750).sum := by decide
  have hdescent : baseEnd_786750 < baseStart_786750 := by decide
  rcases family_descends (prefixWord ++ tailWord_786750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786769 : List Nat := [1, 2, 2, 1, 4, 2, 2, 1, 1, 7]
def baseStart_786769 : Nat := 118140960795 + 786769 * 2 ^ 59
def prefixEnd_786769 : Nat := 4983230072969 + 3 ^ 40 * 786769 * 2
def baseEnd_786769 : Nat := 134663553685779165456407

theorem tailTrace_786769 : CollatzResearch.WordTrace tailWord_786769 prefixEnd_786769 134663553685779165456407 := by
  unfold tailWord_786769
  simp only [CollatzResearch.WordTrace]
  refine ⟨28695822886677757292611361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19130548591118504861740907 28695822886677757292611361)
  ·
    refine ⟨21521867165008317969458521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28695822886677757292611361 21521867165008317969458521)
    ·
      refine ⟨16141400373756238477093891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21521867165008317969458521 16141400373756238477093891)
      ·
        refine ⟨24212100560634357715640837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16141400373756238477093891 24212100560634357715640837)
        ·
          refine ⟨4539768855118942071682657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24212100560634357715640837 4539768855118942071682657)
          ·
            refine ⟨3404826641339206553761993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4539768855118942071682657 3404826641339206553761993)
            ·
              refine ⟨2553619981004404915321495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3404826641339206553761993 2553619981004404915321495)
              ·
                refine ⟨3830429971506607372982243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2553619981004404915321495 3830429971506607372982243)
                ·
                  refine ⟨5745644957259911059473365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3830429971506607372982243 5745644957259911059473365)
                  ·
                    refine ⟨134663553685779165456407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5745644957259911059473365 134663553685779165456407)
                    ·
                      rfl

theorem cell23_786769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 7].length) (baseStart_786769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786769 prefixEnd_786769 := by exact prefixLift 786769
  have htrace : WordTrace (prefixWord ++ tailWord_786769) baseStart_786769 baseEnd_786769 := by
    simpa [prefixWord, tailWord_786769, baseEnd_786769] using wordTrace_append hprefix tailTrace_786769
  have hstable : (prefixWord ++ tailWord_786769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786769).length < 2 ^ (prefixWord ++ tailWord_786769).sum := by decide
  have hdescent : baseEnd_786769 < baseStart_786769 := by decide
  rcases family_descends (prefixWord ++ tailWord_786769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786786 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 4, 5]
def baseStart_786786 : Nat := 118140960795 + 786786 * 2 ^ 59
def prefixEnd_786786 : Nat := 4983230072969 + 3 ^ 40 * 786786 * 2
def baseEnd_786786 : Nat := 134666463409487976618881

theorem tailTrace_786786 : CollatzResearch.WordTrace tailWord_786786 prefixEnd_786786 134666463409487976618881 := by
  unfold tailWord_786786
  simp only [CollatzResearch.WordTrace]
  refine ⟨7174110731904042298995053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19130961951744112797320141 7174110731904042298995053)
  ·
    refine ⟨2690291524464015862123145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7174110731904042298995053 2690291524464015862123145)
    ·
      refine ⟨2017718643348011896592359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2690291524464015862123145 2017718643348011896592359)
      ·
        refine ⟨3026577965022017844888539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2017718643348011896592359 3026577965022017844888539)
        ·
          refine ⟨4539866947533026767332809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3026577965022017844888539 4539866947533026767332809)
          ·
            refine ⟨3404900210649770075499607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4539866947533026767332809 3404900210649770075499607)
            ·
              refine ⟨5107350315974655113249411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3404900210649770075499607 5107350315974655113249411)
              ·
                refine ⟨7661025473961982669874117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5107350315974655113249411 7661025473961982669874117)
                ·
                  refine ⟨1436442276367871750601397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7661025473961982669874117 1436442276367871750601397)
                  ·
                    refine ⟨134666463409487976618881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1436442276367871750601397 134666463409487976618881)
                    ·
                      rfl

theorem cell23_786786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_786786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786786 prefixEnd_786786 := by exact prefixLift 786786
  have htrace : WordTrace (prefixWord ++ tailWord_786786) baseStart_786786 baseEnd_786786 := by
    simpa [prefixWord, tailWord_786786, baseEnd_786786] using wordTrace_append hprefix tailTrace_786786
  have hstable : (prefixWord ++ tailWord_786786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786786).length < 2 ^ (prefixWord ++ tailWord_786786).sum := by decide
  have hdescent : baseEnd_786786 < baseStart_786786 := by decide
  rcases family_descends (prefixWord ++ tailWord_786786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786796 : List Nat := [2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 5]
def baseStart_786796 : Nat := 118140960795 + 786796 * 2 ^ 59
def prefixEnd_786796 : Nat := 4983230072969 + 3 ^ 40 * 786796 * 2
def baseEnd_786796 : Nat := 404004525035008890731597

theorem tailTrace_786796 : CollatzResearch.WordTrace tailWord_786796 prefixEnd_786796 404004525035008890731597 := by
  unfold tailWord_786796
  simp only [CollatzResearch.WordTrace]
  refine ⟨14348403828789970451922121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19131205105053293935896161 14348403828789970451922121)
  ·
    refine ⟨10761302871592477838941591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14348403828789970451922121 10761302871592477838941591)
    ·
      refine ⟨16141954307388716758412387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10761302871592477838941591 16141954307388716758412387)
      ·
        refine ⟨24212931461083075137618581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16141954307388716758412387 24212931461083075137618581)
        ·
          refine ⟨1134981162238269147075871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24212931461083075137618581 1134981162238269147075871)
          ·
            refine ⟨1702471743357403720613807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1134981162238269147075871 1702471743357403720613807)
            ·
              refine ⟨2553707615036105580920711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1702471743357403720613807 2553707615036105580920711)
              ·
                refine ⟨3830561422554158371381067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2553707615036105580920711 3830561422554158371381067)
                ·
                  refine ⟨5745842133831237557071601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3830561422554158371381067 5745842133831237557071601)
                  ·
                    refine ⟨4309381600373428167803701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5745842133831237557071601 4309381600373428167803701)
                    ·
                      refine ⟨404004525035008890731597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4309381600373428167803701 404004525035008890731597)
                      ·
                        rfl

theorem cell23_786796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 5].length) (baseStart_786796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786796 prefixEnd_786796 := by exact prefixLift 786796
  have htrace : WordTrace (prefixWord ++ tailWord_786796) baseStart_786796 baseEnd_786796 := by
    simpa [prefixWord, tailWord_786796, baseEnd_786796] using wordTrace_append hprefix tailTrace_786796
  have hstable : (prefixWord ++ tailWord_786796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786796).length < 2 ^ (prefixWord ++ tailWord_786796).sum := by decide
  have hdescent : baseEnd_786796 < baseStart_786796 := by decide
  rcases family_descends (prefixWord ++ tailWord_786796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786850 : List Nat := [3, 3, 1, 2, 1, 1, 3, 4, 1, 4]
def baseStart_786850 : Nat := 118140960795 + 786850 * 2 ^ 59
def prefixEnd_786850 : Nat := 4983230072969 + 3 ^ 40 * 786850 * 2
def baseEnd_786850 : Nat := 134677417663450559818783

theorem tailTrace_786850 : CollatzResearch.WordTrace tailWord_786850 prefixEnd_786850 134677417663450559818783 := by
  unfold tailWord_786850
  simp only [CollatzResearch.WordTrace]
  refine ⟨7174694299846077031577501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19132518132922872084206669 7174694299846077031577501)
  ·
    refine ⟨2690510362442278886841563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7174694299846077031577501 2690510362442278886841563)
    ·
      refine ⟨4035765543663418330262345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2690510362442278886841563 4035765543663418330262345)
      ·
        refine ⟨3026824157747563747696759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4035765543663418330262345 3026824157747563747696759)
        ·
          refine ⟨4540236236621345621545139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3026824157747563747696759 4540236236621345621545139)
          ·
            refine ⟨6810354354932018432317709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4540236236621345621545139 6810354354932018432317709)
            ·
              refine ⟨2553882883099506912119141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6810354354932018432317709 2553882883099506912119141)
              ·
                refine ⟨478853040581157546022339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2553882883099506912119141 478853040581157546022339)
                ·
                  refine ⟨718279560871736319033509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 478853040581157546022339 718279560871736319033509)
                  ·
                    refine ⟨134677417663450559818783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 718279560871736319033509 134677417663450559818783)
                    ·
                      rfl

theorem cell23_786850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_786850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786850 prefixEnd_786850 := by exact prefixLift 786850
  have htrace : WordTrace (prefixWord ++ tailWord_786850) baseStart_786850 baseEnd_786850 := by
    simpa [prefixWord, tailWord_786850, baseEnd_786850] using wordTrace_append hprefix tailTrace_786850
  have hstable : (prefixWord ++ tailWord_786850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786850).length < 2 ^ (prefixWord ++ tailWord_786850).sum := by decide
  have hdescent : baseEnd_786850 < baseStart_786850 := by decide
  rcases family_descends (prefixWord ++ tailWord_786850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786873 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 5, 1, 3]
def baseStart_786873 : Nat := 118140960795 + 786873 * 2 ^ 59
def prefixEnd_786873 : Nat := 4983230072969 + 3 ^ 40 * 786873 * 2
def baseEnd_786873 : Nat := 404044063045405089468743

theorem tailTrace_786873 : CollatzResearch.WordTrace tailWord_786873 prefixEnd_786873 404044063045405089468743 := by
  unfold tailWord_786873
  simp only [CollatzResearch.WordTrace]
  refine ⟨28699616078300983054397273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19133077385533988702931515 28699616078300983054397273)
  ·
    refine ⟨21524712058725737290797955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28699616078300983054397273 21524712058725737290797955)
    ·
      refine ⟨32287068088088605936196933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21524712058725737290797955 32287068088088605936196933)
      ·
        refine ⟨6053825266516613613036925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32287068088088605936196933 6053825266516613613036925)
        ·
          refine ⟨2270184474943730104888847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6053825266516613613036925 2270184474943730104888847)
          ·
            refine ⟨3405276712415595157333271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2270184474943730104888847 3405276712415595157333271)
            ·
              refine ⟨5107915068623392735999907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3405276712415595157333271 5107915068623392735999907)
              ·
                refine ⟨7661872602935089103999861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5107915068623392735999907 7661872602935089103999861)
                ·
                  refine ⟨718300556525164603499987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7661872602935089103999861 718300556525164603499987)
                  ·
                    refine ⟨1077450834787746905249981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 718300556525164603499987 1077450834787746905249981)
                    ·
                      refine ⟨404044063045405089468743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1077450834787746905249981 404044063045405089468743)
                      ·
                        rfl

theorem cell23_786873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_786873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786873 prefixEnd_786873 := by exact prefixLift 786873
  have htrace : WordTrace (prefixWord ++ tailWord_786873) baseStart_786873 baseEnd_786873 := by
    simpa [prefixWord, tailWord_786873, baseEnd_786873] using wordTrace_append hprefix tailTrace_786873
  have hstable : (prefixWord ++ tailWord_786873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786873).length < 2 ^ (prefixWord ++ tailWord_786873).sum := by decide
  have hdescent : baseEnd_786873 < baseStart_786873 := by decide
  rcases family_descends (prefixWord ++ tailWord_786873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786957 : List Nat := [1, 7, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_786957 : Nat := 118140960795 + 786957 * 2 ^ 59
def prefixEnd_786957 : Nat := 4983230072969 + 3 ^ 40 * 786957 * 2
def baseEnd_786957 : Nat := 134695731806794253606119

theorem tailTrace_786957 : CollatzResearch.WordTrace tailWord_786957 prefixEnd_786957 134695731806794253606119 := by
  unfold tailWord_786957
  simp only [CollatzResearch.WordTrace]
  refine ⟨28702679809996665400455125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19135119873331110266970083 28702679809996665400455125)
  ·
    refine ⟨672719058046796845323167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 28702679809996665400455125 672719058046796845323167)
    ·
      refine ⟨1009078587070195267984751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 672719058046796845323167 1009078587070195267984751)
      ·
        refine ⟨1513617880605292901977127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1009078587070195267984751 1513617880605292901977127)
        ·
          refine ⟨2270426820907939352965691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1513617880605292901977127 2270426820907939352965691)
          ·
            refine ⟨3405640231361909029448537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2270426820907939352965691 3405640231361909029448537)
            ·
              refine ⟨2554230173521431772086403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3405640231361909029448537 2554230173521431772086403)
              ·
                refine ⟨3831345260282147658129605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2554230173521431772086403 3831345260282147658129605)
                ·
                  refine ⟨718377236302902685899301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3831345260282147658129605 718377236302902685899301)
                  ·
                    refine ⟨134695731806794253606119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 718377236302902685899301 134695731806794253606119)
                    ·
                      rfl

theorem cell23_786957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_786957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786957 prefixEnd_786957 := by exact prefixLift 786957
  have htrace : WordTrace (prefixWord ++ tailWord_786957) baseStart_786957 baseEnd_786957 := by
    simpa [prefixWord, tailWord_786957, baseEnd_786957] using wordTrace_append hprefix tailTrace_786957
  have hstable : (prefixWord ++ tailWord_786957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786957).length < 2 ^ (prefixWord ++ tailWord_786957).sum := by decide
  have hdescent : baseEnd_786957 < baseStart_786957 := by decide
  rcases family_descends (prefixWord ++ tailWord_786957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786963 : List Nat := [1, 1, 1, 2, 1, 5, 1, 3, 4, 1, 3]
def baseStart_786963 : Nat := 118140960795 + 786963 * 2 ^ 59
def prefixEnd_786963 : Nat := 4983230072969 + 3 ^ 40 * 786963 * 2
def baseEnd_786963 : Nat := 404090276304309737343329

theorem tailTrace_786963 : CollatzResearch.WordTrace tailWord_786963 prefixEnd_786963 404090276304309737343329 := by
  unfold tailWord_786963
  simp only [CollatzResearch.WordTrace]
  refine ⟨28702898647974928425173543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19135265765316618950115695 28702898647974928425173543)
  ·
    refine ⟨43054347971962392637760315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28702898647974928425173543 43054347971962392637760315)
    ·
      refine ⟨64581521957943588956640473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43054347971962392637760315 64581521957943588956640473)
      ·
        refine ⟨48436141468457691717480355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64581521957943588956640473 48436141468457691717480355)
        ·
          refine ⟨72654212202686537576220533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48436141468457691717480355 72654212202686537576220533)
          ·
            refine ⟨6811332394001862897770675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72654212202686537576220533 6811332394001862897770675)
            ·
              refine ⟨10216998591002794346656013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6811332394001862897770675 10216998591002794346656013)
              ·
                refine ⟨3831374471626047879996005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10216998591002794346656013 3831374471626047879996005)
                ·
                  refine ⟨718382713429883977499251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3831374471626047879996005 718382713429883977499251)
                  ·
                    refine ⟨1077574070144825966248877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 718382713429883977499251 1077574070144825966248877)
                    ·
                      refine ⟨404090276304309737343329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1077574070144825966248877 404090276304309737343329)
                      ·
                        rfl

theorem cell23_786963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 1, 3].length) (baseStart_786963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786963 prefixEnd_786963 := by exact prefixLift 786963
  have htrace : WordTrace (prefixWord ++ tailWord_786963) baseStart_786963 baseEnd_786963 := by
    simpa [prefixWord, tailWord_786963, baseEnd_786963] using wordTrace_append hprefix tailTrace_786963
  have hstable : (prefixWord ++ tailWord_786963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786963).length < 2 ^ (prefixWord ++ tailWord_786963).sum := by decide
  have hdescent : baseEnd_786963 < baseStart_786963 := by decide
  rcases family_descends (prefixWord ++ tailWord_786963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786964 : List Nat := [2, 4, 3, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_786964 : Nat := 118140960795 + 786964 * 2 ^ 59
def prefixEnd_786964 : Nat := 4983230072969 + 3 ^ 40 * 786964 * 2
def baseEnd_786964 : Nat := 404090789784964233430825

theorem tailTrace_786964 : CollatzResearch.WordTrace tailWord_786964 prefixEnd_786964 404090789784964233430825 := by
  unfold tailWord_786964
  simp only [CollatzResearch.WordTrace]
  refine ⟨14351467560485652797979973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19135290080647537063973297 14351467560485652797979973)
  ·
    refine ⟨2690900167591059899621245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14351467560485652797979973 2690900167591059899621245)
    ·
      refine ⟨1009087562846647462357967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2690900167591059899621245 1009087562846647462357967)
      ·
        refine ⟨1513631344269971193536951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1009087562846647462357967 1513631344269971193536951)
        ·
          refine ⟨2270447016404956790305427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1513631344269971193536951 2270447016404956790305427)
          ·
            refine ⟨3405670524607435185458141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2270447016404956790305427 3405670524607435185458141)
            ·
              refine ⟨1277126446727788194546803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3405670524607435185458141 1277126446727788194546803)
              ·
                refine ⟨1915689670091682291820205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1277126446727788194546803 1915689670091682291820205)
                ·
                  refine ⟨718383626284380859432577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1915689670091682291820205 718383626284380859432577)
                  ·
                    refine ⟨538787719713285644574433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 718383626284380859432577 538787719713285644574433)
                    ·
                      refine ⟨404090789784964233430825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 538787719713285644574433 404090789784964233430825)
                      ·
                        rfl

theorem cell23_786964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_786964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_786964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_786964 prefixEnd_786964 := by exact prefixLift 786964
  have htrace : WordTrace (prefixWord ++ tailWord_786964) baseStart_786964 baseEnd_786964 := by
    simpa [prefixWord, tailWord_786964, baseEnd_786964] using wordTrace_append hprefix tailTrace_786964
  have hstable : (prefixWord ++ tailWord_786964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786964).length < 2 ^ (prefixWord ++ tailWord_786964).sum := by decide
  have hdescent : baseEnd_786964 < baseStart_786964 := by decide
  rcases family_descends (prefixWord ++ tailWord_786964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787007 : List Nat := [1, 1, 2, 2, 3, 2, 5, 1, 1, 3, 2]
def baseStart_787007 : Nat := 118140960795 + 787007 * 2 ^ 59
def prefixEnd_787007 : Nat := 4983230072969 + 3 ^ 40 * 787007 * 2
def baseEnd_787007 : Nat := 404112869453107565193127

theorem tailTrace_787007 : CollatzResearch.WordTrace tailWord_787007 prefixEnd_787007 404112869453107565193127 := by
  unfold tailWord_787007
  simp only [CollatzResearch.WordTrace]
  refine ⟨28704503459815523939775275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19136335639877015959850183 28704503459815523939775275)
  ·
    refine ⟨43056755189723285909662913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28704503459815523939775275 43056755189723285909662913)
    ·
      refine ⟨32292566392292464432247185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43056755189723285909662913 32292566392292464432247185)
      ·
        refine ⟨24219424794219348324185389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32292566392292464432247185 24219424794219348324185389)
        ·
          refine ⟨9082284297832255621569521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24219424794219348324185389 9082284297832255621569521)
          ·
            refine ⟨6811713223374191716177141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9082284297832255621569521 6811713223374191716177141)
            ·
              refine ⟨638598114691330473391607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6811713223374191716177141 638598114691330473391607)
              ·
                refine ⟨957897172036995710087411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 638598114691330473391607 957897172036995710087411)
                ·
                  refine ⟨1436845758055493565131117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 957897172036995710087411 1436845758055493565131117)
                  ·
                    refine ⟨538817159270810086924169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1436845758055493565131117 538817159270810086924169)
                    ·
                      refine ⟨404112869453107565193127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 538817159270810086924169 404112869453107565193127)
                      ·
                        rfl

theorem cell23_787007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 1, 3, 2].length) (baseStart_787007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787007 prefixEnd_787007 := by exact prefixLift 787007
  have htrace : WordTrace (prefixWord ++ tailWord_787007) baseStart_787007 baseEnd_787007 := by
    simpa [prefixWord, tailWord_787007, baseEnd_787007] using wordTrace_append hprefix tailTrace_787007
  have hstable : (prefixWord ++ tailWord_787007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787007).length < 2 ^ (prefixWord ++ tailWord_787007).sum := by decide
  have hdescent : baseEnd_787007 < baseStart_787007 := by decide
  rcases family_descends (prefixWord ++ tailWord_787007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787014 : List Nat := [6, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_787014 : Nat := 118140960795 + 787014 * 2 ^ 59
def prefixEnd_787014 : Nat := 4983230072969 + 3 ^ 40 * 787014 * 2
def baseEnd_787014 : Nat := 404116463817689037805595

theorem tailTrace_787014 : CollatzResearch.WordTrace tailWord_787014 prefixEnd_787014 404116463817689037805595 := by
  unfold tailWord_787014
  simp only [CollatzResearch.WordTrace]
  refine ⟨897023711587192629227503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19136505847193442756853397 897023711587192629227503)
  ·
    refine ⟨1345535567380788943841255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 897023711587192629227503 1345535567380788943841255)
    ·
      refine ⟨2018303351071183415761883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1345535567380788943841255 2018303351071183415761883)
      ·
        refine ⟨3027455026606775123642825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2018303351071183415761883 3027455026606775123642825)
        ·
          refine ⟨2270591269955081342732119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3027455026606775123642825 2270591269955081342732119)
          ·
            refine ⟨3405886904932622014098179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2270591269955081342732119 3405886904932622014098179)
            ·
              refine ⟨5108830357398933021147269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3405886904932622014098179 5108830357398933021147269)
              ·
                refine ⟨957905692012299941465113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5108830357398933021147269 957905692012299941465113)
                ·
                  refine ⟨718429269009224956098835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 957905692012299941465113 718429269009224956098835)
                  ·
                    refine ⟨1077643903513837434148253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 718429269009224956098835 1077643903513837434148253)
                    ·
                      refine ⟨404116463817689037805595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1077643903513837434148253 404116463817689037805595)
                      ·
                        rfl

theorem cell23_787014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_787014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787014 prefixEnd_787014 := by exact prefixLift 787014
  have htrace : WordTrace (prefixWord ++ tailWord_787014) baseStart_787014 baseEnd_787014 := by
    simpa [prefixWord, tailWord_787014, baseEnd_787014] using wordTrace_append hprefix tailTrace_787014
  have hstable : (prefixWord ++ tailWord_787014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787014).length < 2 ^ (prefixWord ++ tailWord_787014).sum := by decide
  have hdescent : baseEnd_787014 < baseStart_787014 := by decide
  rcases family_descends (prefixWord ++ tailWord_787014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787016 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 3, 4, 4]
def baseStart_787016 : Nat := 118140960795 + 787016 * 2 ^ 59
def prefixEnd_787016 : Nat := 4983230072969 + 3 ^ 40 * 787016 * 2
def baseEnd_787016 : Nat := 404117490778998029980585

theorem tailTrace_787016 : CollatzResearch.WordTrace tailWord_787016 prefixEnd_787016 404117490778998029980585 := by
  unfold tailWord_787016
  simp only [CollatzResearch.WordTrace]
  refine ⟨14352415858391459238426451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19136554477855278984568601 14352415858391459238426451)
  ·
    refine ⟨21528623787587188857639677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14352415858391459238426451 21528623787587188857639677)
    ·
      refine ⟨8073233920345195821614879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21528623787587188857639677 8073233920345195821614879)
      ·
        refine ⟨12109850880517793732422319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8073233920345195821614879 12109850880517793732422319)
        ·
          refine ⟨18164776320776690598633479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12109850880517793732422319 18164776320776690598633479)
          ·
            refine ⟨27247164481165035897950219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18164776320776690598633479 27247164481165035897950219)
            ·
              refine ⟨40870746721747553846925329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27247164481165035897950219 40870746721747553846925329)
              ·
                refine ⟨30653060041310665385193997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40870746721747553846925329 30653060041310665385193997)
                ·
                  refine ⟨11494897515491499519447749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30653060041310665385193997 11494897515491499519447749)
                  ·
                    refine ⟨2155293284154656159896453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11494897515491499519447749 2155293284154656159896453)
                    ·
                      refine ⟨404117490778998029980585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2155293284154656159896453 404117490778998029980585)
                      ·
                        rfl

theorem cell23_787016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_787016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787016 prefixEnd_787016 := by exact prefixLift 787016
  have htrace : WordTrace (prefixWord ++ tailWord_787016) baseStart_787016 baseEnd_787016 := by
    simpa [prefixWord, tailWord_787016, baseEnd_787016] using wordTrace_append hprefix tailTrace_787016
  have hstable : (prefixWord ++ tailWord_787016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787016).length < 2 ^ (prefixWord ++ tailWord_787016).sum := by decide
  have hdescent : baseEnd_787016 < baseStart_787016 := by decide
  rcases family_descends (prefixWord ++ tailWord_787016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787073 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 4, 5]
def baseStart_787073 : Nat := 118140960795 + 787073 * 2 ^ 59
def prefixEnd_787073 : Nat := 4983230072969 + 3 ^ 40 * 787073 * 2
def baseEnd_787073 : Nat := 134715586392101435655941

theorem tailTrace_787073 : CollatzResearch.WordTrace tailWord_787073 prefixEnd_787073 134715586392101435655941 := by
  unfold tailWord_787073
  simp only [CollatzResearch.WordTrace]
  refine ⟨28706910677576417211677873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19137940451717611474451915 28706910677576417211677873)
  ·
    refine ⟨21530183008182312908758405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28706910677576417211677873 21530183008182312908758405)
    ·
      refine ⟨4036909314034183670392201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21530183008182312908758405 4036909314034183670392201)
      ·
        refine ⟨3027681985525637752794151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4036909314034183670392201 3027681985525637752794151)
        ·
          refine ⟨4541522978288456629191227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3027681985525637752794151 4541522978288456629191227)
          ·
            refine ⟨6812284467432684943786841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4541522978288456629191227 6812284467432684943786841)
            ·
              refine ⟨5109213350574513707840131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6812284467432684943786841 5109213350574513707840131)
              ·
                refine ⟨7663820025861770561760197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5109213350574513707840131 7663820025861770561760197)
                ·
                  refine ⟨1436966254849081980330037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7663820025861770561760197 1436966254849081980330037)
                  ·
                    refine ⟨134715586392101435655941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1436966254849081980330037 134715586392101435655941)
                    ·
                      rfl

theorem cell23_787073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_787073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787073 prefixEnd_787073 := by exact prefixLift 787073
  have htrace : WordTrace (prefixWord ++ tailWord_787073) baseStart_787073 baseEnd_787073 := by
    simpa [prefixWord, tailWord_787073, baseEnd_787073] using wordTrace_append hprefix tailTrace_787073
  have hstable : (prefixWord ++ tailWord_787073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787073).length < 2 ^ (prefixWord ++ tailWord_787073).sum := by decide
  have hdescent : baseEnd_787073 < baseStart_787073 := by decide
  rcases family_descends (prefixWord ++ tailWord_787073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787111 : List Nat := [1, 1, 6, 3, 2, 1, 1, 3, 5]
def baseStart_787111 : Nat := 118140960795 + 787111 * 2 ^ 59
def prefixEnd_787111 : Nat := 4983230072969 + 3 ^ 40 * 787111 * 2
def baseEnd_787111 : Nat := 44907363493463906476961

theorem tailTrace_787111 : CollatzResearch.WordTrace tailWord_787111 prefixEnd_787111 44907363493463906476961 := by
  unfold tailWord_787111
  simp only [CollatzResearch.WordTrace]
  refine ⟨28708296651438749701561187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19138864434292499801040791 28708296651438749701561187)
  ·
    refine ⟨43062444977158124552341781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28708296651438749701561187 43062444977158124552341781)
    ·
      refine ⟨2018552108304287088391021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43062444977158124552341781 2018552108304287088391021)
      ·
        refine ⟨756957040614107658146633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2018552108304287088391021 756957040614107658146633)
        ·
          refine ⟨567717780460580743609975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 756957040614107658146633 567717780460580743609975)
          ·
            refine ⟨851576670690871115414963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567717780460580743609975 851576670690871115414963)
            ·
              refine ⟨1277365006036306673122445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851576670690871115414963 1277365006036306673122445)
              ·
                refine ⟨479011877263615002420917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1277365006036306673122445 479011877263615002420917)
                ·
                  refine ⟨44907363493463906476961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 479011877263615002420917 44907363493463906476961)
                  ·
                    rfl

theorem cell23_787111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3, 5].length) (baseStart_787111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787111 prefixEnd_787111 := by exact prefixLift 787111
  have htrace : WordTrace (prefixWord ++ tailWord_787111) baseStart_787111 baseEnd_787111 := by
    simpa [prefixWord, tailWord_787111, baseEnd_787111] using wordTrace_append hprefix tailTrace_787111
  have hstable : (prefixWord ++ tailWord_787111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787111).length < 2 ^ (prefixWord ++ tailWord_787111).sum := by decide
  have hdescent : baseEnd_787111 < baseStart_787111 := by decide
  rcases family_descends (prefixWord ++ tailWord_787111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787130 : List Nat := [3, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3]
def baseStart_787130 : Nat := 118140960795 + 787130 * 2 ^ 59
def prefixEnd_787130 : Nat := 4983230072969 + 3 ^ 40 * 787130 * 2
def baseEnd_787130 : Nat := 404176027573610583955061

theorem tailTrace_787130 : CollatzResearch.WordTrace tailWord_787130 prefixEnd_787130 404176027573610583955061 := by
  unfold tailWord_787130
  simp only [CollatzResearch.WordTrace]
  refine ⟨7177247409592478986625711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19139326425579943964335229 7177247409592478986625711)
  ·
    refine ⟨10765871114388718479938567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7177247409592478986625711 10765871114388718479938567)
    ·
      refine ⟨16148806671583077719907851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10765871114388718479938567 16148806671583077719907851)
      ·
        refine ⟨24223210007374616579861777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16148806671583077719907851 24223210007374616579861777)
        ·
          refine ⟨18167407505530962434896333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24223210007374616579861777 18167407505530962434896333)
          ·
            refine ⟨6812777814574110913086125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18167407505530962434896333 6812777814574110913086125)
            ·
              refine ⟨2554791680465291592407297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6812777814574110913086125 2554791680465291592407297)
              ·
                refine ⟨1916093760348968694305473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2554791680465291592407297 1916093760348968694305473)
                ·
                  refine ⟨1437070320261726520729105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1916093760348968694305473 1437070320261726520729105)
                  ·
                    refine ⟨1077802740196294890546829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1437070320261726520729105 1077802740196294890546829)
                    ·
                      refine ⟨404176027573610583955061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1077802740196294890546829 404176027573610583955061)
                      ·
                        rfl

theorem cell23_787130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3].length) (baseStart_787130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787130 prefixEnd_787130 := by exact prefixLift 787130
  have htrace : WordTrace (prefixWord ++ tailWord_787130) baseStart_787130 baseEnd_787130 := by
    simpa [prefixWord, tailWord_787130, baseEnd_787130] using wordTrace_append hprefix tailTrace_787130
  have hstable : (prefixWord ++ tailWord_787130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787130).length < 2 ^ (prefixWord ++ tailWord_787130).sum := by decide
  have hdescent : baseEnd_787130 < baseStart_787130 := by decide
  rcases family_descends (prefixWord ++ tailWord_787130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787133 : List Nat := [1, 4, 1, 2, 1, 3, 2, 1, 8]
def baseStart_787133 : Nat := 118140960795 + 787133 * 2 ^ 59
def prefixEnd_787133 : Nat := 4983230072969 + 3 ^ 40 * 787133 * 2
def baseEnd_787133 : Nat := 44908618668397119135283

theorem tailTrace_787133 : CollatzResearch.WordTrace tailWord_787133 prefixEnd_787133 44908618668397119135283 := by
  unfold tailWord_787133
  simp only [CollatzResearch.WordTrace]
  refine ⟨28709099057359047458862053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19139399371572698305908035 28709099057359047458862053)
  ·
    refine ⟨5382956073254821398536635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28709099057359047458862053 5382956073254821398536635)
    ·
      refine ⟨8074434109882232097804953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5382956073254821398536635 8074434109882232097804953)
      ·
        refine ⟨6055825582411674073353715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8074434109882232097804953 6055825582411674073353715)
        ·
          refine ⟨9083738373617511110030573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6055825582411674073353715 9083738373617511110030573)
          ·
            refine ⟨3406401890106566666261465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9083738373617511110030573 3406401890106566666261465)
            ·
              refine ⟨2554801417579924999696099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3406401890106566666261465 2554801417579924999696099)
              ·
                refine ⟨3832202126369887499544149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2554801417579924999696099 3832202126369887499544149)
                ·
                  refine ⟨44908618668397119135283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3832202126369887499544149 44908618668397119135283)
                  ·
                    rfl

theorem cell23_787133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_787133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787133 prefixEnd_787133 := by exact prefixLift 787133
  have htrace : WordTrace (prefixWord ++ tailWord_787133) baseStart_787133 baseEnd_787133 := by
    simpa [prefixWord, tailWord_787133, baseEnd_787133] using wordTrace_append hprefix tailTrace_787133
  have hstable : (prefixWord ++ tailWord_787133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787133).length < 2 ^ (prefixWord ++ tailWord_787133).sum := by decide
  have hdescent : baseEnd_787133 < baseStart_787133 := by decide
  rcases family_descends (prefixWord ++ tailWord_787133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787143 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 2, 5, 3]
def baseStart_787143 : Nat := 118140960795 + 787143 * 2 ^ 59
def prefixEnd_787143 : Nat := 4983230072969 + 3 ^ 40 * 787143 * 2
def baseEnd_787143 : Nat := 404182702822119033092501

theorem tailTrace_787143 : CollatzResearch.WordTrace tailWord_787143 prefixEnd_787143 404182702822119033092501 := by
  unfold tailWord_787143
  simp only [CollatzResearch.WordTrace]
  refine ⟨28709463787322819166726083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19139642524881879444484055 28709463787322819166726083)
  ·
    refine ⟨43064195680984228750089125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28709463787322819166726083 43064195680984228750089125)
    ·
      refine ⟨8074536690184542890641711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43064195680984228750089125 8074536690184542890641711)
      ·
        refine ⟨12111805035276814335962567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8074536690184542890641711 12111805035276814335962567)
        ·
          refine ⟨18167707552915221503943851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12111805035276814335962567 18167707552915221503943851)
          ·
            refine ⟨27251561329372832255915777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18167707552915221503943851 27251561329372832255915777)
            ·
              refine ⟨20438670997029624191936833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27251561329372832255915777 20438670997029624191936833)
              ·
                refine ⟨15329003247772218143952625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20438670997029624191936833 15329003247772218143952625)
                ·
                  refine ⟨11496752435829163607964469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15329003247772218143952625 11496752435829163607964469)
                  ·
                    refine ⟨1077820540858984088246669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11496752435829163607964469 1077820540858984088246669)
                    ·
                      refine ⟨404182702822119033092501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1077820540858984088246669 404182702822119033092501)
                      ·
                        rfl

theorem cell23_787143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_787143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787143 prefixEnd_787143 := by exact prefixLift 787143
  have htrace : WordTrace (prefixWord ++ tailWord_787143) baseStart_787143 baseEnd_787143 := by
    simpa [prefixWord, tailWord_787143, baseEnd_787143] using wordTrace_append hprefix tailTrace_787143
  have hstable : (prefixWord ++ tailWord_787143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787143).length < 2 ^ (prefixWord ++ tailWord_787143).sum := by decide
  have hdescent : baseEnd_787143 < baseStart_787143 := by decide
  rcases family_descends (prefixWord ++ tailWord_787143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787150 : List Nat := [4, 1, 1, 1, 3, 3, 1, 3, 6]
def baseStart_787150 : Nat := 118140960795 + 787150 * 2 ^ 59
def prefixEnd_787150 : Nat := 4983230072969 + 3 ^ 40 * 787150 * 2
def baseEnd_787150 : Nat := 44909588576300056189441

theorem tailTrace_787150 : CollatzResearch.WordTrace tailWord_787150 prefixEnd_787150 44909588576300056189441 := by
  unfold tailWord_787150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3588714887287182420278863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19139812732198306241487269 3588714887287182420278863)
  ·
    refine ⟨5383072330930773630418295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3588714887287182420278863 5383072330930773630418295)
    ·
      refine ⟨8074608496396160445627443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5383072330930773630418295 8074608496396160445627443)
      ·
        refine ⟨12111912744594240668441165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8074608496396160445627443 12111912744594240668441165)
        ·
          refine ⟨4541967279222840250665437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12111912744594240668441165 4541967279222840250665437)
          ·
            refine ⟨1703237729708565093999539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4541967279222840250665437 1703237729708565093999539)
            ·
              refine ⟨2554856594562847640999309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1703237729708565093999539 2554856594562847640999309)
              ·
                refine ⟨958071222961067865374741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2554856594562847640999309 958071222961067865374741)
                ·
                  refine ⟨44909588576300056189441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 958071222961067865374741 44909588576300056189441)
                  ·
                    rfl

theorem cell23_787150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 6].length) (baseStart_787150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787150 prefixEnd_787150 := by exact prefixLift 787150
  have htrace : WordTrace (prefixWord ++ tailWord_787150) baseStart_787150 baseEnd_787150 := by
    simpa [prefixWord, tailWord_787150, baseEnd_787150] using wordTrace_append hprefix tailTrace_787150
  have hstable : (prefixWord ++ tailWord_787150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787150).length < 2 ^ (prefixWord ++ tailWord_787150).sum := by decide
  have hdescent : baseEnd_787150 < baseStart_787150 := by decide
  rcases family_descends (prefixWord ++ tailWord_787150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787164 : List Nat := [2, 2, 5, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_787164 : Nat := 118140960795 + 787164 * 2 ^ 59
def prefixEnd_787164 : Nat := 4983230072969 + 3 ^ 40 * 787164 * 2
def baseEnd_787164 : Nat := 404193485915863450929905

theorem tailTrace_787164 : CollatzResearch.WordTrace tailWord_787164 prefixEnd_787164 404193485915863450929905 := by
  unfold tailWord_787164
  simp only [CollatzResearch.WordTrace]
  refine ⟨14355114860123369876620273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19140153146831159835493697 14355114860123369876620273)
  ·
    refine ⟨10766336145092527407465205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14355114860123369876620273 10766336145092527407465205)
    ·
      refine ⟨1009344013602424444449863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10766336145092527407465205 1009344013602424444449863)
      ·
        refine ⟨1514016020403636666674795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1009344013602424444449863 1514016020403636666674795)
        ·
          refine ⟨2271024030605455000012193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1514016020403636666674795 2271024030605455000012193)
          ·
            refine ⟨1703268022954091250009145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2271024030605455000012193 1703268022954091250009145)
            ·
              refine ⟨1277451017215568437506859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1703268022954091250009145 1277451017215568437506859)
              ·
                refine ⟨1916176525823352656260289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1277451017215568437506859 1916176525823352656260289)
                ·
                  refine ⟨1437132394367514492195217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1916176525823352656260289 1437132394367514492195217)
                  ·
                    refine ⟨1077849295775635869146413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1437132394367514492195217 1077849295775635869146413)
                    ·
                      refine ⟨404193485915863450929905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1077849295775635869146413 404193485915863450929905)
                      ·
                        rfl

theorem cell23_787164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_787164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787164 prefixEnd_787164 := by exact prefixLift 787164
  have htrace : WordTrace (prefixWord ++ tailWord_787164) baseStart_787164 baseEnd_787164 := by
    simpa [prefixWord, tailWord_787164, baseEnd_787164] using wordTrace_append hprefix tailTrace_787164
  have hstable : (prefixWord ++ tailWord_787164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787164).length < 2 ^ (prefixWord ++ tailWord_787164).sum := by decide
  have hdescent : baseEnd_787164 < baseStart_787164 := by decide
  rcases family_descends (prefixWord ++ tailWord_787164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787188 : List Nat := [2, 6, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_787188 : Nat := 118140960795 + 787188 * 2 ^ 59
def prefixEnd_787188 : Nat := 4983230072969 + 3 ^ 40 * 787188 * 2
def baseEnd_787188 : Nat := 134735269817190452343265

theorem tailTrace_787188 : CollatzResearch.WordTrace tailWord_787188 prefixEnd_787188 134735269817190452343265 := by
  unfold tailWord_787188
  simp only [CollatzResearch.WordTrace]
  refine ⟨14355552536079895926057109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19140736714773194568076145 14355552536079895926057109)
  ·
    refine ⟨672916525128745121533927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14355552536079895926057109 672916525128745121533927)
    ·
      refine ⟨1009374787693117682300891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 672916525128745121533927 1009374787693117682300891)
      ·
        refine ⟨1514062181539676523451337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1009374787693117682300891 1514062181539676523451337)
        ·
          refine ⟨1135546636154757392588503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1514062181539676523451337 1135546636154757392588503)
          ·
            refine ⟨1703319954232136088882755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1135546636154757392588503 1703319954232136088882755)
            ·
              refine ⟨2554979931348204133324133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1703319954232136088882755 2554979931348204133324133)
              ·
                refine ⟨479058737127788274998275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2554979931348204133324133 479058737127788274998275)
                ·
                  refine ⟨718588105691682412497413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 479058737127788274998275 718588105691682412497413)
                  ·
                    refine ⟨134735269817190452343265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 718588105691682412497413 134735269817190452343265)
                    ·
                      rfl

theorem cell23_787188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_787188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787188 prefixEnd_787188 := by exact prefixLift 787188
  have htrace : WordTrace (prefixWord ++ tailWord_787188) baseStart_787188 baseEnd_787188 := by
    simpa [prefixWord, tailWord_787188, baseEnd_787188] using wordTrace_append hprefix tailTrace_787188
  have hstable : (prefixWord ++ tailWord_787188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787188).length < 2 ^ (prefixWord ++ tailWord_787188).sum := by decide
  have hdescent : baseEnd_787188 < baseStart_787188 := by decide
  rcases family_descends (prefixWord ++ tailWord_787188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787203 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 5]
def baseStart_787203 : Nat := 118140960795 + 787203 * 2 ^ 59
def prefixEnd_787203 : Nat := 4983230072969 + 3 ^ 40 * 787203 * 2
def baseEnd_787203 : Nat := 404213511661388798342225

theorem tailTrace_787203 : CollatzResearch.WordTrace tailWord_787203 prefixEnd_787203 404213511661388798342225 := by
  unfold tailWord_787203
  simp only [CollatzResearch.WordTrace]
  refine ⟨28711652167105449413910263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19141101444736966275940175 28711652167105449413910263)
  ·
    refine ⟨43067478250658174120865395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28711652167105449413910263 43067478250658174120865395)
    ·
      refine ⟨64601217375987261181298093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43067478250658174120865395 64601217375987261181298093)
      ·
        refine ⟨24225456515995222942986785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64601217375987261181298093 24225456515995222942986785)
        ·
          refine ⟨18169092386996417207240089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24225456515995222942986785 18169092386996417207240089)
          ·
            refine ⟨13626819290247312905430067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18169092386996417207240089 13626819290247312905430067)
            ·
              refine ⟨20440228935370969358145101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13626819290247312905430067 20440228935370969358145101)
              ·
                refine ⟨7665085850764113509304413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20440228935370969358145101 7665085850764113509304413)
                ·
                  refine ⟨2874407194036542565989155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7665085850764113509304413 2874407194036542565989155)
                  ·
                    refine ⟨4311610791054813848983733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2874407194036542565989155 4311610791054813848983733)
                    ·
                      refine ⟨404213511661388798342225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4311610791054813848983733 404213511661388798342225)
                      ·
                        rfl

theorem cell23_787203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_787203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787203 prefixEnd_787203 := by exact prefixLift 787203
  have htrace : WordTrace (prefixWord ++ tailWord_787203) baseStart_787203 baseEnd_787203 := by
    simpa [prefixWord, tailWord_787203, baseEnd_787203] using wordTrace_append hprefix tailTrace_787203
  have hstable : (prefixWord ++ tailWord_787203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787203).length < 2 ^ (prefixWord ++ tailWord_787203).sum := by decide
  have hdescent : baseEnd_787203 < baseStart_787203 := by decide
  rcases family_descends (prefixWord ++ tailWord_787203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787210 : List Nat := [3, 1, 2, 2, 1, 2, 4, 1, 1, 6]
def baseStart_787210 : Nat := 118140960795 + 787210 * 2 ^ 59
def prefixEnd_787210 : Nat := 4983230072969 + 3 ^ 40 * 787210 * 2
def baseEnd_787210 : Nat := 134739035341990090318231

theorem tailTrace_787210 : CollatzResearch.WordTrace tailWord_787210 prefixEnd_787210 134739035341990090318231 := by
  unfold tailWord_787210
  simp only [CollatzResearch.WordTrace]
  refine ⟨7177976869520022402353771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19141271652053393072943389 7177976869520022402353771)
  ·
    refine ⟨10766965304280033603530657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7177976869520022402353771 10766965304280033603530657)
    ·
      refine ⟨8075223978210025202647993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10766965304280033603530657 8075223978210025202647993)
      ·
        refine ⟨6056417983657518901985995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8075223978210025202647993 6056417983657518901985995)
        ·
          refine ⟨9084626975486278352978993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6056417983657518901985995 9084626975486278352978993)
          ·
            refine ⟨6813470231614708764734245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9084626975486278352978993 6813470231614708764734245)
            ·
              refine ⟨1277525668427757893387671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6813470231614708764734245 1277525668427757893387671)
              ·
                refine ⟨1916288502641636840081507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1277525668427757893387671 1916288502641636840081507)
                ·
                  refine ⟨2874432753962455260122261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1916288502641636840081507 2874432753962455260122261)
                  ·
                    refine ⟨134739035341990090318231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2874432753962455260122261 134739035341990090318231)
                    ·
                      rfl

theorem cell23_787210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_787210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787210 prefixEnd_787210 := by exact prefixLift 787210
  have htrace : WordTrace (prefixWord ++ tailWord_787210) baseStart_787210 baseEnd_787210 := by
    simpa [prefixWord, tailWord_787210, baseEnd_787210] using wordTrace_append hprefix tailTrace_787210
  have hstable : (prefixWord ++ tailWord_787210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787210).length < 2 ^ (prefixWord ++ tailWord_787210).sum := by decide
  have hdescent : baseEnd_787210 < baseStart_787210 := by decide
  rcases family_descends (prefixWord ++ tailWord_787210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787217 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 5, 2, 2]
def baseStart_787217 : Nat := 118140960795 + 787217 * 2 ^ 59
def prefixEnd_787217 : Nat := 4983230072969 + 3 ^ 40 * 787217 * 2
def baseEnd_787217 : Nat := 404220700390551743567161

theorem tailTrace_787217 : CollatzResearch.WordTrace tailWord_787217 prefixEnd_787217 404220700390551743567161 := by
  unfold tailWord_787217
  simp only [CollatzResearch.WordTrace]
  refine ⟨28712162789054729804919905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19141441859369819869946603 28712162789054729804919905)
  ·
    refine ⟨21534122091791047353689929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28712162789054729804919905 21534122091791047353689929)
    ·
      refine ⟨16150591568843285515267447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21534122091791047353689929 16150591568843285515267447)
      ·
        refine ⟨24225887353264928272901171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16150591568843285515267447 24225887353264928272901171)
        ·
          refine ⟨36338831029897392409351757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24225887353264928272901171 36338831029897392409351757)
          ·
            refine ⟨13627061636211522153506909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36338831029897392409351757 13627061636211522153506909)
            ·
              refine ⟨5110148113579320807565091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13627061636211522153506909 5110148113579320807565091)
              ·
                refine ⟨7665222170368981211347637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5110148113579320807565091 7665222170368981211347637)
                ·
                  refine ⟨718614578472091988563841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7665222170368981211347637 718614578472091988563841)
                  ·
                    refine ⟨538960933854068991422881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 718614578472091988563841 538960933854068991422881)
                    ·
                      refine ⟨404220700390551743567161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 538960933854068991422881 404220700390551743567161)
                      ·
                        rfl

theorem cell23_787217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5, 2, 2].length) (baseStart_787217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787217 prefixEnd_787217 := by exact prefixLift 787217
  have htrace : WordTrace (prefixWord ++ tailWord_787217) baseStart_787217 baseEnd_787217 := by
    simpa [prefixWord, tailWord_787217, baseEnd_787217] using wordTrace_append hprefix tailTrace_787217
  have hstable : (prefixWord ++ tailWord_787217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787217).length < 2 ^ (prefixWord ++ tailWord_787217).sum := by decide
  have hdescent : baseEnd_787217 < baseStart_787217 := by decide
  rcases family_descends (prefixWord ++ tailWord_787217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787234 : List Nat := [3, 3, 1, 1, 2, 2, 4, 1, 1, 1, 4]
def baseStart_787234 : Nat := 118140960795 + 787234 * 2 ^ 59
def prefixEnd_787234 : Nat := 4983230072969 + 3 ^ 40 * 787234 * 2
def baseEnd_787234 : Nat := 404229429561678177054583

theorem tailTrace_787234 : CollatzResearch.WordTrace tailWord_787234 prefixEnd_787234 404229429561678177054583 := by
  unfold tailWord_787234
  simp only [CollatzResearch.WordTrace]
  refine ⟨7178195707498285427072189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19141855219995427805525837 7178195707498285427072189)
  ·
    refine ⟨2691823390311857035152071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7178195707498285427072189 2691823390311857035152071)
    ·
      refine ⟨4037735085467785552728107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2691823390311857035152071 4037735085467785552728107)
      ·
        refine ⟨6056602628201678329092161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4037735085467785552728107 6056602628201678329092161)
        ·
          refine ⟨4542451971151258746819121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6056602628201678329092161 4542451971151258746819121)
          ·
            refine ⟨3406838978363444060114341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4542451971151258746819121 3406838978363444060114341)
            ·
              refine ⟨638782308443145761271439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3406838978363444060114341 638782308443145761271439)
              ·
                refine ⟨958173462664718641907159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 638782308443145761271439 958173462664718641907159)
                ·
                  refine ⟨1437260193997077962860739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 958173462664718641907159 1437260193997077962860739)
                  ·
                    refine ⟨2155890290995616944291109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1437260193997077962860739 2155890290995616944291109)
                    ·
                      refine ⟨404229429561678177054583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2155890290995616944291109 404229429561678177054583)
                      ·
                        rfl

theorem cell23_787234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_787234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787234 prefixEnd_787234 := by exact prefixLift 787234
  have htrace : WordTrace (prefixWord ++ tailWord_787234) baseStart_787234 baseEnd_787234 := by
    simpa [prefixWord, tailWord_787234, baseEnd_787234] using wordTrace_append hprefix tailTrace_787234
  have hstable : (prefixWord ++ tailWord_787234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787234).length < 2 ^ (prefixWord ++ tailWord_787234).sum := by decide
  have hdescent : baseEnd_787234 < baseStart_787234 := by decide
  rcases family_descends (prefixWord ++ tailWord_787234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787237 : List Nat := [1, 3, 1, 2, 3, 1, 3, 3, 1, 2, 3]
def baseStart_787237 : Nat := 118140960795 + 787237 * 2 ^ 59
def prefixEnd_787237 : Nat := 4983230072969 + 3 ^ 40 * 787237 * 2
def baseEnd_787237 : Nat := 404230970003641665317069

theorem tailTrace_787237 : CollatzResearch.WordTrace tailWord_787237 prefixEnd_787237 404230970003641665317069 := by
  unfold tailWord_787237
  simp only [CollatzResearch.WordTrace]
  refine ⟨28712892248982273220647965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19141928165988182147098643 28712892248982273220647965)
  ·
    refine ⟨10767334593368352457742987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28712892248982273220647965 10767334593368352457742987)
    ·
      refine ⟨16151001890052528686614481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10767334593368352457742987 16151001890052528686614481)
      ·
        refine ⟨12113251417539396514960861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16151001890052528686614481 12113251417539396514960861)
        ·
          refine ⟨4542469281577273693110323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12113251417539396514960861 4542469281577273693110323)
          ·
            refine ⟨6813703922365910539665485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4542469281577273693110323 6813703922365910539665485)
            ·
              refine ⟨2555138970887216452374557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6813703922365910539665485 2555138970887216452374557)
              ·
                refine ⟨958177114082706169640459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2555138970887216452374557 958177114082706169640459)
                ·
                  refine ⟨1437265671124059254460689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 958177114082706169640459 1437265671124059254460689)
                  ·
                    refine ⟨1077949253343044440845517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1437265671124059254460689 1077949253343044440845517)
                    ·
                      refine ⟨404230970003641665317069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1077949253343044440845517 404230970003641665317069)
                      ·
                        rfl

theorem cell23_787237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_787237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787237 prefixEnd_787237 := by exact prefixLift 787237
  have htrace : WordTrace (prefixWord ++ tailWord_787237) baseStart_787237 baseEnd_787237 := by
    simpa [prefixWord, tailWord_787237, baseEnd_787237] using wordTrace_append hprefix tailTrace_787237
  have hstable : (prefixWord ++ tailWord_787237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787237).length < 2 ^ (prefixWord ++ tailWord_787237).sum := by decide
  have hdescent : baseEnd_787237 < baseStart_787237 := by decide
  rcases family_descends (prefixWord ++ tailWord_787237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787251 : List Nat := [1, 1, 1, 2, 6, 1, 2, 4, 1, 2, 2]
def baseStart_787251 : Nat := 118140960795 + 787251 * 2 ^ 59
def prefixEnd_787251 : Nat := 4983230072969 + 3 ^ 40 * 787251 * 2
def baseEnd_787251 : Nat := 404238158732804610542005

theorem tailTrace_787251 : CollatzResearch.WordTrace tailWord_787251 prefixEnd_787251 404238158732804610542005 := by
  unfold tailWord_787251
  simp only [CollatzResearch.WordTrace]
  refine ⟨28713402870931553611657607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19142268580621035741105071 28713402870931553611657607)
  ·
    refine ⟨43070104306397330417486411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28713402870931553611657607 43070104306397330417486411)
    ·
      refine ⟨64605156459595995626229617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43070104306397330417486411 64605156459595995626229617)
      ·
        refine ⟨48453867344696996719672213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64605156459595995626229617 48453867344696996719672213)
        ·
          refine ⟨2271275031782671721234635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48453867344696996719672213 2271275031782671721234635)
          ·
            refine ⟨3406912547674007581851953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2271275031782671721234635 3406912547674007581851953)
            ·
              refine ⟨2555184410755505686388965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3406912547674007581851953 2555184410755505686388965)
              ·
                refine ⟨479097077016657316197931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2555184410755505686388965 479097077016657316197931)
                ·
                  refine ⟨718645615524985974296897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 479097077016657316197931 718645615524985974296897)
                  ·
                    refine ⟨538984211643739480722673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 718645615524985974296897 538984211643739480722673)
                    ·
                      refine ⟨404238158732804610542005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 538984211643739480722673 404238158732804610542005)
                      ·
                        rfl

theorem cell23_787251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4, 1, 2, 2].length) (baseStart_787251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787251 prefixEnd_787251 := by exact prefixLift 787251
  have htrace : WordTrace (prefixWord ++ tailWord_787251) baseStart_787251 baseEnd_787251 := by
    simpa [prefixWord, tailWord_787251, baseEnd_787251] using wordTrace_append hprefix tailTrace_787251
  have hstable : (prefixWord ++ tailWord_787251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787251).length < 2 ^ (prefixWord ++ tailWord_787251).sum := by decide
  have hdescent : baseEnd_787251 < baseStart_787251 := by decide
  rcases family_descends (prefixWord ++ tailWord_787251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787254 : List Nat := [5, 1, 2, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_787254 : Nat := 118140960795 + 787254 * 2 ^ 59
def prefixEnd_787254 : Nat := 4983230072969 + 3 ^ 40 * 787254 * 2
def baseEnd_787254 : Nat := 404239699174768098804491

theorem tailTrace_787254 : CollatzResearch.WordTrace tailWord_787254 prefixEnd_787254 404239699174768098804491 := by
  unfold tailWord_787254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1794594518120042820251051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19142341526613790082677877 1794594518120042820251051)
  ·
    refine ⟨2691891777180064230376577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1794594518120042820251051 2691891777180064230376577)
    ·
      refine ⟨2018918832885048172782433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2691891777180064230376577 2018918832885048172782433)
      ·
        refine ⟨1514189124663786129586825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2018918832885048172782433 1514189124663786129586825)
        ·
          refine ⟨1135641843497839597190119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1514189124663786129586825 1135641843497839597190119)
          ·
            refine ⟨1703462765246759395785179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1135641843497839597190119 1703462765246759395785179)
            ·
              refine ⟨2555194147870139093677769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1703462765246759395785179 2555194147870139093677769)
              ·
                refine ⟨1916395610902604320258327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2555194147870139093677769 1916395610902604320258327)
                ·
                  refine ⟨2874593416353906480387491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1916395610902604320258327 2874593416353906480387491)
                  ·
                    refine ⟨4311890124530859720581237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2874593416353906480387491 4311890124530859720581237)
                    ·
                      refine ⟨404239699174768098804491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4311890124530859720581237 404239699174768098804491)
                      ·
                        rfl

theorem cell23_787254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_787254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787254 prefixEnd_787254 := by exact prefixLift 787254
  have htrace : WordTrace (prefixWord ++ tailWord_787254) baseStart_787254 baseEnd_787254 := by
    simpa [prefixWord, tailWord_787254, baseEnd_787254] using wordTrace_append hprefix tailTrace_787254
  have hstable : (prefixWord ++ tailWord_787254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787254).length < 2 ^ (prefixWord ++ tailWord_787254).sum := by decide
  have hdescent : baseEnd_787254 < baseStart_787254 := by decide
  rcases family_descends (prefixWord ++ tailWord_787254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787261 : List Nat := [1, 4, 1, 4, 2, 1, 3, 1, 2, 4]
def baseStart_787261 : Nat := 118140960795 + 787261 * 2 ^ 59
def prefixEnd_787261 : Nat := 4983230072969 + 3 ^ 40 * 787261 * 2
def baseEnd_787261 : Nat := 134747764513116523805653

theorem tailTrace_787261 : CollatzResearch.WordTrace tailWord_787261 prefixEnd_787261 134747764513116523805653 := by
  unfold tailWord_787261
  simp only [CollatzResearch.WordTrace]
  refine ⟨28713767600895325319521637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19142511733930216879681091 28713767600895325319521637)
  ·
    refine ⟨5383831425167873497410307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28713767600895325319521637 5383831425167873497410307)
    ·
      refine ⟨8075747137751810246115461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5383831425167873497410307 8075747137751810246115461)
      ·
        refine ⟨1514202588328464421146649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8075747137751810246115461 1514202588328464421146649)
        ·
          refine ⟨1135651941246348315859987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1514202588328464421146649 1135651941246348315859987)
          ·
            refine ⟨1703477911869522473789981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1135651941246348315859987 1703477911869522473789981)
            ·
              refine ⟨638804216951070927671243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1703477911869522473789981 638804216951070927671243)
              ·
                refine ⟨958206325426606391506865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 638804216951070927671243 958206325426606391506865)
                ·
                  refine ⟨718654744069954793630149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 958206325426606391506865 718654744069954793630149)
                  ·
                    refine ⟨134747764513116523805653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 718654744069954793630149 134747764513116523805653)
                    ·
                      rfl

theorem cell23_787261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_787261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787261 prefixEnd_787261 := by exact prefixLift 787261
  have htrace : WordTrace (prefixWord ++ tailWord_787261) baseStart_787261 baseEnd_787261 := by
    simpa [prefixWord, tailWord_787261, baseEnd_787261] using wordTrace_append hprefix tailTrace_787261
  have hstable : (prefixWord ++ tailWord_787261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787261).length < 2 ^ (prefixWord ++ tailWord_787261).sum := by decide
  have hdescent : baseEnd_787261 < baseStart_787261 := by decide
  rcases family_descends (prefixWord ++ tailWord_787261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787283 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 1, 8]
def baseStart_787283 : Nat := 118140960795 + 787283 * 2 ^ 59
def prefixEnd_787283 : Nat := 4983230072969 + 3 ^ 40 * 787283 * 2
def baseEnd_787283 : Nat := 134751530037916161780619

theorem tailTrace_787283 : CollatzResearch.WordTrace tailWord_787283 prefixEnd_787283 134751530037916161780619 := by
  unfold tailWord_787283
  simp only [CollatzResearch.WordTrace]
  refine ⟨28714570006815623076822503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19143046671210415384548335 28714570006815623076822503)
  ·
    refine ⟨43071855010223434615233755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28714570006815623076822503 43071855010223434615233755)
    ·
      refine ⟨64607782515335151922850633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43071855010223434615233755 64607782515335151922850633)
      ·
        refine ⟨48455836886501363942137975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64607782515335151922850633 48455836886501363942137975)
        ·
          refine ⟨72683755329752045913206963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48455836886501363942137975 72683755329752045913206963)
          ·
            refine ⟨109025632994628068869810445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72683755329752045913206963 109025632994628068869810445)
            ·
              refine ⟨40884612372985525826178917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109025632994628068869810445 40884612372985525826178917)
              ·
                refine ⟨7665864819934786092408547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40884612372985525826178917 7665864819934786092408547)
                ·
                  refine ⟨11498797229902179138612821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7665864819934786092408547 11498797229902179138612821)
                  ·
                    refine ⟨134751530037916161780619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11498797229902179138612821 134751530037916161780619)
                    ·
                      rfl

theorem cell23_787283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 8].length) (baseStart_787283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787283 prefixEnd_787283 := by exact prefixLift 787283
  have htrace : WordTrace (prefixWord ++ tailWord_787283) baseStart_787283 baseEnd_787283 := by
    simpa [prefixWord, tailWord_787283, baseEnd_787283] using wordTrace_append hprefix tailTrace_787283
  have hstable : (prefixWord ++ tailWord_787283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787283).length < 2 ^ (prefixWord ++ tailWord_787283).sum := by decide
  have hdescent : baseEnd_787283 < baseStart_787283 := by decide
  rcases family_descends (prefixWord ++ tailWord_787283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787318 : List Nat := [5, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3]
def baseStart_787318 : Nat := 118140960795 + 787318 * 2 ^ 59
def prefixEnd_787318 : Nat := 4983230072969 + 3 ^ 40 * 787318 * 2
def baseEnd_787318 : Nat := 404272561936655848404197

theorem tailTrace_787318 : CollatzResearch.WordTrace tailWord_787318 prefixEnd_787318 404272561936655848404197 := by
  unfold tailWord_787318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1794740410105551503396663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19143897707792549369564405 1794740410105551503396663)
  ·
    refine ⟨2692110615158327255094995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1794740410105551503396663 2692110615158327255094995)
    ·
      refine ⟨4038165922737490882642493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2692110615158327255094995 4038165922737490882642493)
      ·
        refine ⟨1514312221026559080990935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4038165922737490882642493 1514312221026559080990935)
        ·
          refine ⟨2271468331539838621486403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1514312221026559080990935 2271468331539838621486403)
          ·
            refine ⟨3407202497309757932229605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2271468331539838621486403 3407202497309757932229605)
            ·
              refine ⟨638850468245579612293051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3407202497309757932229605 638850468245579612293051)
              ·
                refine ⟨958275702368369418439577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 638850468245579612293051 958275702368369418439577)
                ·
                  refine ⟨718706776776277063829683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 958275702368369418439577 718706776776277063829683)
                  ·
                    refine ⟨1078060165164415595744525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 718706776776277063829683 1078060165164415595744525)
                    ·
                      refine ⟨404272561936655848404197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1078060165164415595744525 404272561936655848404197)
                      ·
                        rfl

theorem cell23_787318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_787318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787318 prefixEnd_787318 := by exact prefixLift 787318
  have htrace : WordTrace (prefixWord ++ tailWord_787318) baseStart_787318 baseEnd_787318 := by
    simpa [prefixWord, tailWord_787318, baseEnd_787318] using wordTrace_append hprefix tailTrace_787318
  have hstable : (prefixWord ++ tailWord_787318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787318).length < 2 ^ (prefixWord ++ tailWord_787318).sum := by decide
  have hdescent : baseEnd_787318 < baseStart_787318 := by decide
  rcases family_descends (prefixWord ++ tailWord_787318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787357 : List Nat := [1, 4, 2, 1, 2, 1, 2, 2, 2, 3, 3]
def baseStart_787357 : Nat := 118140960795 + 787357 * 2 ^ 59
def prefixEnd_787357 : Nat := 4983230072969 + 3 ^ 40 * 787357 * 2
def baseEnd_787357 : Nat := 404292587682181195816517

theorem tailTrace_787357 : CollatzResearch.WordTrace tailWord_787357 prefixEnd_787357 404292587682181195816517 := by
  unfold tailWord_787357
  simp only [CollatzResearch.WordTrace]
  refine ⟨28717269008547533715016325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19144846005698355810010883 28717269008547533715016325)
  ·
    refine ⟨5384487939102662571565561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28717269008547533715016325 5384487939102662571565561)
    ·
      refine ⟨4038365954326996928674171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5384487939102662571565561 4038365954326996928674171)
      ·
        refine ⟨6057548931490495393011257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4038365954326996928674171 6057548931490495393011257)
        ·
          refine ⟨4543161698617871544758443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6057548931490495393011257 4543161698617871544758443)
          ·
            refine ⟨6814742547926807317137665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4543161698617871544758443 6814742547926807317137665)
            ·
              refine ⟨5111056910945105487853249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6814742547926807317137665 5111056910945105487853249)
              ·
                refine ⟨3833292683208829115889937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5111056910945105487853249 3833292683208829115889937)
                ·
                  refine ⟨2874969512406621836917453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3833292683208829115889937 2874969512406621836917453)
                  ·
                    refine ⟨1078113567152483188844045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2874969512406621836917453 1078113567152483188844045)
                    ·
                      refine ⟨404292587682181195816517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1078113567152483188844045 404292587682181195816517)
                      ·
                        rfl

theorem cell23_787357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_787357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787357 prefixEnd_787357 := by exact prefixLift 787357
  have htrace : WordTrace (prefixWord ++ tailWord_787357) baseStart_787357 baseEnd_787357 := by
    simpa [prefixWord, tailWord_787357, baseEnd_787357] using wordTrace_append hprefix tailTrace_787357
  have hstable : (prefixWord ++ tailWord_787357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787357).length < 2 ^ (prefixWord ++ tailWord_787357).sum := by decide
  have hdescent : baseEnd_787357 < baseStart_787357 := by decide
  rcases family_descends (prefixWord ++ tailWord_787357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787440 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 6]
def baseStart_787440 : Nat := 118140960795 + 787440 * 2 ^ 59
def prefixEnd_787440 : Nat := 4983230072969 + 3 ^ 40 * 787440 * 2
def baseEnd_787440 : Nat := 404335206576504371078635

theorem tailTrace_787440 : CollatzResearch.WordTrace tailWord_787440 prefixEnd_787440 404335206576504371078635 := by
  unfold tailWord_787440
  simp only [CollatzResearch.WordTrace]
  refine ⟨14360148133623419445143887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19146864178164559260191849 14360148133623419445143887)
  ·
    refine ⟨21540222200435129167715831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14360148133623419445143887 21540222200435129167715831)
    ·
      refine ⟨32310333300652693751573747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21540222200435129167715831 32310333300652693751573747)
      ·
        refine ⟨48465499950979040627360621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32310333300652693751573747 48465499950979040627360621)
        ·
          refine ⟨18174562481617140235260233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48465499950979040627360621 18174562481617140235260233)
          ·
            refine ⟨13630921861212855176445175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18174562481617140235260233 13630921861212855176445175)
            ·
              refine ⟨20446382791819282764667763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13630921861212855176445175 20446382791819282764667763)
              ·
                refine ⟨30669574187728924147001645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20446382791819282764667763 30669574187728924147001645)
                ·
                  refine ⟨11501090320398346555125617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30669574187728924147001645 11501090320398346555125617)
                  ·
                    refine ⟨8625817740298759916344213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11501090320398346555125617 8625817740298759916344213)
                    ·
                      refine ⟨404335206576504371078635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8625817740298759916344213 404335206576504371078635)
                      ·
                        rfl

theorem cell23_787440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 6].length) (baseStart_787440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787440 prefixEnd_787440 := by exact prefixLift 787440
  have htrace : WordTrace (prefixWord ++ tailWord_787440) baseStart_787440 baseEnd_787440 := by
    simpa [prefixWord, tailWord_787440, baseEnd_787440] using wordTrace_append hprefix tailTrace_787440
  have hstable : (prefixWord ++ tailWord_787440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787440).length < 2 ^ (prefixWord ++ tailWord_787440).sum := by decide
  have hdescent : baseEnd_787440 < baseStart_787440 := by decide
  rcases family_descends (prefixWord ++ tailWord_787440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787450 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 2, 9]
def baseStart_787450 : Nat := 118140960795 + 787450 * 2 ^ 59
def prefixEnd_787450 : Nat := 4983230072969 + 3 ^ 40 * 787450 * 2
def baseEnd_787450 : Nat := 134780113794349777317863

theorem tailTrace_787450 : CollatzResearch.WordTrace tailWord_787450 prefixEnd_787450 134780113794349777317863 := by
  unfold tailWord_787450
  simp only [CollatzResearch.WordTrace]
  refine ⟨7180165249302652649537951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19147107331473740398767869 7180165249302652649537951)
  ·
    refine ⟨10770247873953978974306927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7180165249302652649537951 10770247873953978974306927)
    ·
      refine ⟨16155371810930968461460391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10770247873953978974306927 16155371810930968461460391)
      ·
        refine ⟨24233057716396452692190587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16155371810930968461460391 24233057716396452692190587)
        ·
          refine ⟨36349586574594679038285881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24233057716396452692190587 36349586574594679038285881)
          ·
            refine ⟨27262189930946009278714411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36349586574594679038285881 27262189930946009278714411)
            ·
              refine ⟨40893284896419013918071617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27262189930946009278714411 40893284896419013918071617)
              ·
                refine ⟨30669963672314260438553713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40893284896419013918071617 30669963672314260438553713)
                ·
                  refine ⟨23002472754235695328915285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30669963672314260438553713 23002472754235695328915285)
                  ·
                    refine ⟨134780113794349777317863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 23002472754235695328915285 134780113794349777317863)
                    ·
                      rfl

theorem cell23_787450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_787450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787450 prefixEnd_787450 := by exact prefixLift 787450
  have htrace : WordTrace (prefixWord ++ tailWord_787450) baseStart_787450 baseEnd_787450 := by
    simpa [prefixWord, tailWord_787450, baseEnd_787450] using wordTrace_append hprefix tailTrace_787450
  have hstable : (prefixWord ++ tailWord_787450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787450).length < 2 ^ (prefixWord ++ tailWord_787450).sum := by decide
  have hdescent : baseEnd_787450 < baseStart_787450 := by decide
  rcases family_descends (prefixWord ++ tailWord_787450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787481 : List Nat := [1, 2, 1, 2, 1, 1, 4, 6, 1, 1, 3]
def baseStart_787481 : Nat := 118140960795 + 787481 * 2 ^ 59
def prefixEnd_787481 : Nat := 4983230072969 + 3 ^ 40 * 787481 * 2
def baseEnd_787481 : Nat := 404356259283338710665947

theorem tailTrace_787481 : CollatzResearch.WordTrace tailWord_787481 prefixEnd_787481 404356259283338710665947 := by
  unfold tailWord_787481
  simp only [CollatzResearch.WordTrace]
  refine ⟨28721791660098302892530297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19147861106732201928353531 28721791660098302892530297)
  ·
    refine ⟨21541343745073727169397723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28721791660098302892530297 21541343745073727169397723)
    ·
      refine ⟨32312015617610590754096585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21541343745073727169397723 32312015617610590754096585)
      ·
        refine ⟨24234011713207943065572439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32312015617610590754096585 24234011713207943065572439)
        ·
          refine ⟨36351017569811914598358659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24234011713207943065572439 36351017569811914598358659)
          ·
            refine ⟨54526526354717871897537989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36351017569811914598358659 54526526354717871897537989)
            ·
              refine ⟨10223723691509600980788373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54526526354717871897537989 10223723691509600980788373)
              ·
                refine ⟨479237048039512545974455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10223723691509600980788373 479237048039512545974455)
                ·
                  refine ⟨718855572059268818961683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 479237048039512545974455 718855572059268818961683)
                  ·
                    refine ⟨1078283358088903228442525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 718855572059268818961683 1078283358088903228442525)
                    ·
                      refine ⟨404356259283338710665947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1078283358088903228442525 404356259283338710665947)
                      ·
                        rfl

theorem cell23_787481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6, 1, 1, 3].length) (baseStart_787481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787481 prefixEnd_787481 := by exact prefixLift 787481
  have htrace : WordTrace (prefixWord ++ tailWord_787481) baseStart_787481 baseEnd_787481 := by
    simpa [prefixWord, tailWord_787481, baseEnd_787481] using wordTrace_append hprefix tailTrace_787481
  have hstable : (prefixWord ++ tailWord_787481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787481).length < 2 ^ (prefixWord ++ tailWord_787481).sum := by decide
  have hdescent : baseEnd_787481 < baseStart_787481 := by decide
  rcases family_descends (prefixWord ++ tailWord_787481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787488 : List Nat := [2, 1, 1, 7, 1, 2, 2, 1, 6]
def baseStart_787488 : Nat := 118140960795 + 787488 * 2 ^ 59
def prefixEnd_787488 : Nat := 4983230072969 + 3 ^ 40 * 787488 * 2
def baseEnd_787488 : Nat := 44928872627546687030935

theorem tailTrace_787488 : CollatzResearch.WordTrace tailWord_787488 prefixEnd_787488 44928872627546687030935 := by
  unfold tailWord_787488
  simp only [CollatzResearch.WordTrace]
  refine ⟨14361023485536471544017559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19148031314048628725356745 14361023485536471544017559)
  ·
    refine ⟨21541535228304707316026339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14361023485536471544017559 21541535228304707316026339)
    ·
      refine ⟨32312302842457060974039509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21541535228304707316026339 32312302842457060974039509)
      ·
        refine ⟨757319597870087366579051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 32312302842457060974039509 757319597870087366579051)
        ·
          refine ⟨1135979396805131049868577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 757319597870087366579051 1135979396805131049868577)
          ·
            refine ⟨851984547603848287401433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1135979396805131049868577 851984547603848287401433)
            ·
              refine ⟨638988410702886215551075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 851984547603848287401433 638988410702886215551075)
              ·
                refine ⟨958482616054329323326613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 638988410702886215551075 958482616054329323326613)
                ·
                  refine ⟨44928872627546687030935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 958482616054329323326613 44928872627546687030935)
                  ·
                    rfl

theorem cell23_787488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 6].length) (baseStart_787488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787488 prefixEnd_787488 := by exact prefixLift 787488
  have htrace : WordTrace (prefixWord ++ tailWord_787488) baseStart_787488 baseEnd_787488 := by
    simpa [prefixWord, tailWord_787488, baseEnd_787488] using wordTrace_append hprefix tailTrace_787488
  have hstable : (prefixWord ++ tailWord_787488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787488).length < 2 ^ (prefixWord ++ tailWord_787488).sum := by decide
  have hdescent : baseEnd_787488 < baseStart_787488 := by decide
  rcases family_descends (prefixWord ++ tailWord_787488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787508 : List Nat := [2, 5, 1, 2, 1, 1, 1, 3, 2, 3, 2]
def baseStart_787508 : Nat := 118140960795 + 787508 * 2 ^ 59
def prefixEnd_787508 : Nat := 4983230072969 + 3 ^ 40 * 787508 * 2
def baseEnd_787508 : Nat := 404370123261010105028323

theorem tailTrace_787508 : CollatzResearch.WordTrace tailWord_787508 prefixEnd_787508 404370123261010105028323 := by
  unfold tailWord_787508
  simp only [CollatzResearch.WordTrace]
  refine ⟨14361388215500243251881589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19148517620666991002508785 14361388215500243251881589)
  ·
    refine ⟨1346380145203147804863899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14361388215500243251881589 1346380145203147804863899)
    ·
      refine ⟨2019570217804721707295849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1346380145203147804863899 2019570217804721707295849)
      ·
        refine ⟨1514677663353541280471887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2019570217804721707295849 1514677663353541280471887)
        ·
          refine ⟨2272016495030311920707831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1514677663353541280471887 2272016495030311920707831)
          ·
            refine ⟨3408024742545467881061747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2272016495030311920707831 3408024742545467881061747)
            ·
              refine ⟨5112037113818201821592621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3408024742545467881061747 5112037113818201821592621)
              ·
                refine ⟨1917013917681825683097233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5112037113818201821592621 1917013917681825683097233)
                ·
                  refine ⟨1437760438261369262322925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1917013917681825683097233 1437760438261369262322925)
                  ·
                    refine ⟨539160164348013473371097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1437760438261369262322925 539160164348013473371097)
                    ·
                      refine ⟨404370123261010105028323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 539160164348013473371097 404370123261010105028323)
                      ·
                        rfl

theorem cell23_787508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_787508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787508 prefixEnd_787508 := by exact prefixLift 787508
  have htrace : WordTrace (prefixWord ++ tailWord_787508) baseStart_787508 baseEnd_787508 := by
    simpa [prefixWord, tailWord_787508, baseEnd_787508] using wordTrace_append hprefix tailTrace_787508
  have hstable : (prefixWord ++ tailWord_787508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787508).length < 2 ^ (prefixWord ++ tailWord_787508).sum := by decide
  have hdescent : baseEnd_787508 < baseStart_787508 := by decide
  rcases family_descends (prefixWord ++ tailWord_787508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787518 : List Nat := [4, 2, 1, 3, 1, 2, 3, 1, 1, 5]
def baseStart_787518 : Nat := 118140960795 + 787518 * 2 ^ 59
def prefixEnd_787518 : Nat := 4983230072969 + 3 ^ 40 * 787518 * 2
def baseEnd_787518 : Nat := 134791752689185021967759

theorem tailTrace_787518 : CollatzResearch.WordTrace tailWord_787518 prefixEnd_787518 134791752689185021967759 := by
  unfold tailWord_787518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3590392645120532276453401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19148760773976172141084805 3590392645120532276453401)
  ·
    refine ⟨2692794483840399207340051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3590392645120532276453401 2692794483840399207340051)
    ·
      refine ⟨4039191725760598811010077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2692794483840399207340051 4039191725760598811010077)
      ·
        refine ⟨1514696897160224554128779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4039191725760598811010077 1514696897160224554128779)
        ·
          refine ⟨2272045345740336831193169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1514696897160224554128779 2272045345740336831193169)
          ·
            refine ⟨1704034009305252623394877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2272045345740336831193169 1704034009305252623394877)
            ·
              refine ⟨639012753489469733773079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1704034009305252623394877 639012753489469733773079)
              ·
                refine ⟨958519130234204600659619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 639012753489469733773079 958519130234204600659619)
                ·
                  refine ⟨1437778695351306900989429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 958519130234204600659619 1437778695351306900989429)
                  ·
                    refine ⟨134791752689185021967759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1437778695351306900989429 134791752689185021967759)
                    ·
                      rfl

theorem cell23_787518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_787518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787518 prefixEnd_787518 := by exact prefixLift 787518
  have htrace : WordTrace (prefixWord ++ tailWord_787518) baseStart_787518 baseEnd_787518 := by
    simpa [prefixWord, tailWord_787518, baseEnd_787518] using wordTrace_append hprefix tailTrace_787518
  have hstable : (prefixWord ++ tailWord_787518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787518).length < 2 ^ (prefixWord ++ tailWord_787518).sum := by decide
  have hdescent : baseEnd_787518 < baseStart_787518 := by decide
  rcases family_descends (prefixWord ++ tailWord_787518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787557 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 2, 7]
def baseStart_787557 : Nat := 118140960795 + 787557 * 2 ^ 59
def prefixEnd_787557 : Nat := 4983230072969 + 3 ^ 40 * 787557 * 2
def baseEnd_787557 : Nat := 134798427937693471105199

theorem tailTrace_787557 : CollatzResearch.WordTrace tailWord_787557 prefixEnd_787557 134798427937693471105199 := by
  unfold tailWord_787557
  simp only [CollatzResearch.WordTrace]
  refine ⟨28724563607822967872296925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19149709071881978581531283 28724563607822967872296925)
  ·
    refine ⟨10771711352933612952111347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28724563607822967872296925 10771711352933612952111347)
    ·
      refine ⟨16157567029400419428167021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10771711352933612952111347 16157567029400419428167021)
      ·
        refine ⟨6059087636025157285562633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16157567029400419428167021 6059087636025157285562633)
        ·
          refine ⟨4544315727018867964171975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6059087636025157285562633 4544315727018867964171975)
          ·
            refine ⟨6816473590528301946257963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4544315727018867964171975 6816473590528301946257963)
            ·
              refine ⟨10224710385792452919386945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6816473590528301946257963 10224710385792452919386945)
              ·
                refine ⟨7668532789344339689540209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10224710385792452919386945 7668532789344339689540209)
                ·
                  refine ⟨5751399592008254767155157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7668532789344339689540209 5751399592008254767155157)
                  ·
                    refine ⟨134798427937693471105199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5751399592008254767155157 134798427937693471105199)
                    ·
                      rfl

theorem cell23_787557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_787557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787557 prefixEnd_787557 := by exact prefixLift 787557
  have htrace : WordTrace (prefixWord ++ tailWord_787557) baseStart_787557 baseEnd_787557 := by
    simpa [prefixWord, tailWord_787557, baseEnd_787557] using wordTrace_append hprefix tailTrace_787557
  have hstable : (prefixWord ++ tailWord_787557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787557).length < 2 ^ (prefixWord ++ tailWord_787557).sum := by decide
  have hdescent : baseEnd_787557 < baseStart_787557 := by decide
  rcases family_descends (prefixWord ++ tailWord_787557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787567 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 5]
def baseStart_787567 : Nat := 118140960795 + 787567 * 2 ^ 59
def prefixEnd_787567 : Nat := 4983230072969 + 3 ^ 40 * 787567 * 2
def baseEnd_787567 : Nat := 404400418619625374190551

theorem tailTrace_787567 : CollatzResearch.WordTrace tailWord_787567 prefixEnd_787567 404400418619625374190551 := by
  unfold tailWord_787567
  simp only [CollatzResearch.WordTrace]
  refine ⟨28724928337786739580160955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19149952225191159720107303 28724928337786739580160955)
  ·
    refine ⟨43087392506680109370241433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28724928337786739580160955 43087392506680109370241433)
    ·
      refine ⟨32315544380010082027681075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43087392506680109370241433 32315544380010082027681075)
      ·
        refine ⟨48473316570015123041521613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32315544380010082027681075 48473316570015123041521613)
        ·
          refine ⟨18177493713755671140570605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48473316570015123041521613 18177493713755671140570605)
          ·
            refine ⟨6816560142658376677713977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18177493713755671140570605 6816560142658376677713977)
            ·
              refine ⟨5112420106993782508285483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6816560142658376677713977 5112420106993782508285483)
              ·
                refine ⟨7668630160490673762428225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5112420106993782508285483 7668630160490673762428225)
                ·
                  refine ⟨5751472620368005321821169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7668630160490673762428225 5751472620368005321821169)
                  ·
                    refine ⟨4313604465276003991365877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5751472620368005321821169 4313604465276003991365877)
                    ·
                      refine ⟨404400418619625374190551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4313604465276003991365877 404400418619625374190551)
                      ·
                        rfl

theorem cell23_787567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 5].length) (baseStart_787567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787567 prefixEnd_787567 := by exact prefixLift 787567
  have htrace : WordTrace (prefixWord ++ tailWord_787567) baseStart_787567 baseEnd_787567 := by
    simpa [prefixWord, tailWord_787567, baseEnd_787567] using wordTrace_append hprefix tailTrace_787567
  have hstable : (prefixWord ++ tailWord_787567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787567).length < 2 ^ (prefixWord ++ tailWord_787567).sum := by decide
  have hdescent : baseEnd_787567 < baseStart_787567 := by decide
  rcases family_descends (prefixWord ++ tailWord_787567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787587 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 4, 6]
def baseStart_787587 : Nat := 118140960795 + 787587 * 2 ^ 59
def prefixEnd_787587 : Nat := 4983230072969 + 3 ^ 40 * 787587 * 2
def baseEnd_787587 : Nat := 134803562744238431980153

theorem tailTrace_787587 : CollatzResearch.WordTrace tailWord_787587 prefixEnd_787587 134803562744238431980153 := by
  unfold tailWord_787587
  simp only [CollatzResearch.WordTrace]
  refine ⟨28725657797714282995889015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19150438531809521997259343 28725657797714282995889015)
  ·
    refine ⟨43088486696571424493833523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28725657797714282995889015 43088486696571424493833523)
    ·
      refine ⟨64632730044857136740750285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43088486696571424493833523 64632730044857136740750285)
      ·
        refine ⟨24237273766821426277781357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64632730044857136740750285 24237273766821426277781357)
        ·
          refine ⟨9088977662558034854168009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24237273766821426277781357 9088977662558034854168009)
          ·
            refine ⟨6816733246918526140626007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9088977662558034854168009 6816733246918526140626007)
            ·
              refine ⟨10225099870377789210939011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6816733246918526140626007 10225099870377789210939011)
              ·
                refine ⟨15337649805566683816408517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10225099870377789210939011 15337649805566683816408517)
                ·
                  refine ⟨2875809338543753215576597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15337649805566683816408517 2875809338543753215576597)
                  ·
                    refine ⟨134803562744238431980153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2875809338543753215576597 134803562744238431980153)
                    ·
                      rfl

theorem cell23_787587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 6].length) (baseStart_787587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787587 prefixEnd_787587 := by exact prefixLift 787587
  have htrace : WordTrace (prefixWord ++ tailWord_787587) baseStart_787587 baseEnd_787587 := by
    simpa [prefixWord, tailWord_787587, baseEnd_787587] using wordTrace_append hprefix tailTrace_787587
  have hstable : (prefixWord ++ tailWord_787587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787587).length < 2 ^ (prefixWord ++ tailWord_787587).sum := by decide
  have hdescent : baseEnd_787587 < baseStart_787587 := by decide
  rcases family_descends (prefixWord ++ tailWord_787587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787588 : List Nat := [2, 3, 2, 1, 2, 2, 3, 2, 2, 1, 3]
def baseStart_787588 : Nat := 118140960795 + 787588 * 2 ^ 59
def prefixEnd_787588 : Nat := 4983230072969 + 3 ^ 40 * 787588 * 2
def baseEnd_787588 : Nat := 404411201713369792027955

theorem tailTrace_787588 : CollatzResearch.WordTrace tailWord_787588 prefixEnd_787588 404411201713369792027955 := by
  unfold tailWord_787588
  simp only [CollatzResearch.WordTrace]
  refine ⟨14362847135355330083337709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19150462847140440111116945 14362847135355330083337709)
  ·
    refine ⟨5386067675758248781251641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14362847135355330083337709 5386067675758248781251641)
    ·
      refine ⟨4039550756818686585938731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5386067675758248781251641 4039550756818686585938731)
      ·
        refine ⟨6059326135228029878908097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4039550756818686585938731 6059326135228029878908097)
        ·
          refine ⟨4544494601421022409181073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6059326135228029878908097 4544494601421022409181073)
          ·
            refine ⟨3408370951065766806885805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4544494601421022409181073 3408370951065766806885805)
            ·
              refine ⟨1278139106649662552582177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3408370951065766806885805 1278139106649662552582177)
              ·
                refine ⟨958604329987246914436633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1278139106649662552582177 958604329987246914436633)
                ·
                  refine ⟨718953247490435185827475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 958604329987246914436633 718953247490435185827475)
                  ·
                    refine ⟨1078429871235652778741213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 718953247490435185827475 1078429871235652778741213)
                    ·
                      refine ⟨404411201713369792027955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1078429871235652778741213 404411201713369792027955)
                      ·
                        rfl

theorem cell23_787588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_787588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787588 prefixEnd_787588 := by exact prefixLift 787588
  have htrace : WordTrace (prefixWord ++ tailWord_787588) baseStart_787588 baseEnd_787588 := by
    simpa [prefixWord, tailWord_787588, baseEnd_787588] using wordTrace_append hprefix tailTrace_787588
  have hstable : (prefixWord ++ tailWord_787588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787588).length < 2 ^ (prefixWord ++ tailWord_787588).sum := by decide
  have hdescent : baseEnd_787588 < baseStart_787588 := by decide
  rcases family_descends (prefixWord ++ tailWord_787588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787615 : List Nat := [1, 1, 2, 6, 2, 1, 2, 2, 1, 3, 2]
def baseStart_787615 : Nat := 118140960795 + 787615 * 2 ^ 59
def prefixEnd_787615 : Nat := 4983230072969 + 3 ^ 40 * 787615 * 2
def baseEnd_787615 : Nat := 404425065691041186390331

theorem tailTrace_787615 : CollatzResearch.WordTrace tailWord_787615 prefixEnd_787615 404425065691041186390331 := by
  unfold tailWord_787615
  simp only [CollatzResearch.WordTrace]
  refine ⟨28726679041612843777908299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19151119361075229185272199 28726679041612843777908299)
  ·
    refine ⟨43090018562419265666862449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28726679041612843777908299 43090018562419265666862449)
    ·
      refine ⟨32317513921814449250146837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43090018562419265666862449 32317513921814449250146837)
      ·
        refine ⟨1514883465085052308600633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32317513921814449250146837 1514883465085052308600633)
        ·
          refine ⟨1136162598813789231450475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1514883465085052308600633 1136162598813789231450475)
          ·
            refine ⟨1704243898220683847175713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1136162598813789231450475 1704243898220683847175713)
            ·
              refine ⟨1278182923665512885381785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1704243898220683847175713 1278182923665512885381785)
              ·
                refine ⟨958637192749134664036339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1278182923665512885381785 958637192749134664036339)
                ·
                  refine ⟨1437955789123701996054509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 958637192749134664036339 1437955789123701996054509)
                  ·
                    refine ⟨539233420921388248520441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1437955789123701996054509 539233420921388248520441)
                    ·
                      refine ⟨404425065691041186390331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 539233420921388248520441 404425065691041186390331)
                      ·
                        rfl

theorem cell23_787615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_787615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787615 prefixEnd_787615 := by exact prefixLift 787615
  have htrace : WordTrace (prefixWord ++ tailWord_787615) baseStart_787615 baseEnd_787615 := by
    simpa [prefixWord, tailWord_787615, baseEnd_787615] using wordTrace_append hprefix tailTrace_787615
  have hstable : (prefixWord ++ tailWord_787615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787615).length < 2 ^ (prefixWord ++ tailWord_787615).sum := by decide
  have hdescent : baseEnd_787615 < baseStart_787615 := by decide
  rcases family_descends (prefixWord ++ tailWord_787615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787681 : List Nat := [1, 2, 3, 1, 3, 3, 2, 1, 2, 5]
def baseStart_787681 : Nat := 118140960795 + 787681 * 2 ^ 59
def prefixEnd_787681 : Nat := 4983230072969 + 3 ^ 40 * 787681 * 2
def baseEnd_787681 : Nat := 134819651804745976055009

theorem tailTrace_787681 : CollatzResearch.WordTrace tailWord_787681 prefixEnd_787681 134819651804745976055009 := by
  unfold tailWord_787681
  simp only [CollatzResearch.WordTrace]
  refine ⟨28729086259373737049810897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19152724172915824699873931 28729086259373737049810897)
  ·
    refine ⟨21546814694530302787358173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28729086259373737049810897 21546814694530302787358173)
    ·
      refine ⟨8080055510448863545259315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21546814694530302787358173 8080055510448863545259315)
      ·
        refine ⟨12120083265673295317888973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8080055510448863545259315 12120083265673295317888973)
        ·
          refine ⟨4545031224627485744208365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12120083265673295317888973 4545031224627485744208365)
          ·
            refine ⟨1704386709235307154078137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4545031224627485744208365 1704386709235307154078137)
            ·
              refine ⟨1278290031926480365558603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1704386709235307154078137 1278290031926480365558603)
              ·
                refine ⟨1917435047889720548337905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1278290031926480365558603 1917435047889720548337905)
                ·
                  refine ⟨1438076285917290411253429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1917435047889720548337905 1438076285917290411253429)
                  ·
                    refine ⟨134819651804745976055009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1438076285917290411253429 134819651804745976055009)
                    ·
                      rfl

theorem cell23_787681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_787681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787681 prefixEnd_787681 := by exact prefixLift 787681
  have htrace : WordTrace (prefixWord ++ tailWord_787681) baseStart_787681 baseEnd_787681 := by
    simpa [prefixWord, tailWord_787681, baseEnd_787681] using wordTrace_append hprefix tailTrace_787681
  have hstable : (prefixWord ++ tailWord_787681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787681).length < 2 ^ (prefixWord ++ tailWord_787681).sum := by decide
  have hdescent : baseEnd_787681 < baseStart_787681 := by decide
  rcases family_descends (prefixWord ++ tailWord_787681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787684 : List Nat := [2, 3, 1, 1, 1, 2, 2, 3, 1, 3, 4]
def baseStart_787684 : Nat := 118140960795 + 787684 * 2 ^ 59
def prefixEnd_787684 : Nat := 4983230072969 + 3 ^ 40 * 787684 * 2
def baseEnd_787684 : Nat := 404460495856201416427513

theorem tailTrace_787684 : CollatzResearch.WordTrace tailWord_787684 prefixEnd_787684 404460495856201416427513 := by
  unfold tailWord_787684
  simp only [CollatzResearch.WordTrace]
  refine ⟨14364597839181434281085053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19152797118908579041446737 14364597839181434281085053)
  ·
    refine ⟨5386724189693037855406895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14364597839181434281085053 5386724189693037855406895)
    ·
      refine ⟨8080086284539556783110343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5386724189693037855406895 8080086284539556783110343)
      ·
        refine ⟨12120129426809335174665515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8080086284539556783110343 12120129426809335174665515)
        ·
          refine ⟨18180194140214002761998273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12120129426809335174665515 18180194140214002761998273)
          ·
            refine ⟨13635145605160502071498705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18180194140214002761998273 13635145605160502071498705)
            ·
              refine ⟨10226359203870376553624029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13635145605160502071498705 10226359203870376553624029)
              ·
                refine ⟨3834884701451391207609011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10226359203870376553624029 3834884701451391207609011)
                ·
                  refine ⟨5752327052177086811413517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3834884701451391207609011 5752327052177086811413517)
                  ·
                    refine ⟨2157122644566407554280069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5752327052177086811413517 2157122644566407554280069)
                    ·
                      refine ⟨404460495856201416427513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2157122644566407554280069 404460495856201416427513)
                      ·
                        rfl

theorem cell23_787684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_787684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787684 prefixEnd_787684 := by exact prefixLift 787684
  have htrace : WordTrace (prefixWord ++ tailWord_787684) baseStart_787684 baseEnd_787684 := by
    simpa [prefixWord, tailWord_787684, baseEnd_787684] using wordTrace_append hprefix tailTrace_787684
  have hstable : (prefixWord ++ tailWord_787684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787684).length < 2 ^ (prefixWord ++ tailWord_787684).sum := by decide
  have hdescent : baseEnd_787684 < baseStart_787684 := by decide
  rcases family_descends (prefixWord ++ tailWord_787684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787704 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 5, 4, 3]
def baseStart_787704 : Nat := 118140960795 + 787704 * 2 ^ 59
def prefixEnd_787704 : Nat := 4983230072969 + 3 ^ 40 * 787704 * 2
def baseEnd_787704 : Nat := 404470765469291338177421

theorem tailTrace_787704 : CollatzResearch.WordTrace tailWord_787704 prefixEnd_787704 404470765469291338177421 := by
  unfold tailWord_787704
  simp only [CollatzResearch.WordTrace]
  refine ⟨14364962569145205988949083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19153283425526941318598777 14364962569145205988949083)
  ·
    refine ⟨21547443853717808983423625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14364962569145205988949083 21547443853717808983423625)
    ·
      refine ⟨16160582890288356737567719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21547443853717808983423625 16160582890288356737567719)
      ·
        refine ⟨24240874335432535106351579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16160582890288356737567719 24240874335432535106351579)
        ·
          refine ⟨36361311503148802659527369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24240874335432535106351579 36361311503148802659527369)
          ·
            refine ⟨27270983627361601994645527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36361311503148802659527369 27270983627361601994645527)
            ·
              refine ⟨40906475441042402991968291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27270983627361601994645527 40906475441042402991968291)
              ·
                refine ⟨61359713161563604487952437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40906475441042402991968291 61359713161563604487952437)
                ·
                  refine ⟨5752473108896587920745541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61359713161563604487952437 5752473108896587920745541)
                  ·
                    refine ⟨1078588707918110235139789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5752473108896587920745541 1078588707918110235139789)
                    ·
                      refine ⟨404470765469291338177421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1078588707918110235139789 404470765469291338177421)
                      ·
                        rfl

theorem cell23_787704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 5, 4, 3].length) (baseStart_787704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787704 prefixEnd_787704 := by exact prefixLift 787704
  have htrace : WordTrace (prefixWord ++ tailWord_787704) baseStart_787704 baseEnd_787704 := by
    simpa [prefixWord, tailWord_787704, baseEnd_787704] using wordTrace_append hprefix tailTrace_787704
  have hstable : (prefixWord ++ tailWord_787704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787704).length < 2 ^ (prefixWord ++ tailWord_787704).sum := by decide
  have hdescent : baseEnd_787704 < baseStart_787704 := by decide
  rcases family_descends (prefixWord ++ tailWord_787704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787738 : List Nat := [3, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3]
def baseStart_787738 : Nat := 118140960795 + 787738 * 2 ^ 59
def prefixEnd_787738 : Nat := 4983230072969 + 3 ^ 40 * 787738 * 2
def baseEnd_787738 : Nat := 404488223811544205152265

theorem tailTrace_787738 : CollatzResearch.WordTrace tailWord_787738 prefixEnd_787738 404488223811544205152265 := by
  unfold tailWord_787738
  simp only [CollatzResearch.WordTrace]
  refine ⟨7182791305041808946158967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19154110146778157189757245 7182791305041808946158967)
  ·
    refine ⟨10774186957562713419238451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7182791305041808946158967 10774186957562713419238451)
    ·
      refine ⟨16161280436344070128857677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10774186957562713419238451 16161280436344070128857677)
      ·
        refine ⟨6060480163629026298321629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16161280436344070128857677 6060480163629026298321629)
        ·
          refine ⟨2272680061360884861870611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6060480163629026298321629 2272680061360884861870611)
          ·
            refine ⟨3409020092041327292805917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2272680061360884861870611 3409020092041327292805917)
            ·
              refine ⟨1278382534515497734802219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3409020092041327292805917 1278382534515497734802219)
              ·
                refine ⟨1917573801773246602203329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1278382534515497734802219 1917573801773246602203329)
                ·
                  refine ⟨1438180351329934951652497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1917573801773246602203329 1438180351329934951652497)
                  ·
                    refine ⟨1078635263497451213739373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1438180351329934951652497 1078635263497451213739373)
                    ·
                      refine ⟨404488223811544205152265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1078635263497451213739373 404488223811544205152265)
                      ·
                        rfl

theorem cell23_787738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_787738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787738 prefixEnd_787738 := by exact prefixLift 787738
  have htrace : WordTrace (prefixWord ++ tailWord_787738) baseStart_787738 baseEnd_787738 := by
    simpa [prefixWord, tailWord_787738, baseEnd_787738] using wordTrace_append hprefix tailTrace_787738
  have hstable : (prefixWord ++ tailWord_787738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787738).length < 2 ^ (prefixWord ++ tailWord_787738).sum := by decide
  have hdescent : baseEnd_787738 < baseStart_787738 := by decide
  rcases family_descends (prefixWord ++ tailWord_787738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787788 : List Nat := [2, 2, 1, 3, 2, 3, 2, 2, 1, 5]
def baseStart_787788 : Nat := 118140960795 + 787788 * 2 ^ 59
def prefixEnd_787788 : Nat := 4983230072969 + 3 ^ 40 * 787788 * 2
def baseEnd_787788 : Nat := 134837965948089669842345

theorem tailTrace_787788 : CollatzResearch.WordTrace tailWord_787788 prefixEnd_787788 134837965948089669842345 := by
  unfold tailWord_787788
  simp only [CollatzResearch.WordTrace]
  refine ⟨14366494434993047161978009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19155325913324062882637345 14366494434993047161978009)
  ·
    refine ⟨10774870826244785371483507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14366494434993047161978009 10774870826244785371483507)
    ·
      refine ⟨16162306239367178057225261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10774870826244785371483507 16162306239367178057225261)
      ·
        refine ⟨6060864839762691771459473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16162306239367178057225261 6060864839762691771459473)
        ·
          refine ⟨4545648629822018828594605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6060864839762691771459473 4545648629822018828594605)
          ·
            refine ⟨1704618236183257060722977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4545648629822018828594605 1704618236183257060722977)
            ·
              refine ⟨1278463677137442795542233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1704618236183257060722977 1278463677137442795542233)
              ·
                refine ⟨958847757853082096656675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1278463677137442795542233 958847757853082096656675)
                ·
                  refine ⟨1438271636779623144985013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 958847757853082096656675 1438271636779623144985013)
                  ·
                    refine ⟨134837965948089669842345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1438271636779623144985013 134837965948089669842345)
                    ·
                      rfl

theorem cell23_787788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 1, 5].length) (baseStart_787788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787788 prefixEnd_787788 := by exact prefixLift 787788
  have htrace : WordTrace (prefixWord ++ tailWord_787788) baseStart_787788 baseEnd_787788 := by
    simpa [prefixWord, tailWord_787788, baseEnd_787788] using wordTrace_append hprefix tailTrace_787788
  have hstable : (prefixWord ++ tailWord_787788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787788).length < 2 ^ (prefixWord ++ tailWord_787788).sum := by decide
  have hdescent : baseEnd_787788 < baseStart_787788 := by decide
  rcases family_descends (prefixWord ++ tailWord_787788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787801 : List Nat := [1, 2, 1, 2, 2, 2, 3, 2, 4, 4]
def baseStart_787801 : Nat := 118140960795 + 787801 * 2 ^ 59
def prefixEnd_787801 : Nat := 4983230072969 + 3 ^ 40 * 787801 * 2
def baseEnd_787801 : Nat := 134840191030925819554825

theorem tailTrace_787801 : CollatzResearch.WordTrace tailWord_787801 prefixEnd_787801 134840191030925819554825 := by
  unfold tailWord_787801
  simp only [CollatzResearch.WordTrace]
  refine ⟨28733463018938997544179257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19155642012625998362786171 28733463018938997544179257)
  ·
    refine ⟨21550097264204248158134443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28733463018938997544179257 21550097264204248158134443)
    ·
      refine ⟨32325145896306372237201665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21550097264204248158134443 32325145896306372237201665)
      ·
        refine ⟨24243859422229779177901249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32325145896306372237201665 24243859422229779177901249)
        ·
          refine ⟨18182894566672334383425937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24243859422229779177901249 18182894566672334383425937)
          ·
            refine ⟨13637170925004250787569453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18182894566672334383425937 13637170925004250787569453)
            ·
              refine ⟨5113939096876594045338545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13637170925004250787569453 5113939096876594045338545)
              ·
                refine ⟨3835454322657445534003909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5113939096876594045338545 3835454322657445534003909)
                ·
                  refine ⟨719147685498271037625733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3835454322657445534003909 719147685498271037625733)
                  ·
                    refine ⟨134840191030925819554825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 719147685498271037625733 134840191030925819554825)
                    ·
                      rfl

theorem cell23_787801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4, 4].length) (baseStart_787801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787801 prefixEnd_787801 := by exact prefixLift 787801
  have htrace : WordTrace (prefixWord ++ tailWord_787801) baseStart_787801 baseEnd_787801 := by
    simpa [prefixWord, tailWord_787801, baseEnd_787801] using wordTrace_append hprefix tailTrace_787801
  have hstable : (prefixWord ++ tailWord_787801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787801).length < 2 ^ (prefixWord ++ tailWord_787801).sum := by decide
  have hdescent : baseEnd_787801 < baseStart_787801 := by decide
  rcases family_descends (prefixWord ++ tailWord_787801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787808 : List Nat := [2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 4]
def baseStart_787808 : Nat := 118140960795 + 787808 * 2 ^ 59
def prefixEnd_787808 : Nat := 4983230072969 + 3 ^ 40 * 787808 * 2
def baseEnd_787808 : Nat := 404524167457358931276943

theorem tailTrace_787808 : CollatzResearch.WordTrace tailWord_787808 prefixEnd_787808 404524167457358931276943 := by
  unfold tailWord_787808
  simp only [CollatzResearch.WordTrace]
  refine ⟨14366859164956818869842039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19155812219942425159789385 14366859164956818869842039)
  ·
    refine ⟨21550288747435228304763059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14366859164956818869842039 21550288747435228304763059)
    ·
      refine ⟨32325433121152842457144589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21550288747435228304763059 32325433121152842457144589)
      ·
        refine ⟨12122037420432315921429221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32325433121152842457144589 12122037420432315921429221)
        ·
          refine ⟨2272882016331059235267979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12122037420432315921429221 2272882016331059235267979)
          ·
            refine ⟨3409323024496588852901969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2272882016331059235267979 3409323024496588852901969)
            ·
              refine ⟨2556992268372441639676477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3409323024496588852901969 2556992268372441639676477)
              ·
                refine ⟨958872100639665614878679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2556992268372441639676477 958872100639665614878679)
                ·
                  refine ⟨1438308150959498422318019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 958872100639665614878679 1438308150959498422318019)
                  ·
                    refine ⟨2157462226439247633477029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1438308150959498422318019 2157462226439247633477029)
                    ·
                      refine ⟨404524167457358931276943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2157462226439247633477029 404524167457358931276943)
                      ·
                        rfl

theorem cell23_787808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_787808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787808 prefixEnd_787808 := by exact prefixLift 787808
  have htrace : WordTrace (prefixWord ++ tailWord_787808) baseStart_787808 baseEnd_787808 := by
    simpa [prefixWord, tailWord_787808, baseEnd_787808] using wordTrace_append hprefix tailTrace_787808
  have hstable : (prefixWord ++ tailWord_787808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787808).length < 2 ^ (prefixWord ++ tailWord_787808).sum := by decide
  have hdescent : baseEnd_787808 < baseStart_787808 := by decide
  rcases family_descends (prefixWord ++ tailWord_787808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787811 : List Nat := [1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 5]
def baseStart_787811 : Nat := 118140960795 + 787811 * 2 ^ 59
def prefixEnd_787811 : Nat := 4983230072969 + 3 ^ 40 * 787811 * 2
def baseEnd_787811 : Nat := 404525707899322419539429

theorem tailTrace_787811 : CollatzResearch.WordTrace tailWord_787811 prefixEnd_787811 404525707899322419539429 := by
  unfold tailWord_787811
  simp only [CollatzResearch.WordTrace]
  refine ⟨28733827748902769252043287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19155885165935179501362191 28733827748902769252043287)
  ·
    refine ⟨43100741623354153878064931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28733827748902769252043287 43100741623354153878064931)
    ·
      refine ⟨64651112435031230817097397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43100741623354153878064931 64651112435031230817097397)
      ·
        refine ⟨6061041790784177889102881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64651112435031230817097397 6061041790784177889102881)
        ·
          refine ⟨4545781343088133416827161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6061041790784177889102881 4545781343088133416827161)
          ·
            refine ⟨3409336007316100062620371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4545781343088133416827161 3409336007316100062620371)
            ·
              refine ⟨5114004010974150093930557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3409336007316100062620371 5114004010974150093930557)
              ·
                refine ⟨1917751504115306285223959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5114004010974150093930557 1917751504115306285223959)
                ·
                  refine ⟨2876627256172959427835939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1917751504115306285223959 2876627256172959427835939)
                  ·
                    refine ⟨4314940884259439141753909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2876627256172959427835939 4314940884259439141753909)
                    ·
                      refine ⟨404525707899322419539429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4314940884259439141753909 404525707899322419539429)
                      ·
                        rfl

theorem cell23_787811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_787811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787811 prefixEnd_787811 := by exact prefixLift 787811
  have htrace : WordTrace (prefixWord ++ tailWord_787811) baseStart_787811 baseEnd_787811 := by
    simpa [prefixWord, tailWord_787811, baseEnd_787811] using wordTrace_append hprefix tailTrace_787811
  have hstable : (prefixWord ++ tailWord_787811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787811).length < 2 ^ (prefixWord ++ tailWord_787811).sum := by decide
  have hdescent : baseEnd_787811 < baseStart_787811 := by decide
  rcases family_descends (prefixWord ++ tailWord_787811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787821 : List Nat := [1, 5, 1, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_787821 : Nat := 118140960795 + 787821 * 2 ^ 59
def prefixEnd_787821 : Nat := 4983230072969 + 3 ^ 40 * 787821 * 2
def baseEnd_787821 : Nat := 404530842705867380414383

theorem tailTrace_787821 : CollatzResearch.WordTrace tailWord_787821 prefixEnd_787821 404530842705867380414383 := by
  unfold tailWord_787821
  simp only [CollatzResearch.WordTrace]
  refine ⟨28734192478866540959907317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19156128319244360639938211 28734192478866540959907317)
  ·
    refine ⟨2693830544893738214991311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28734192478866540959907317 2693830544893738214991311)
    ·
      refine ⟨4040745817340607322486967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2693830544893738214991311 4040745817340607322486967)
      ·
        refine ⟨6061118726010910983730451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4040745817340607322486967 6061118726010910983730451)
        ·
          refine ⟨9091678089016366475595677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6061118726010910983730451 9091678089016366475595677)
          ·
            refine ⟨3409379283381137428348379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9091678089016366475595677 3409379283381137428348379)
            ·
              refine ⟨5114068925071706142522569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3409379283381137428348379 5114068925071706142522569)
              ·
                refine ⟨3835551693803779606891927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5114068925071706142522569 3835551693803779606891927)
                ·
                  refine ⟨5753327540705669410337891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3835551693803779606891927 5753327540705669410337891)
                  ·
                    refine ⟨8629991311058504115506837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5753327540705669410337891 8629991311058504115506837)
                    ·
                      refine ⟨404530842705867380414383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8629991311058504115506837 404530842705867380414383)
                      ·
                        rfl

theorem cell23_787821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_787821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787821 prefixEnd_787821 := by exact prefixLift 787821
  have htrace : WordTrace (prefixWord ++ tailWord_787821) baseStart_787821 baseEnd_787821 := by
    simpa [prefixWord, tailWord_787821, baseEnd_787821] using wordTrace_append hprefix tailTrace_787821
  have hstable : (prefixWord ++ tailWord_787821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787821).length < 2 ^ (prefixWord ++ tailWord_787821).sum := by decide
  have hdescent : baseEnd_787821 < baseStart_787821 := by decide
  rcases family_descends (prefixWord ++ tailWord_787821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787825 : List Nat := [1, 2, 2, 2, 1, 2, 5, 1, 3, 2, 2]
def baseStart_787825 : Nat := 118140960795 + 787825 * 2 ^ 59
def prefixEnd_787825 : Nat := 4983230072969 + 3 ^ 40 * 787825 * 2
def baseEnd_787825 : Nat := 404532896628485364764365

theorem tailTrace_787825 : CollatzResearch.WordTrace tailWord_787825 prefixEnd_787825 404532896628485364764365 := by
  unfold tailWord_787825
  simp only [CollatzResearch.WordTrace]
  refine ⟨28734338370852049643052929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19156225580568033095368619 28734338370852049643052929)
  ·
    refine ⟨21550753778139037232289697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28734338370852049643052929 21550753778139037232289697)
    ·
      refine ⟨16163065333604277924217273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21550753778139037232289697 16163065333604277924217273)
      ·
        refine ⟨12122299000203208443162955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16163065333604277924217273 12122299000203208443162955)
        ·
          refine ⟨18183448500304812664744433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12122299000203208443162955 18183448500304812664744433)
          ·
            refine ⟨13637586375228609498558325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18183448500304812664744433 13637586375228609498558325)
            ·
              refine ⟨1278523722677682140489843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13637586375228609498558325 1278523722677682140489843)
              ·
                refine ⟨1917785584016523210734765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1278523722677682140489843 1917785584016523210734765)
                ·
                  refine ⟨719169594006196204025537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1917785584016523210734765 719169594006196204025537)
                  ·
                    refine ⟨539377195504647153019153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 719169594006196204025537 539377195504647153019153)
                    ·
                      refine ⟨404532896628485364764365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 539377195504647153019153 404532896628485364764365)
                      ·
                        rfl

theorem cell23_787825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3, 2, 2].length) (baseStart_787825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787825 prefixEnd_787825 := by exact prefixLift 787825
  have htrace : WordTrace (prefixWord ++ tailWord_787825) baseStart_787825 baseEnd_787825 := by
    simpa [prefixWord, tailWord_787825, baseEnd_787825] using wordTrace_append hprefix tailTrace_787825
  have hstable : (prefixWord ++ tailWord_787825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787825).length < 2 ^ (prefixWord ++ tailWord_787825).sum := by decide
  have hdescent : baseEnd_787825 < baseStart_787825 := by decide
  rcases family_descends (prefixWord ++ tailWord_787825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787842 : List Nat := [3, 4, 2, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_787842 : Nat := 118140960795 + 787842 * 2 ^ 59
def prefixEnd_787842 : Nat := 4983230072969 + 3 ^ 40 * 787842 * 2
def baseEnd_787842 : Nat := 404541625799611798251787

theorem tailTrace_787842 : CollatzResearch.WordTrace tailWord_787842 prefixEnd_787842 404541625799611798251787 := by
  unfold tailWord_787842
  simp only [CollatzResearch.WordTrace]
  refine ⟨7183739602947615386605445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19156638941193641030947853 7183739602947615386605445)
  ·
    refine ⟨1346951175552677884988521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7183739602947615386605445 1346951175552677884988521)
    ·
      refine ⟨1010213381664508413741391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1346951175552677884988521 1010213381664508413741391)
      ·
        refine ⟨1515320072496762620612087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1010213381664508413741391 1515320072496762620612087)
        ·
          refine ⟨2272980108745143930918131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1515320072496762620612087 2272980108745143930918131)
          ·
            refine ⟨3409470163117715896377197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2272980108745143930918131 3409470163117715896377197)
            ·
              refine ⟨1278551311169143461141449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3409470163117715896377197 1278551311169143461141449)
              ·
                refine ⟨958913483376857595856087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1278551311169143461141449 958913483376857595856087)
                ·
                  refine ⟨1438370225065286393784131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 958913483376857595856087 1438370225065286393784131)
                  ·
                    refine ⟨2157555337597929590676197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1438370225065286393784131 2157555337597929590676197)
                    ·
                      refine ⟨404541625799611798251787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2157555337597929590676197 404541625799611798251787)
                      ·
                        rfl

theorem cell23_787842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_787842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787842 prefixEnd_787842 := by exact prefixLift 787842
  have htrace : WordTrace (prefixWord ++ tailWord_787842) baseStart_787842 baseEnd_787842 := by
    simpa [prefixWord, tailWord_787842, baseEnd_787842] using wordTrace_append hprefix tailTrace_787842
  have hstable : (prefixWord ++ tailWord_787842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787842).length < 2 ^ (prefixWord ++ tailWord_787842).sum := by decide
  have hdescent : baseEnd_787842 < baseStart_787842 := by decide
  rcases family_descends (prefixWord ++ tailWord_787842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
