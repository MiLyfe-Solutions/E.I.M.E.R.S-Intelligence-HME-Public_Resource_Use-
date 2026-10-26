import V185TrunkScan23Chunk0418

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2477396 : List Nat := [2, 4, 1, 1, 2, 1, 1, 3, 2, 6]
def baseStart_2477396 : Nat := 118140960795 + 2477396 * 2 ^ 59
def prefixEnd_2477396 : Nat := 4983230072969 + 3 ^ 40 * 2477396 * 2
def baseEnd_2477396 : Nat := 424031639842031470152223

theorem tailTrace_2477396 : CollatzResearch.WordTrace tailWord_2477396 prefixEnd_2477396 424031639842031470152223 := by
  unfold tailWord_2477396
  simp only [CollatzResearch.WordTrace]
  refine ⟨45179027666412436198378021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60238703555216581597837361 45179027666412436198378021)
  ·
    refine ⟨8471067687452331787195879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45179027666412436198378021 8471067687452331787195879)
    ·
      refine ⟨12706601531178497680793819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8471067687452331787195879 12706601531178497680793819)
      ·
        refine ⟨19059902296767746521190729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12706601531178497680793819 19059902296767746521190729)
        ·
          refine ⟨14294926722575809890893047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19059902296767746521190729 14294926722575809890893047)
          ·
            refine ⟨21442390083863714836339571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14294926722575809890893047 21442390083863714836339571)
            ·
              refine ⟨32163585125795572254509357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21442390083863714836339571 32163585125795572254509357)
              ·
                refine ⟨12061344422173339595441009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32163585125795572254509357 12061344422173339595441009)
                ·
                  refine ⟨9046008316630004696580757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12061344422173339595441009 9046008316630004696580757)
                  ·
                    refine ⟨424031639842031470152223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9046008316630004696580757 424031639842031470152223)
                    ·
                      rfl

theorem cell23_2477396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_2477396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477396 prefixEnd_2477396 := by exact prefixLift 2477396
  have htrace : WordTrace (prefixWord ++ tailWord_2477396) baseStart_2477396 baseEnd_2477396 := by
    simpa [prefixWord, tailWord_2477396, baseEnd_2477396] using wordTrace_append hprefix tailTrace_2477396
  have hstable : (prefixWord ++ tailWord_2477396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477396).length < 2 ^ (prefixWord ++ tailWord_2477396).sum := by decide
  have hdescent : baseEnd_2477396 < baseStart_2477396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477397 : List Nat := [1, 3, 2, 2, 3, 2, 3, 1, 2, 1, 3]
def baseStart_2477397 : Nat := 118140960795 + 2477397 * 2 ^ 59
def prefixEnd_2477397 : Nat := 4983230072969 + 3 ^ 40 * 2477397 * 2
def baseEnd_2477397 : Nat := 1272095433006748906544165

theorem tailTrace_2477397 : CollatzResearch.WordTrace tailWord_2477397 prefixEnd_2477397 1272095433006748906544165 := by
  unfold tailWord_2477397
  simp only [CollatzResearch.WordTrace]
  refine ⟨90358091805821249567542445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60238727870547499711694963 90358091805821249567542445)
  ·
    refine ⟨33884284427182968587828417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90358091805821249567542445 33884284427182968587828417)
    ·
      refine ⟨25413213320387226440871313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33884284427182968587828417 25413213320387226440871313)
      ·
        refine ⟨19059909990290419830653485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25413213320387226440871313 19059909990290419830653485)
        ·
          refine ⟨7147466246358907436495057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19059909990290419830653485 7147466246358907436495057)
          ·
            refine ⟨5360599684769180577371293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7147466246358907436495057 5360599684769180577371293)
            ·
              refine ⟨2010224881788442716514235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5360599684769180577371293 2010224881788442716514235)
              ·
                refine ⟨3015337322682664074771353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2010224881788442716514235 3015337322682664074771353)
                ·
                  refine ⟨2261502992011998056078515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3015337322682664074771353 2261502992011998056078515)
                  ·
                    refine ⟨3392254488017997084117773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2261502992011998056078515 3392254488017997084117773)
                    ·
                      refine ⟨1272095433006748906544165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3392254488017997084117773 1272095433006748906544165)
                      ·
                        rfl

theorem cell23_2477397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_2477397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477397 prefixEnd_2477397 := by exact prefixLift 2477397
  have htrace : WordTrace (prefixWord ++ tailWord_2477397) baseStart_2477397 baseEnd_2477397 := by
    simpa [prefixWord, tailWord_2477397, baseEnd_2477397] using wordTrace_append hprefix tailTrace_2477397
  have hstable : (prefixWord ++ tailWord_2477397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477397).length < 2 ^ (prefixWord ++ tailWord_2477397).sum := by decide
  have hdescent : baseEnd_2477397 < baseStart_2477397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477419 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 7]
def baseStart_2477419 : Nat := 118140960795 + 2477419 * 2 ^ 59
def prefixEnd_2477419 : Nat := 4983230072969 + 3 ^ 40 * 2477419 * 2
def baseEnd_2477419 : Nat := 1272106729581147820469063

theorem tailTrace_2477419 : CollatzResearch.WordTrace tailWord_2477419 prefixEnd_2477419 1272106729581147820469063 := by
  unfold tailWord_2477419
  simp only [CollatzResearch.WordTrace]
  refine ⟨90358894211741547324843311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60239262807827698216562207 90358894211741547324843311)
  ·
    refine ⟨135538341317612320987264967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90358894211741547324843311 135538341317612320987264967)
    ·
      refine ⟨203307511976418481480897451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135538341317612320987264967 203307511976418481480897451)
      ·
        refine ⟨304961267964627722221346177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203307511976418481480897451 304961267964627722221346177)
        ·
          refine ⟨228720950973470791666009633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304961267964627722221346177 228720950973470791666009633)
          ·
            refine ⟨171540713230103093749507225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228720950973470791666009633 171540713230103093749507225)
            ·
              refine ⟨128655534922577320312130419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171540713230103093749507225 128655534922577320312130419)
              ·
                refine ⟨192983302383865980468195629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128655534922577320312130419 192983302383865980468195629)
                ·
                  refine ⟨72368738393949742675573361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 192983302383865980468195629 72368738393949742675573361)
                  ·
                    refine ⟨54276553795462307006680021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72368738393949742675573361 54276553795462307006680021)
                    ·
                      refine ⟨1272106729581147820469063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54276553795462307006680021 1272106729581147820469063)
                      ·
                        rfl

theorem cell23_2477419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 7].length) (baseStart_2477419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477419 prefixEnd_2477419 := by exact prefixLift 2477419
  have htrace : WordTrace (prefixWord ++ tailWord_2477419) baseStart_2477419 baseEnd_2477419 := by
    simpa [prefixWord, tailWord_2477419, baseEnd_2477419] using wordTrace_append hprefix tailTrace_2477419
  have hstable : (prefixWord ++ tailWord_2477419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477419).length < 2 ^ (prefixWord ++ tailWord_2477419).sum := by decide
  have hdescent : baseEnd_2477419 < baseStart_2477419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477420 : List Nat := [2, 2, 1, 1, 5, 1, 1, 2, 4, 2, 2]
def baseStart_2477420 : Nat := 118140960795 + 2477420 * 2 ^ 59
def prefixEnd_2477420 : Nat := 4983230072969 + 3 ^ 40 * 2477420 * 2
def baseEnd_2477420 : Nat := 1272107243061802316556559

theorem tailTrace_2477420 : CollatzResearch.WordTrace tailWord_2477420 prefixEnd_2477420 1272107243061802316556559 := by
  unfold tailWord_2477420
  simp only [CollatzResearch.WordTrace]
  refine ⟨45179465342368962247814857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60239287123158616330419809 45179465342368962247814857)
  ·
    refine ⟨33884599006776721685861143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45179465342368962247814857 33884599006776721685861143)
    ·
      refine ⟨50826898510165082528791715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33884599006776721685861143 50826898510165082528791715)
      ·
        refine ⟨76240347765247623793187573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50826898510165082528791715 76240347765247623793187573)
        ·
          refine ⟨7147532602991964730611335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76240347765247623793187573 7147532602991964730611335)
          ·
            refine ⟨10721298904487947095917003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7147532602991964730611335 10721298904487947095917003)
            ·
              refine ⟨16081948356731920643875505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10721298904487947095917003 16081948356731920643875505)
              ·
                refine ⟨12061461267548940482906629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16081948356731920643875505 12061461267548940482906629)
                ·
                  refine ⟨2261523987665426340544993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12061461267548940482906629 2261523987665426340544993)
                  ·
                    refine ⟨1696142990749069755408745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2261523987665426340544993 1696142990749069755408745)
                    ·
                      refine ⟨1272107243061802316556559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1696142990749069755408745 1272107243061802316556559)
                      ·
                        rfl

theorem cell23_2477420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 2, 2].length) (baseStart_2477420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477420 prefixEnd_2477420 := by exact prefixLift 2477420
  have htrace : WordTrace (prefixWord ++ tailWord_2477420) baseStart_2477420 baseEnd_2477420 := by
    simpa [prefixWord, tailWord_2477420, baseEnd_2477420] using wordTrace_append hprefix tailTrace_2477420
  have hstable : (prefixWord ++ tailWord_2477420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477420).length < 2 ^ (prefixWord ++ tailWord_2477420).sum := by decide
  have hdescent : baseEnd_2477420 < baseStart_2477420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477443 : List Nat := [1, 1, 1, 3, 5, 3, 1, 1, 7]
def baseStart_2477443 : Nat := 118140960795 + 2477443 * 2 ^ 59
def prefixEnd_2477443 : Nat := 4983230072969 + 3 ^ 40 * 2477443 * 2
def baseEnd_2477443 : Nat := 141346561457428414063217

theorem tailTrace_2477443 : CollatzResearch.WordTrace tailWord_2477443 prefixEnd_2477443 141346561457428414063217 := by
  unfold tailWord_2477443
  simp only [CollatzResearch.WordTrace]
  refine ⟨90359769563654599423716983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60239846375769732949144655 90359769563654599423716983)
  ·
    refine ⟨135539654345481899135575475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90359769563654599423716983 135539654345481899135575475)
    ·
      refine ⟨203309481518222848703363213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135539654345481899135575475 203309481518222848703363213)
      ·
        refine ⟨76241055569333568263761205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203309481518222848703363213 76241055569333568263761205)
        ·
          refine ⟨7147598959625022024727613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76241055569333568263761205 7147598959625022024727613)
          ·
            refine ⟨2680349609859383259272855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7147598959625022024727613 2680349609859383259272855)
            ·
              refine ⟨4020524414789074888909283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2680349609859383259272855 4020524414789074888909283)
              ·
                refine ⟨6030786622183612333363925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4020524414789074888909283 6030786622183612333363925)
                ·
                  refine ⟨141346561457428414063217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6030786622183612333363925 141346561457428414063217)
                  ·
                    rfl

theorem cell23_2477443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 7].length) (baseStart_2477443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477443 prefixEnd_2477443 := by exact prefixLift 2477443
  have htrace : WordTrace (prefixWord ++ tailWord_2477443) baseStart_2477443 baseEnd_2477443 := by
    simpa [prefixWord, tailWord_2477443, baseEnd_2477443] using wordTrace_append hprefix tailTrace_2477443
  have hstable : (prefixWord ++ tailWord_2477443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477443).length < 2 ^ (prefixWord ++ tailWord_2477443).sum := by decide
  have hdescent : baseEnd_2477443 < baseStart_2477443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477454 : List Nat := [4, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2]
def baseStart_2477454 : Nat := 118140960795 + 2477454 * 2 ^ 59
def prefixEnd_2477454 : Nat := 4983230072969 + 3 ^ 40 * 2477454 * 2
def baseEnd_2477454 : Nat := 1272124701404055183531403

theorem tailTrace_2477454 : CollatzResearch.WordTrace tailWord_2477454 prefixEnd_2477454 1272124701404055183531403 := by
  unfold tailWord_2477454
  simp only [CollatzResearch.WordTrace]
  refine ⟨11295021345826843537795927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60240113844409832201578277 11295021345826843537795927)
  ·
    refine ⟨16942532018740265306693891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11295021345826843537795927 16942532018740265306693891)
    ·
      refine ⟨25413798028110397960040837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16942532018740265306693891 25413798028110397960040837)
      ·
        refine ⟨4765087130270699617507657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25413798028110397960040837 4765087130270699617507657)
        ·
          refine ⟨3573815347703024713130743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4765087130270699617507657 3573815347703024713130743)
          ·
            refine ⟨5360723021554537069696115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3573815347703024713130743 5360723021554537069696115)
            ·
              refine ⟨8041084532331805604544173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5360723021554537069696115 8041084532331805604544173)
              ·
                refine ⟨3015406699624427101704065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8041084532331805604544173 3015406699624427101704065)
                ·
                  refine ⟨2261555024718320326278049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3015406699624427101704065 2261555024718320326278049)
                  ·
                    refine ⟨1696166268538740244708537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2261555024718320326278049 1696166268538740244708537)
                    ·
                      refine ⟨1272124701404055183531403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1696166268538740244708537 1272124701404055183531403)
                      ·
                        rfl

theorem cell23_2477454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_2477454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477454 prefixEnd_2477454 := by exact prefixLift 2477454
  have htrace : WordTrace (prefixWord ++ tailWord_2477454) baseStart_2477454 baseEnd_2477454 := by
    simpa [prefixWord, tailWord_2477454, baseEnd_2477454] using wordTrace_append hprefix tailTrace_2477454
  have hstable : (prefixWord ++ tailWord_2477454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477454).length < 2 ^ (prefixWord ++ tailWord_2477454).sum := by decide
  have hdescent : baseEnd_2477454 < baseStart_2477454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477466 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7]
def baseStart_2477466 : Nat := 118140960795 + 2477466 * 2 ^ 59
def prefixEnd_2477466 : Nat := 4983230072969 + 3 ^ 40 * 2477466 * 2
def baseEnd_2477466 : Nat := 1272130863171909136581347

theorem tailTrace_2477466 : CollatzResearch.WordTrace tailWord_2477466 prefixEnd_2477466 1272130863171909136581347 := by
  unfold tailWord_2477466
  simp only [CollatzResearch.WordTrace]
  refine ⟨22590152110642818587951063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60240405628380849567869501 22590152110642818587951063)
  ·
    refine ⟨33885228165964227881926595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22590152110642818587951063 33885228165964227881926595)
    ·
      refine ⟨50827842248946341822889893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33885228165964227881926595 50827842248946341822889893)
      ·
        refine ⟨9530220421677439091791855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50827842248946341822889893 9530220421677439091791855)
        ·
          refine ⟨14295330632516158637687783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9530220421677439091791855 14295330632516158637687783)
          ·
            refine ⟨21442995948774237956531675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14295330632516158637687783 21442995948774237956531675)
            ·
              refine ⟨32164493923161356934797513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21442995948774237956531675 32164493923161356934797513)
              ·
                refine ⟨24123370442371017701098135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32164493923161356934797513 24123370442371017701098135)
                ·
                  refine ⟨36185055663556526551647203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24123370442371017701098135 36185055663556526551647203)
                  ·
                    refine ⟨54277583495334789827470805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36185055663556526551647203 54277583495334789827470805)
                    ·
                      refine ⟨1272130863171909136581347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54277583495334789827470805 1272130863171909136581347)
                      ·
                        rfl

theorem cell23_2477466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_2477466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477466 prefixEnd_2477466 := by exact prefixLift 2477466
  have htrace : WordTrace (prefixWord ++ tailWord_2477466) baseStart_2477466 baseEnd_2477466 := by
    simpa [prefixWord, tailWord_2477466, baseEnd_2477466] using wordTrace_append hprefix tailTrace_2477466
  have hstable : (prefixWord ++ tailWord_2477466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477466).length < 2 ^ (prefixWord ++ tailWord_2477466).sum := by decide
  have hdescent : baseEnd_2477466 < baseStart_2477466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477530 : List Nat := [3, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3]
def baseStart_2477530 : Nat := 118140960795 + 2477530 * 2 ^ 59
def prefixEnd_2477530 : Nat := 4983230072969 + 3 ^ 40 * 2477530 * 2
def baseEnd_2477530 : Nat := 1272163725933796886181053

theorem tailTrace_2477530 : CollatzResearch.WordTrace tailWord_2477530 prefixEnd_2477530 1272163725933796886181053 := by
  unfold tailWord_2477530
  simp only [CollatzResearch.WordTrace]
  refine ⟨22590735678584853320533511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60241961809559608854756029 22590735678584853320533511)
  ·
    refine ⟨33886103517877279980800267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22590735678584853320533511 33886103517877279980800267)
    ·
      refine ⟨50829155276815919971200401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33886103517877279980800267 50829155276815919971200401)
      ·
        refine ⟨38121866457611939978400301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50829155276815919971200401 38121866457611939978400301)
        ·
          refine ⟨14295699921604477491900113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38121866457611939978400301 14295699921604477491900113)
          ·
            refine ⟨10721774941203358118925085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14295699921604477491900113 10721774941203358118925085)
            ·
              refine ⟨4020665602951259294596907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10721774941203358118925085 4020665602951259294596907)
              ·
                refine ⟨6030998404426888941895361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4020665602951259294596907 6030998404426888941895361)
                ·
                  refine ⟨4523248803320166706421521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6030998404426888941895361 4523248803320166706421521)
                  ·
                    refine ⟨3392436602490125029816141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4523248803320166706421521 3392436602490125029816141)
                    ·
                      refine ⟨1272163725933796886181053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3392436602490125029816141 1272163725933796886181053)
                      ·
                        rfl

theorem cell23_2477530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_2477530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477530 prefixEnd_2477530 := by exact prefixLift 2477530
  have htrace : WordTrace (prefixWord ++ tailWord_2477530) baseStart_2477530 baseEnd_2477530 := by
    simpa [prefixWord, tailWord_2477530, baseEnd_2477530] using wordTrace_append hprefix tailTrace_2477530
  have hstable : (prefixWord ++ tailWord_2477530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477530).length < 2 ^ (prefixWord ++ tailWord_2477530).sum := by decide
  have hdescent : baseEnd_2477530 < baseStart_2477530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477537 : List Nat := [1, 2, 3, 1, 2, 4, 2, 3, 1, 4]
def baseStart_2477537 : Nat := 118140960795 + 2477537 * 2 ^ 59
def prefixEnd_2477537 : Nat := 4983230072969 + 3 ^ 40 * 2477537 * 2
def baseEnd_2477537 : Nat := 424055773432792786264507

theorem tailTrace_2477537 : CollatzResearch.WordTrace tailWord_2477537 prefixEnd_2477537 424055773432792786264507 := by
  unfold tailWord_2477537
  simp only [CollatzResearch.WordTrace]
  refine ⟨90363198025314053477638865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60242132016876035651759243 90363198025314053477638865)
  ·
    refine ⟨67772398518985540108229149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90363198025314053477638865 67772398518985540108229149)
    ·
      refine ⟨25414649444619577540585931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67772398518985540108229149 25414649444619577540585931)
      ·
        refine ⟨38121974166929366310878897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25414649444619577540585931 38121974166929366310878897)
        ·
          refine ⟨28591480625197024733159173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38121974166929366310878897 28591480625197024733159173)
          ·
            refine ⟨5360902617224442137467345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28591480625197024733159173 5360902617224442137467345)
            ·
              refine ⟨4020676962918331603100509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5360902617224442137467345 4020676962918331603100509)
              ·
                refine ⟨1507753861094374351162691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4020676962918331603100509 1507753861094374351162691)
                ·
                  refine ⟨2261630791641561526744037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1507753861094374351162691 2261630791641561526744037)
                  ·
                    refine ⟨424055773432792786264507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2261630791641561526744037 424055773432792786264507)
                    ·
                      rfl

theorem cell23_2477537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_2477537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477537 prefixEnd_2477537 := by exact prefixLift 2477537
  have htrace : WordTrace (prefixWord ++ tailWord_2477537) baseStart_2477537 baseEnd_2477537 := by
    simpa [prefixWord, tailWord_2477537, baseEnd_2477537] using wordTrace_append hprefix tailTrace_2477537
  have hstable : (prefixWord ++ tailWord_2477537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477537).length < 2 ^ (prefixWord ++ tailWord_2477537).sum := by decide
  have hdescent : baseEnd_2477537 < baseStart_2477537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477560 : List Nat := [2, 1, 2, 1, 1, 5, 1, 3, 3, 1, 3]
def baseStart_2477560 : Nat := 118140960795 + 2477560 * 2 ^ 59
def prefixEnd_2477560 : Nat := 4983230072969 + 3 ^ 40 * 2477560 * 2
def baseEnd_2477560 : Nat := 1272179130353431768805915

theorem tailTrace_2477560 : CollatzResearch.WordTrace tailWord_2477560 prefixEnd_2477560 1272179130353431768805915 := by
  unfold tailWord_2477560
  simp only [CollatzResearch.WordTrace]
  refine ⟨45182018452115364202863067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60242691269487152270484089 45182018452115364202863067)
  ·
    refine ⟨67773027678173046304294601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45182018452115364202863067 67773027678173046304294601)
    ·
      refine ⟨50829770758629784728220951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67773027678173046304294601 50829770758629784728220951)
      ·
        refine ⟨76244656137944677092331427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50829770758629784728220951 76244656137944677092331427)
        ·
          refine ⟨114366984206917015638497141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76244656137944677092331427 114366984206917015638497141)
          ·
            refine ⟨10721904769398470216109107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114366984206917015638497141 10721904769398470216109107)
            ·
              refine ⟨16082857154097705324163661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10721904769398470216109107 16082857154097705324163661)
              ·
                refine ⟨6031071432786639496561373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16082857154097705324163661 6031071432786639496561373)
                ·
                  refine ⟨2261651787294989811210515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6031071432786639496561373 2261651787294989811210515)
                  ·
                    refine ⟨3392477680942484716815773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2261651787294989811210515 3392477680942484716815773)
                    ·
                      refine ⟨1272179130353431768805915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3392477680942484716815773 1272179130353431768805915)
                      ·
                        rfl

theorem cell23_2477560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 3, 1, 3].length) (baseStart_2477560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477560 prefixEnd_2477560 := by exact prefixLift 2477560
  have htrace : WordTrace (prefixWord ++ tailWord_2477560) baseStart_2477560 baseEnd_2477560 := by
    simpa [prefixWord, tailWord_2477560, baseEnd_2477560] using wordTrace_append hprefix tailTrace_2477560
  have hstable : (prefixWord ++ tailWord_2477560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477560).length < 2 ^ (prefixWord ++ tailWord_2477560).sum := by decide
  have hdescent : baseEnd_2477560 < baseStart_2477560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477588 : List Nat := [2, 4, 3, 1, 3, 1, 1, 3, 1, 4]
def baseStart_2477588 : Nat := 118140960795 + 2477588 * 2 ^ 59
def prefixEnd_2477588 : Nat := 4983230072969 + 3 ^ 40 * 2477588 * 2
def baseEnd_2477588 : Nat := 424064502603919219751929

theorem tailTrace_2477588 : CollatzResearch.WordTrace tailWord_2477588 prefixEnd_2477588 424064502603919219751929 := by
  unfold tailWord_2477588
  simp only [CollatzResearch.WordTrace]
  refine ⟨45182529074064644593872709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60243372098752859458496945 45182529074064644593872709)
  ·
    refine ⟨8471724201387120861351133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45182529074064644593872709 8471724201387120861351133)
    ·
      refine ⟨3176896575520170323006675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8471724201387120861351133 3176896575520170323006675)
      ·
        refine ⟨4765344863280255484510013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3176896575520170323006675 4765344863280255484510013)
        ·
          refine ⟨1787004323730095806691255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4765344863280255484510013 1787004323730095806691255)
          ·
            refine ⟨2680506485595143710036883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1787004323730095806691255 2680506485595143710036883)
            ·
              refine ⟨4020759728392715565055325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2680506485595143710036883 4020759728392715565055325)
              ·
                refine ⟨1507784898147268336895747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4020759728392715565055325 1507784898147268336895747)
                ·
                  refine ⟨2261677347220902505343621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1507784898147268336895747 2261677347220902505343621)
                  ·
                    refine ⟨424064502603919219751929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2261677347220902505343621 424064502603919219751929)
                    ·
                      rfl

theorem cell23_2477588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_2477588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477588 prefixEnd_2477588 := by exact prefixLift 2477588
  have htrace : WordTrace (prefixWord ++ tailWord_2477588) baseStart_2477588 baseEnd_2477588 := by
    simpa [prefixWord, tailWord_2477588, baseEnd_2477588] using wordTrace_append hprefix tailTrace_2477588
  have hstable : (prefixWord ++ tailWord_2477588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477588).length < 2 ^ (prefixWord ++ tailWord_2477588).sum := by decide
  have hdescent : baseEnd_2477588 < baseStart_2477588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477610 : List Nat := [3, 1, 4, 1, 1, 1, 1, 3, 4, 4]
def baseStart_2477610 : Nat := 118140960795 + 2477610 * 2 ^ 59
def prefixEnd_2477610 : Nat := 4983230072969 + 3 ^ 40 * 2477610 * 2
def baseEnd_2477610 : Nat := 424068268128718857726895

theorem tailTrace_2477610 : CollatzResearch.WordTrace tailWord_2477610 prefixEnd_2477610 424068268128718857726895 := by
  unfold tailWord_2477610
  simp only [CollatzResearch.WordTrace]
  refine ⟨22591465138512396736261571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60243907036033057963364189 22591465138512396736261571)
  ·
    refine ⟨33887197707768595104392357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22591465138512396736261571 33887197707768595104392357)
    ·
      refine ⟨6353849570206611582073567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33887197707768595104392357 6353849570206611582073567)
      ·
        refine ⟨9530774355309917373110351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6353849570206611582073567 9530774355309917373110351)
        ·
          refine ⟨14296161532964876059665527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9530774355309917373110351 14296161532964876059665527)
          ·
            refine ⟨21444242299447314089498291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14296161532964876059665527 21444242299447314089498291)
            ·
              refine ⟨32166363449170971134247437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21444242299447314089498291 32166363449170971134247437)
              ·
                refine ⟨12062386293439114175342789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32166363449170971134247437 12062386293439114175342789)
                ·
                  refine ⟨2261697430019833907876773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12062386293439114175342789 2261697430019833907876773)
                  ·
                    refine ⟨424068268128718857726895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2261697430019833907876773 424068268128718857726895)
                    ·
                      rfl

theorem cell23_2477610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_2477610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477610 prefixEnd_2477610 := by exact prefixLift 2477610
  have htrace : WordTrace (prefixWord ++ tailWord_2477610) baseStart_2477610 baseEnd_2477610 := by
    simpa [prefixWord, tailWord_2477610, baseEnd_2477610] using wordTrace_append hprefix tailTrace_2477610
  have hstable : (prefixWord ++ tailWord_2477610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477610).length < 2 ^ (prefixWord ++ tailWord_2477610).sum := by decide
  have hdescent : baseEnd_2477610 < baseStart_2477610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477623 : List Nat := [1, 1, 3, 1, 2, 5, 2, 8]
def baseStart_2477623 : Nat := 118140960795 + 2477623 * 2 ^ 59
def prefixEnd_2477623 : Nat := 4983230072969 + 3 ^ 40 * 2477623 * 2
def baseEnd_2477623 : Nat := 47118943690172778604375

theorem tailTrace_2477623 : CollatzResearch.WordTrace tailWord_2477623 prefixEnd_2477623 47118943690172778604375 := by
  unfold tailWord_2477623
  simp only [CollatzResearch.WordTrace]
  refine ⟨90366334703002490165269523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60244223135334993443513015 90366334703002490165269523)
  ·
    refine ⟨135549502054503735247904285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90366334703002490165269523 135549502054503735247904285)
    ·
      refine ⟨50831063270438900717964107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135549502054503735247904285 50831063270438900717964107)
      ·
        refine ⟨76246594905658351076946161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50831063270438900717964107 76246594905658351076946161)
        ·
          refine ⟨57184946179243763307709621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76246594905658351076946161 57184946179243763307709621)
          ·
            refine ⟨5361088704304102810097777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57184946179243763307709621 5361088704304102810097777)
            ·
              refine ⟨4020816528228077107573333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5361088704304102810097777 4020816528228077107573333)
              ·
                refine ⟨47118943690172778604375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4020816528228077107573333 47118943690172778604375)
                ·
                  rfl

theorem cell23_2477623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 8].length) (baseStart_2477623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477623 prefixEnd_2477623 := by exact prefixLift 2477623
  have htrace : WordTrace (prefixWord ++ tailWord_2477623) baseStart_2477623 baseEnd_2477623 := by
    simpa [prefixWord, tailWord_2477623, baseEnd_2477623] using wordTrace_append hprefix tailTrace_2477623
  have hstable : (prefixWord ++ tailWord_2477623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477623).length < 2 ^ (prefixWord ++ tailWord_2477623).sum := by decide
  have hdescent : baseEnd_2477623 < baseStart_2477623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477650 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 3, 3, 3]
def baseStart_2477650 : Nat := 118140960795 + 2477650 * 2 ^ 59
def prefixEnd_2477650 : Nat := 4983230072969 + 3 ^ 40 * 2477650 * 2
def baseEnd_2477650 : Nat := 1272225343612336416680501

theorem tailTrace_2477650 : CollatzResearch.WordTrace tailWord_2477650 prefixEnd_2477650 1272225343612336416680501 := by
  unfold tailWord_2477650
  simp only [CollatzResearch.WordTrace]
  refine ⟨22591829868476168444125601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60244879649269782517668269 22591829868476168444125601)
  ·
    refine ⟨16943872401357126333094201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22591829868476168444125601 16943872401357126333094201)
    ·
      refine ⟨12707904301017844749820651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16943872401357126333094201 12707904301017844749820651)
      ·
        refine ⟨19061856451526767124730977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12707904301017844749820651 19061856451526767124730977)
        ·
          refine ⟨14296392338645075343548233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19061856451526767124730977 14296392338645075343548233)
          ·
            refine ⟨10722294253983806507661175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14296392338645075343548233 10722294253983806507661175)
            ·
              refine ⟨16083441380975709761491763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10722294253983806507661175 16083441380975709761491763)
              ·
                refine ⟨24125162071463564642237645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16083441380975709761491763 24125162071463564642237645)
                ·
                  refine ⟨9046935776798836740839117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24125162071463564642237645 9046935776798836740839117)
                  ·
                    refine ⟨3392600916299563777814669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9046935776798836740839117 3392600916299563777814669)
                    ·
                      refine ⟨1272225343612336416680501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3392600916299563777814669 1272225343612336416680501)
                      ·
                        rfl

theorem cell23_2477650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_2477650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477650 prefixEnd_2477650 := by exact prefixLift 2477650
  have htrace : WordTrace (prefixWord ++ tailWord_2477650) baseStart_2477650 baseEnd_2477650 := by
    simpa [prefixWord, tailWord_2477650, baseEnd_2477650] using wordTrace_append hprefix tailTrace_2477650
  have hstable : (prefixWord ++ tailWord_2477650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477650).length < 2 ^ (prefixWord ++ tailWord_2477650).sum := by decide
  have hdescent : baseEnd_2477650 < baseStart_2477650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477661 : List Nat := [1, 4, 4, 2, 1, 1, 2, 2, 2, 4]
def baseStart_2477661 : Nat := 118140960795 + 2477661 * 2 ^ 59
def prefixEnd_2477661 : Nat := 4983230072969 + 3 ^ 40 * 2477661 * 2
def baseEnd_2477661 : Nat := 424076997299845291214317

theorem tailTrace_2477661 : CollatzResearch.WordTrace tailWord_2477661 prefixEnd_2477661 424076997299845291214317 := by
  unfold tailWord_2477661
  simp only [CollatzResearch.WordTrace]
  refine ⟨90367720676864822655152837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60245147117909881770101891 90367720676864822655152837)
  ·
    refine ⟨16943947626912154247841157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90367720676864822655152837 16943947626912154247841157)
    ·
      refine ⟨3176990180046028921470217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16943947626912154247841157 3176990180046028921470217)
      ·
        refine ⟨2382742635034521691102663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3176990180046028921470217 2382742635034521691102663)
        ·
          refine ⟨3574113952551782536653995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2382742635034521691102663 3574113952551782536653995)
          ·
            refine ⟨5361170928827673804980993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3574113952551782536653995 5361170928827673804980993)
            ·
              refine ⟨4020878196620755353735745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5361170928827673804980993 4020878196620755353735745)
              ·
                refine ⟨3015658647465566515301809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4020878196620755353735745 3015658647465566515301809)
                ·
                  refine ⟨2261743985599174886476357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3015658647465566515301809 2261743985599174886476357)
                  ·
                    refine ⟨424076997299845291214317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2261743985599174886476357 424076997299845291214317)
                    ·
                      rfl

theorem cell23_2477661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_2477661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477661 prefixEnd_2477661 := by exact prefixLift 2477661
  have htrace : WordTrace (prefixWord ++ tailWord_2477661) baseStart_2477661 baseEnd_2477661 := by
    simpa [prefixWord, tailWord_2477661, baseEnd_2477661] using wordTrace_append hprefix tailTrace_2477661
  have hstable : (prefixWord ++ tailWord_2477661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477661).length < 2 ^ (prefixWord ++ tailWord_2477661).sum := by decide
  have hdescent : baseEnd_2477661 < baseStart_2477661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477667 : List Nat := [1, 1, 1, 5, 1, 3, 1, 4, 2, 1, 3]
def baseStart_2477667 : Nat := 118140960795 + 2477667 * 2 ^ 59
def prefixEnd_2477667 : Nat := 4983230072969 + 3 ^ 40 * 2477667 * 2
def baseEnd_2477667 : Nat := 1272234072783462850167923

theorem tailTrace_2477667 : CollatzResearch.WordTrace tailWord_2477667 prefixEnd_2477667 1272234072783462850167923 := by
  unfold tailWord_2477667
  simp only [CollatzResearch.WordTrace]
  refine ⟨90367939514843085679871255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60245293009895390453247503 90367939514843085679871255)
  ·
    refine ⟨135551909272264628519806883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90367939514843085679871255 135551909272264628519806883)
    ·
      refine ⟨203327863908396942779710325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135551909272264628519806883 203327863908396942779710325)
      ·
        refine ⟨19061987241412213385597843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 203327863908396942779710325 19061987241412213385597843)
        ·
          refine ⟨28592980862118320078396765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19061987241412213385597843 28592980862118320078396765)
          ·
            refine ⟨10722367823294370029398787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28592980862118320078396765 10722367823294370029398787)
            ·
              refine ⟨16083551734941555044098181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10722367823294370029398787 16083551734941555044098181)
              ·
                refine ⟨3015665950301541570768409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16083551734941555044098181 3015665950301541570768409)
                ·
                  refine ⟨2261749462726156178076307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3015665950301541570768409 2261749462726156178076307)
                  ·
                    refine ⟨3392624194089234267114461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2261749462726156178076307 3392624194089234267114461)
                    ·
                      refine ⟨1272234072783462850167923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3392624194089234267114461 1272234072783462850167923)
                      ·
                        rfl

theorem cell23_2477667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_2477667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477667 prefixEnd_2477667 := by exact prefixLift 2477667
  have htrace : WordTrace (prefixWord ++ tailWord_2477667) baseStart_2477667 baseEnd_2477667 := by
    simpa [prefixWord, tailWord_2477667, baseEnd_2477667] using wordTrace_append hprefix tailTrace_2477667
  have hstable : (prefixWord ++ tailWord_2477667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477667).length < 2 ^ (prefixWord ++ tailWord_2477667).sum := by decide
  have hdescent : baseEnd_2477667 < baseStart_2477667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477668 : List Nat := [2, 3, 1, 1, 2, 5, 2, 2, 1, 2, 2]
def baseStart_2477668 : Nat := 118140960795 + 2477668 * 2 ^ 59
def prefixEnd_2477668 : Nat := 4983230072969 + 3 ^ 40 * 2477668 * 2
def baseEnd_2477668 : Nat := 1272234586264117346255419

theorem tailTrace_2477668 : CollatzResearch.WordTrace tailWord_2477668 prefixEnd_2477668 1272234586264117346255419 := by
  unfold tailWord_2477668
  simp only [CollatzResearch.WordTrace]
  refine ⟨45183987993919731425328829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60245317325226308567105105 45183987993919731425328829)
  ·
    refine ⟨16943995497719899284498311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45183987993919731425328829 16943995497719899284498311)
    ·
      refine ⟨25415993246579848926747467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16943995497719899284498311 25415993246579848926747467)
      ·
        refine ⟨38123989869869773390121201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25415993246579848926747467 38123989869869773390121201)
        ·
          refine ⟨28592992402402330042590901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38123989869869773390121201 28592992402402330042590901)
          ·
            refine ⟨2680593037725218441492897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28592992402402330042590901 2680593037725218441492897)
            ·
              refine ⟨2010444778293913831119673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2680593037725218441492897 2010444778293913831119673)
              ·
                refine ⟨1507833583720435373339755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2010444778293913831119673 1507833583720435373339755)
                ·
                  refine ⟨2261750375580653060009633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1507833583720435373339755 2261750375580653060009633)
                  ·
                    refine ⟨1696312781685489795007225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2261750375580653060009633 1696312781685489795007225)
                    ·
                      refine ⟨1272234586264117346255419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1696312781685489795007225 1272234586264117346255419)
                      ·
                        rfl

theorem cell23_2477668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2, 1, 2, 2].length) (baseStart_2477668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477668 prefixEnd_2477668 := by exact prefixLift 2477668
  have htrace : WordTrace (prefixWord ++ tailWord_2477668) baseStart_2477668 baseEnd_2477668 := by
    simpa [prefixWord, tailWord_2477668, baseEnd_2477668] using wordTrace_append hprefix tailTrace_2477668
  have hstable : (prefixWord ++ tailWord_2477668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477668).length < 2 ^ (prefixWord ++ tailWord_2477668).sum := by decide
  have hdescent : baseEnd_2477668 < baseStart_2477668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477673 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 2, 3, 4]
def baseStart_2477673 : Nat := 118140960795 + 2477673 * 2 ^ 59
def prefixEnd_2477673 : Nat := 4983230072969 + 3 ^ 40 * 2477673 * 2
def baseEnd_2477673 : Nat := 1272237153667389826692895

theorem tailTrace_2477673 : CollatzResearch.WordTrace tailWord_2477673 prefixEnd_2477673 1272237153667389826692895 := by
  unfold tailWord_2477673
  simp only [CollatzResearch.WordTrace]
  refine ⟨90368158352821348704589673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60245438901880899136393115 90368158352821348704589673)
  ·
    refine ⟨67776118764616011528442255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90368158352821348704589673 67776118764616011528442255)
    ·
      refine ⟨101664178146924017292663383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67776118764616011528442255 101664178146924017292663383)
      ·
        refine ⟨152496267220386025938995075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101664178146924017292663383 152496267220386025938995075)
        ·
          refine ⟨228744400830579038908492613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152496267220386025938995075 228744400830579038908492613)
          ·
            refine ⟨42889575155733569795342365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 228744400830579038908492613 42889575155733569795342365)
            ·
              refine ⟨16083590683400088673253387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42889575155733569795342365 16083590683400088673253387)
              ·
                refine ⟨24125386025100133009880081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16083590683400088673253387 24125386025100133009880081)
                ·
                  refine ⟨18094039518825099757410061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24125386025100133009880081 18094039518825099757410061)
                  ·
                    refine ⟨6785264819559412409028773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18094039518825099757410061 6785264819559412409028773)
                    ·
                      refine ⟨1272237153667389826692895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6785264819559412409028773 1272237153667389826692895)
                      ·
                        rfl

theorem cell23_2477673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 3, 4].length) (baseStart_2477673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477673 prefixEnd_2477673 := by exact prefixLift 2477673
  have htrace : WordTrace (prefixWord ++ tailWord_2477673) baseStart_2477673 baseEnd_2477673 := by
    simpa [prefixWord, tailWord_2477673, baseEnd_2477673] using wordTrace_append hprefix tailTrace_2477673
  have hstable : (prefixWord ++ tailWord_2477673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477673).length < 2 ^ (prefixWord ++ tailWord_2477673).sum := by decide
  have hdescent : baseEnd_2477673 < baseStart_2477673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477707 : List Nat := [1, 1, 1, 1, 4, 1, 4, 2, 4, 2, 2]
def baseStart_2477707 : Nat := 118140960795 + 2477707 * 2 ^ 59
def prefixEnd_2477707 : Nat := 4983230072969 + 3 ^ 40 * 2477707 * 2
def baseEnd_2477707 : Nat := 1272254612009642693667739

theorem tailTrace_2477707 : CollatzResearch.WordTrace tailWord_2477707 prefixEnd_2477707 1272254612009642693667739 := by
  unfold tailWord_2477707
  simp only [CollatzResearch.WordTrace]
  refine ⟨90369398434698172511327375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60246265623132115007551583 90369398434698172511327375)
  ·
    refine ⟨135554097652047258766991063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90369398434698172511327375 135554097652047258766991063)
    ·
      refine ⟨203331146478070888150486595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135554097652047258766991063 203331146478070888150486595)
      ·
        refine ⟨304996719717106332225729893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203331146478070888150486595 304996719717106332225729893)
        ·
          refine ⟨57186884946957437292324355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 304996719717106332225729893 57186884946957437292324355)
          ·
            refine ⟨85780327420436155938486533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57186884946957437292324355 85780327420436155938486533)
            ·
              refine ⟨16083811391331779238466225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85780327420436155938486533 16083811391331779238466225)
              ·
                refine ⟨12062858543498834428849669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16083811391331779238466225 12062858543498834428849669)
                ·
                  refine ⟨2261785976906031455409313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12062858543498834428849669 2261785976906031455409313)
                  ·
                    refine ⟨1696339482679523591556985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2261785976906031455409313 1696339482679523591556985)
                    ·
                      refine ⟨1272254612009642693667739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1696339482679523591556985 1272254612009642693667739)
                      ·
                        rfl

theorem cell23_2477707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4, 2, 2].length) (baseStart_2477707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477707 prefixEnd_2477707 := by exact prefixLift 2477707
  have htrace : WordTrace (prefixWord ++ tailWord_2477707) baseStart_2477707 baseEnd_2477707 := by
    simpa [prefixWord, tailWord_2477707, baseEnd_2477707] using wordTrace_append hprefix tailTrace_2477707
  have hstable : (prefixWord ++ tailWord_2477707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477707).length < 2 ^ (prefixWord ++ tailWord_2477707).sum := by decide
  have hdescent : baseEnd_2477707 < baseStart_2477707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477720 : List Nat := [2, 1, 2, 4, 1, 2, 1, 2, 2, 2, 4]
def baseStart_2477720 : Nat := 118140960795 + 2477720 * 2 ^ 59
def prefixEnd_2477720 : Nat := 4983230072969 + 3 ^ 40 * 2477720 * 2
def baseEnd_2477720 : Nat := 1272261287258151142805179

theorem tailTrace_2477720 : CollatzResearch.WordTrace tailWord_2477720 prefixEnd_2477720 1272261287258151142805179 := by
  unfold tailWord_2477720
  simp only [CollatzResearch.WordTrace]
  refine ⟨45184936291825537865775307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60246581722434050487700409 45184936291825537865775307)
  ·
    refine ⟨67777404437738306798662961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45184936291825537865775307 67777404437738306798662961)
    ·
      refine ⟨50833053328303730098997221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67777404437738306798662961 50833053328303730098997221)
      ·
        refine ⟨9531197499056949393561979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50833053328303730098997221 9531197499056949393561979)
        ·
          refine ⟨14296796248585424090342969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9531197499056949393561979 14296796248585424090342969)
          ·
            refine ⟨10722597186439068067757227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14296796248585424090342969 10722597186439068067757227)
            ·
              refine ⟨16083895779658602101635841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10722597186439068067757227 16083895779658602101635841)
              ·
                refine ⟨12062921834743951576226881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16083895779658602101635841 12062921834743951576226881)
                ·
                  refine ⟨9047191376057963682170161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12062921834743951576226881 9047191376057963682170161)
                  ·
                    refine ⟨6785393532043472761627621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9047191376057963682170161 6785393532043472761627621)
                    ·
                      refine ⟨1272261287258151142805179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6785393532043472761627621 1272261287258151142805179)
                      ·
                        rfl

theorem cell23_2477720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_2477720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477720 prefixEnd_2477720 := by exact prefixLift 2477720
  have htrace : WordTrace (prefixWord ++ tailWord_2477720) baseStart_2477720 baseEnd_2477720 := by
    simpa [prefixWord, tailWord_2477720, baseEnd_2477720] using wordTrace_append hprefix tailTrace_2477720
  have hstable : (prefixWord ++ tailWord_2477720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477720).length < 2 ^ (prefixWord ++ tailWord_2477720).sum := by decide
  have hdescent : baseEnd_2477720 < baseStart_2477720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477743 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 3, 7]
def baseStart_2477743 : Nat := 118140960795 + 2477743 * 2 ^ 59
def prefixEnd_2477743 : Nat := 4983230072969 + 3 ^ 40 * 2477743 * 2
def baseEnd_2477743 : Nat := 424091032437734850939191

theorem tailTrace_2477743 : CollatzResearch.WordTrace tailWord_2477743 prefixEnd_2477743 424091032437734850939191 := by
  unfold tailWord_2477743
  simp only [CollatzResearch.WordTrace]
  refine ⟨90370711462567750659637883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60247140975045167106425255 90370711462567750659637883)
  ·
    refine ⟨135556067193851625989456825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90370711462567750659637883 135556067193851625989456825)
    ·
      refine ⟨101667050395388719492092619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135556067193851625989456825 101667050395388719492092619)
      ·
        refine ⟨152500575593083079238138929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101667050395388719492092619 152500575593083079238138929)
        ·
          refine ⟨114375431694812309428604197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152500575593083079238138929 114375431694812309428604197)
          ·
            refine ⟨21445393442777308017863287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114375431694812309428604197 21445393442777308017863287)
            ·
              refine ⟨32168090164165962026794931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21445393442777308017863287 32168090164165962026794931)
              ·
                refine ⟨48252135246248943040192397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32168090164165962026794931 48252135246248943040192397)
                ·
                  refine ⟨18094550717343353640072149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48252135246248943040192397 18094550717343353640072149)
                  ·
                    refine ⟨424091032437734850939191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18094550717343353640072149 424091032437734850939191)
                    ·
                      rfl

theorem cell23_2477743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 7].length) (baseStart_2477743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477743 prefixEnd_2477743 := by exact prefixLift 2477743
  have htrace : WordTrace (prefixWord ++ tailWord_2477743) baseStart_2477743 baseEnd_2477743 := by
    simpa [prefixWord, tailWord_2477743, baseEnd_2477743] using wordTrace_append hprefix tailTrace_2477743
  have hstable : (prefixWord ++ tailWord_2477743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477743).length < 2 ^ (prefixWord ++ tailWord_2477743).sum := by decide
  have hdescent : baseEnd_2477743 < baseStart_2477743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477760 : List Nat := [2, 1, 1, 2, 4, 1, 2, 3, 2, 5]
def baseStart_2477760 : Nat := 118140960795 + 2477760 * 2 ^ 59
def prefixEnd_2477760 : Nat := 4983230072969 + 3 ^ 40 * 2477760 * 2
def baseEnd_2477760 : Nat := 424093942161443662101665

theorem tailTrace_2477760 : CollatzResearch.WordTrace tailWord_2477760 prefixEnd_2477760 424093942161443662101665 := by
  unfold tailWord_2477760
  simp only [CollatzResearch.WordTrace]
  refine ⟨45185665751753081281503367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60247554335670775042004489 45185665751753081281503367)
  ·
    refine ⟨67778498627629621922255051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45185665751753081281503367 67778498627629621922255051)
    ·
      refine ⟨101667747941444432883382577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67778498627629621922255051 101667747941444432883382577)
      ·
        refine ⟨76250810956083324662536933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101667747941444432883382577 76250810956083324662536933)
        ·
          refine ⟨14297027054265623374225675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76250810956083324662536933 14297027054265623374225675)
          ·
            refine ⟨21445540581398435061338513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14297027054265623374225675 21445540581398435061338513)
            ·
              refine ⟨16084155436048826296003885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21445540581398435061338513 16084155436048826296003885)
              ·
                refine ⟨6031558288518309861001457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16084155436048826296003885 6031558288518309861001457)
                ·
                  refine ⟨4523668716388732395751093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6031558288518309861001457 4523668716388732395751093)
                  ·
                    refine ⟨424093942161443662101665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4523668716388732395751093 424093942161443662101665)
                    ·
                      rfl

theorem cell23_2477760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 2, 5].length) (baseStart_2477760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477760 prefixEnd_2477760 := by exact prefixLift 2477760
  have htrace : WordTrace (prefixWord ++ tailWord_2477760) baseStart_2477760 baseEnd_2477760 := by
    simpa [prefixWord, tailWord_2477760, baseEnd_2477760] using wordTrace_append hprefix tailTrace_2477760
  have hstable : (prefixWord ++ tailWord_2477760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477760).length < 2 ^ (prefixWord ++ tailWord_2477760).sum := by decide
  have hdescent : baseEnd_2477760 < baseStart_2477760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477797 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 1, 6, 2]
def baseStart_2477797 : Nat := 118140960795 + 2477797 * 2 ^ 59
def prefixEnd_2477797 : Nat := 4983230072969 + 3 ^ 40 * 2477797 * 2
def baseEnd_2477797 : Nat := 1272300825268547341542325

theorem tailTrace_2477797 : CollatzResearch.WordTrace tailWord_2477797 prefixEnd_2477797 1272300825268547341542325 := by
  unfold tailWord_2477797
  simp only [CollatzResearch.WordTrace]
  refine ⟨90372681004372117882103645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60248454002914745254735763 90372681004372117882103645)
  ·
    refine ⟨33889755376639544205788867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90372681004372117882103645 33889755376639544205788867)
    ·
      refine ⟨50834633064959316308683301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33889755376639544205788867 50834633064959316308683301)
      ·
        refine ⟨9531493699679871807878119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50834633064959316308683301 9531493699679871807878119)
        ·
          refine ⟨14297240549519807711817179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9531493699679871807878119 14297240549519807711817179)
          ·
            refine ⟨21445860824279711567725769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14297240549519807711817179 21445860824279711567725769)
            ·
              refine ⟨16084395618209783675794327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21445860824279711567725769 16084395618209783675794327)
              ·
                refine ⟨24126593427314675513691491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16084395618209783675794327 24126593427314675513691491)
                ·
                  refine ⟨36189890140972013270537237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24126593427314675513691491 36189890140972013270537237)
                  ·
                    refine ⟨1696401100358063122056433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 36189890140972013270537237 1696401100358063122056433)
                    ·
                      refine ⟨1272300825268547341542325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1696401100358063122056433 1272300825268547341542325)
                      ·
                        rfl

theorem cell23_2477797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_2477797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477797 prefixEnd_2477797 := by exact prefixLift 2477797
  have htrace : WordTrace (prefixWord ++ tailWord_2477797) baseStart_2477797 baseEnd_2477797 := by
    simpa [prefixWord, tailWord_2477797, baseEnd_2477797] using wordTrace_append hprefix tailTrace_2477797
  have hstable : (prefixWord ++ tailWord_2477797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477797).length < 2 ^ (prefixWord ++ tailWord_2477797).sum := by decide
  have hdescent : baseEnd_2477797 < baseStart_2477797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477814 : List Nat := [5, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4]
def baseStart_2477814 : Nat := 118140960795 + 2477814 * 2 ^ 59
def prefixEnd_2477814 : Nat := 4983230072969 + 3 ^ 40 * 2477814 * 2
def baseEnd_2477814 : Nat := 1272309554439673775029747

theorem tailTrace_2477814 : CollatzResearch.WordTrace tailWord_2477814 prefixEnd_2477814 1272309554439673775029747 := by
  unfold tailWord_2477814
  simp only [CollatzResearch.WordTrace]
  refine ⟨5648331315331908111592031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60248867363540353190314997 5648331315331908111592031)
  ·
    refine ⟨8472496972997862167388047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5648331315331908111592031 8472496972997862167388047)
    ·
      refine ⟨12708745459496793251082071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8472496972997862167388047 12708745459496793251082071)
      ·
        refine ⟨19063118189245189876623107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12708745459496793251082071 19063118189245189876623107)
        ·
          refine ⟨28594677283867784814934661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19063118189245189876623107 28594677283867784814934661)
          ·
            refine ⟨5361501990725209652800249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28594677283867784814934661 5361501990725209652800249)
            ·
              refine ⟨4021126493043907239600187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5361501990725209652800249 4021126493043907239600187)
              ·
                refine ⟨6031689739565860859400281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4021126493043907239600187 6031689739565860859400281)
                ·
                  refine ⟨4523767304674395644550211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6031689739565860859400281 4523767304674395644550211)
                  ·
                    refine ⟨6785650957011593466825317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4523767304674395644550211 6785650957011593466825317)
                    ·
                      refine ⟨1272309554439673775029747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6785650957011593466825317 1272309554439673775029747)
                      ·
                        rfl

theorem cell23_2477814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_2477814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477814 prefixEnd_2477814 := by exact prefixLift 2477814
  have htrace : WordTrace (prefixWord ++ tailWord_2477814) baseStart_2477814 baseEnd_2477814 := by
    simpa [prefixWord, tailWord_2477814, baseEnd_2477814] using wordTrace_append hprefix tailTrace_2477814
  have hstable : (prefixWord ++ tailWord_2477814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477814).length < 2 ^ (prefixWord ++ tailWord_2477814).sum := by decide
  have hdescent : baseEnd_2477814 < baseStart_2477814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477864 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_2477864 : Nat := 118140960795 + 2477864 * 2 ^ 59
def prefixEnd_2477864 : Nat := 4983230072969 + 3 ^ 40 * 2477864 * 2
def baseEnd_2477864 : Nat := 1272335228472398579404517

theorem tailTrace_2477864 : CollatzResearch.WordTrace tailWord_2477864 prefixEnd_2477864 1272335228472398579404517 := by
  unfold tailWord_2477864
  simp only [CollatzResearch.WordTrace]
  refine ⟨45187562347564694162396323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60250083130086258883195097 45187562347564694162396323)
  ·
    refine ⟨67781343521347041243594485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45187562347564694162396323 67781343521347041243594485)
    ·
      refine ⟨6354500955126285116586983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67781343521347041243594485 6354500955126285116586983)
      ·
        refine ⟨9531751432689427674880475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6354500955126285116586983 9531751432689427674880475)
        ·
          refine ⟨14297627149034141512320713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9531751432689427674880475 14297627149034141512320713)
          ·
            refine ⟨10723220361775606134240535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14297627149034141512320713 10723220361775606134240535)
            ·
              refine ⟨16084830542663409201360803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10723220361775606134240535 16084830542663409201360803)
              ·
                refine ⟨24127245813995113802041205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16084830542663409201360803 24127245813995113802041205)
                ·
                  refine ⟨2261929295062041918941363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24127245813995113802041205 2261929295062041918941363)
                  ·
                    refine ⟨3392893942593062878412045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2261929295062041918941363 3392893942593062878412045)
                    ·
                      refine ⟨1272335228472398579404517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3392893942593062878412045 1272335228472398579404517)
                      ·
                        rfl

theorem cell23_2477864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_2477864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477864 prefixEnd_2477864 := by exact prefixLift 2477864
  have htrace : WordTrace (prefixWord ++ tailWord_2477864) baseStart_2477864 baseEnd_2477864 := by
    simpa [prefixWord, tailWord_2477864, baseEnd_2477864] using wordTrace_append hprefix tailTrace_2477864
  have hstable : (prefixWord ++ tailWord_2477864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477864).length < 2 ^ (prefixWord ++ tailWord_2477864).sum := by decide
  have hdescent : baseEnd_2477864 < baseStart_2477864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477874 : List Nat := [3, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2]
def baseStart_2477874 : Nat := 118140960795 + 2477874 * 2 ^ 59
def prefixEnd_2477874 : Nat := 4983230072969 + 3 ^ 40 * 2477874 * 2
def baseEnd_2477874 : Nat := 1272340363278943540279471

theorem tailTrace_2477874 : CollatzResearch.WordTrace tailWord_2477874 prefixEnd_2477874 1272340363278943540279471 := by
  unfold tailWord_2477874
  simp only [CollatzResearch.WordTrace]
  refine ⟨22593872356273290008164169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60250326283395440021771117 22593872356273290008164169)
  ·
    refine ⟨16945404267204967506123127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22593872356273290008164169 16945404267204967506123127)
    ·
      refine ⟨25418106400807451259184691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16945404267204967506123127 25418106400807451259184691)
      ·
        refine ⟨38127159601211176888777037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25418106400807451259184691 38127159601211176888777037)
        ·
          refine ⟨14297684850454191333291389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38127159601211176888777037 14297684850454191333291389)
          ·
            refine ⟨5361631818920321749984271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14297684850454191333291389 5361631818920321749984271)
            ·
              refine ⟨8042447728380482624976407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5361631818920321749984271 8042447728380482624976407)
              ·
                refine ⟨12063671592570723937464611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8042447728380482624976407 12063671592570723937464611)
                ·
                  refine ⟨18095507388856085906196917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12063671592570723937464611 18095507388856085906196917)
                  ·
                    refine ⟨1696453817705258053705961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18095507388856085906196917 1696453817705258053705961)
                    ·
                      refine ⟨1272340363278943540279471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1696453817705258053705961 1272340363278943540279471)
                      ·
                        rfl

theorem cell23_2477874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2].length) (baseStart_2477874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477874 prefixEnd_2477874 := by exact prefixLift 2477874
  have htrace : WordTrace (prefixWord ++ tailWord_2477874) baseStart_2477874 baseEnd_2477874 := by
    simpa [prefixWord, tailWord_2477874, baseEnd_2477874] using wordTrace_append hprefix tailTrace_2477874
  have hstable : (prefixWord ++ tailWord_2477874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477874).length < 2 ^ (prefixWord ++ tailWord_2477874).sum := by decide
  have hdescent : baseEnd_2477874 < baseStart_2477874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477884 : List Nat := [2, 2, 2, 2, 1, 1, 6, 1, 1, 5]
def baseStart_2477884 : Nat := 118140960795 + 2477884 * 2 ^ 59
def prefixEnd_2477884 : Nat := 4983230072969 + 3 ^ 40 * 2477884 * 2
def baseEnd_2477884 : Nat := 424115166028496167051475

theorem tailTrace_2477884 : CollatzResearch.WordTrace tailWord_2477884 prefixEnd_2477884 424115166028496167051475 := by
  unfold tailWord_2477884
  simp only [CollatzResearch.WordTrace]
  refine ⟨45187927077528465870260353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60250569436704621160347137 45187927077528465870260353)
  ·
    refine ⟨33890945308146349402695265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45187927077528465870260353 33890945308146349402695265)
    ·
      refine ⟨25418208981109762052021449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33890945308146349402695265 25418208981109762052021449)
      ·
        refine ⟨19063656735832321539016087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25418208981109762052021449 19063656735832321539016087)
        ·
          refine ⟨28595485103748482308524131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19063656735832321539016087 28595485103748482308524131)
          ·
            refine ⟨42893227655622723462786197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28595485103748482308524131 42893227655622723462786197)
            ·
              refine ⟨2010620046357315162318103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42893227655622723462786197 2010620046357315162318103)
              ·
                refine ⟨3015930069535972743477155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2010620046357315162318103 3015930069535972743477155)
                ·
                  refine ⟨4523895104303959115215733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3015930069535972743477155 4523895104303959115215733)
                  ·
                    refine ⟨424115166028496167051475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4523895104303959115215733 424115166028496167051475)
                    ·
                      rfl

theorem cell23_2477884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_2477884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477884 prefixEnd_2477884 := by exact prefixLift 2477884
  have htrace : WordTrace (prefixWord ++ tailWord_2477884) baseStart_2477884 baseEnd_2477884 := by
    simpa [prefixWord, tailWord_2477884, baseEnd_2477884] using wordTrace_append hprefix tailTrace_2477884
  have hstable : (prefixWord ++ tailWord_2477884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477884).length < 2 ^ (prefixWord ++ tailWord_2477884).sum := by decide
  have hdescent : baseEnd_2477884 < baseStart_2477884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477897 : List Nat := [1, 2, 1, 1, 2, 4, 3, 1, 4, 4]
def baseStart_2477897 : Nat := 118140960795 + 2477897 * 2 ^ 59
def prefixEnd_2477897 : Nat := 4983230072969 + 3 ^ 40 * 2477897 * 2
def baseEnd_2477897 : Nat := 424117391111332316763955

theorem tailTrace_2477897 : CollatzResearch.WordTrace tailWord_2477897 prefixEnd_2477897 424117391111332316763955 := by
  unfold tailWord_2477897
  simp only [CollatzResearch.WordTrace]
  refine ⟨90376328304009834960743945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60250885536006556640495963 90376328304009834960743945)
  ·
    refine ⟨67782246228007376220557959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90376328304009834960743945 67782246228007376220557959)
    ·
      refine ⟨101673369342011064330836939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67782246228007376220557959 101673369342011064330836939)
      ·
        refine ⟨152510054013016596496255409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101673369342011064330836939 152510054013016596496255409)
        ·
          refine ⟨114382540509762447372191557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152510054013016596496255409 114382540509762447372191557)
          ·
            refine ⟨21446726345580458882285917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114382540509762447372191557 21446726345580458882285917)
            ·
              refine ⟨8042522379592672080857219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21446726345580458882285917 8042522379592672080857219)
              ·
                refine ⟨12063783569389008121285829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8042522379592672080857219 12063783569389008121285829)
                ·
                  refine ⟨2261959419260439022741093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12063783569389008121285829 2261959419260439022741093)
                  ·
                    refine ⟨424117391111332316763955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2261959419260439022741093 424117391111332316763955)
                    ·
                      rfl

theorem cell23_2477897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4, 4].length) (baseStart_2477897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477897 prefixEnd_2477897 := by exact prefixLift 2477897
  have htrace : WordTrace (prefixWord ++ tailWord_2477897) baseStart_2477897 baseEnd_2477897 := by
    simpa [prefixWord, tailWord_2477897, baseEnd_2477897] using wordTrace_append hprefix tailTrace_2477897
  have hstable : (prefixWord ++ tailWord_2477897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477897).length < 2 ^ (prefixWord ++ tailWord_2477897).sum := by decide
  have hdescent : baseEnd_2477897 < baseStart_2477897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477937 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 3, 3, 3]
def baseStart_2477937 : Nat := 118140960795 + 2477937 * 2 ^ 59
def prefixEnd_2477937 : Nat := 4983230072969 + 3 ^ 40 * 2477937 * 2
def baseEnd_2477937 : Nat := 1272372712560176793791681

theorem tailTrace_2477937 : CollatzResearch.WordTrace tailWord_2477937 prefixEnd_2477937 1272372712560176793791681 := by
  unfold tailWord_2477937
  simp only [CollatzResearch.WordTrace]
  refine ⟨90377787223864921792200065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60251858149243281194800043 90377787223864921792200065)
  ·
    refine ⟨67783340417898691344150049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90377787223864921792200065 67783340417898691344150049)
    ·
      refine ⟨50837505313424018508112537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67783340417898691344150049 50837505313424018508112537)
      ·
        refine ⟨38128128985068013881084403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50837505313424018508112537 38128128985068013881084403)
        ·
          refine ⟨57192193477602020821626605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38128128985068013881084403 57192193477602020821626605)
          ·
            refine ⟨21447072554100757808109977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57192193477602020821626605 21447072554100757808109977)
            ·
              refine ⟨16085304415575568356082483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21447072554100757808109977 16085304415575568356082483)
              ·
                refine ⟨24127956623363352534123725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16085304415575568356082483 24127956623363352534123725)
                ·
                  refine ⟨9047983733761257200296397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24127956623363352534123725 9047983733761257200296397)
                  ·
                    refine ⟨3392993900160471450111149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9047983733761257200296397 3392993900160471450111149)
                    ·
                      refine ⟨1272372712560176793791681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3392993900160471450111149 1272372712560176793791681)
                      ·
                        rfl

theorem cell23_2477937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_2477937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477937 prefixEnd_2477937 := by exact prefixLift 2477937
  have htrace : WordTrace (prefixWord ++ tailWord_2477937) baseStart_2477937 baseEnd_2477937 := by
    simpa [prefixWord, tailWord_2477937, baseEnd_2477937] using wordTrace_append hprefix tailTrace_2477937
  have hstable : (prefixWord ++ tailWord_2477937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477937).length < 2 ^ (prefixWord ++ tailWord_2477937).sum := by decide
  have hdescent : baseEnd_2477937 < baseStart_2477937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477955 : List Nat := [1, 1, 1, 3, 4, 3, 3, 2, 1, 2, 2]
def baseStart_2477955 : Nat := 118140960795 + 2477955 * 2 ^ 59
def prefixEnd_2477955 : Nat := 4983230072969 + 3 ^ 40 * 2477955 * 2
def baseEnd_2477955 : Nat := 1272381955211957723366599

theorem tailTrace_2477955 : CollatzResearch.WordTrace tailWord_2477955 prefixEnd_2477955 1272381955211957723366599 := by
  unfold tailWord_2477955
  simp only [CollatzResearch.WordTrace]
  refine ⟨90378443737799710866355319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60252295825199807244236879 90378443737799710866355319)
  ·
    refine ⟨135567665606699566299532979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90378443737799710866355319 135567665606699566299532979)
    ·
      refine ⟨203351498410049349449299469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135567665606699566299532979 203351498410049349449299469)
      ·
        refine ⟨76256811903768506043487301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203351498410049349449299469 76256811903768506043487301)
        ·
          refine ⟨14298152231956594883153869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76256811903768506043487301 14298152231956594883153869)
          ·
            refine ⟨5361807086983723081182701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14298152231956594883153869 5361807086983723081182701)
            ·
              refine ⟨2010677657618896155443513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5361807086983723081182701 2010677657618896155443513)
              ·
                refine ⟨1508008243214172116582635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2010677657618896155443513 1508008243214172116582635)
                ·
                  refine ⟨2262012364821258174873953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1508008243214172116582635 2262012364821258174873953)
                  ·
                    refine ⟨1696509273615943631155465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2262012364821258174873953 1696509273615943631155465)
                    ·
                      refine ⟨1272381955211957723366599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1696509273615943631155465 1272381955211957723366599)
                      ·
                        rfl

theorem cell23_2477955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2, 1, 2, 2].length) (baseStart_2477955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477955 prefixEnd_2477955 := by exact prefixLift 2477955
  have htrace : WordTrace (prefixWord ++ tailWord_2477955) baseStart_2477955 baseEnd_2477955 := by
    simpa [prefixWord, tailWord_2477955, baseEnd_2477955] using wordTrace_append hprefix tailTrace_2477955
  have hstable : (prefixWord ++ tailWord_2477955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477955).length < 2 ^ (prefixWord ++ tailWord_2477955).sum := by decide
  have hdescent : baseEnd_2477955 < baseStart_2477955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477964 : List Nat := [2, 2, 1, 2, 1, 2, 1, 4, 3, 3, 2]
def baseStart_2477964 : Nat := 118140960795 + 2477964 * 2 ^ 59
def prefixEnd_2477964 : Nat := 4983230072969 + 3 ^ 40 * 2477964 * 2
def baseEnd_2477964 : Nat := 1272386576537848188154057

theorem tailTrace_2477964 : CollatzResearch.WordTrace tailWord_2477964 prefixEnd_2477964 1272386576537848188154057 := by
  unfold tailWord_2477964
  simp only [CollatzResearch.WordTrace]
  refine ⟨45189385997383552701716473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60252514663178070268955297 45189385997383552701716473)
  ·
    refine ⟨33892039498037664526287355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45189385997383552701716473 33892039498037664526287355)
    ·
      refine ⟨50838059247056496789431033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33892039498037664526287355 50838059247056496789431033)
      ·
        refine ⟨38128544435292372592073275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50838059247056496789431033 38128544435292372592073275)
        ·
          refine ⟨57192816652938558888109913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38128544435292372592073275 57192816652938558888109913)
          ·
            refine ⟨42894612489703919166082435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57192816652938558888109913 42894612489703919166082435)
            ·
              refine ⟨64341918734555878749123653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42894612489703919166082435 64341918734555878749123653)
              ·
                refine ⟨12064109762729227265460685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64341918734555878749123653 12064109762729227265460685)
                ·
                  refine ⟨4524041161023460224547757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12064109762729227265460685 4524041161023460224547757)
                  ·
                    refine ⟨1696515435383797584205409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4524041161023460224547757 1696515435383797584205409)
                    ·
                      refine ⟨1272386576537848188154057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1696515435383797584205409 1272386576537848188154057)
                      ·
                        rfl

theorem cell23_2477964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 3, 3, 2].length) (baseStart_2477964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477964 prefixEnd_2477964 := by exact prefixLift 2477964
  have htrace : WordTrace (prefixWord ++ tailWord_2477964) baseStart_2477964 baseEnd_2477964 := by
    simpa [prefixWord, tailWord_2477964, baseEnd_2477964] using wordTrace_append hprefix tailTrace_2477964
  have hstable : (prefixWord ++ tailWord_2477964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477964).length < 2 ^ (prefixWord ++ tailWord_2477964).sum := by decide
  have hdescent : baseEnd_2477964 < baseStart_2477964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477981 : List Nat := [1, 4, 2, 1, 2, 3, 1, 1, 3, 3, 2]
def baseStart_2477981 : Nat := 118140960795 + 2477981 * 2 ^ 59
def prefixEnd_2477981 : Nat := 4983230072969 + 3 ^ 40 * 2477981 * 2
def baseEnd_2477981 : Nat := 1272395305708974621641479

theorem tailTrace_2477981 : CollatzResearch.WordTrace tailWord_2477981 prefixEnd_2477981 1272395305708974621641479 := by
  unfold tailWord_2477981
  simp only [CollatzResearch.WordTrace]
  refine ⟨90379392035705517306801797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60252928023803678204534531 90379392035705517306801797)
  ·
    refine ⟨16946136006694784495025337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90379392035705517306801797 16946136006694784495025337)
    ·
      refine ⟨12709602005021088371269003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16946136006694784495025337 12709602005021088371269003)
      ·
        refine ⟨19064403007531632556903505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12709602005021088371269003 19064403007531632556903505)
        ·
          refine ⟨14298302255648724417677629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19064403007531632556903505 14298302255648724417677629)
          ·
            refine ⟨5361863345868271656629111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14298302255648724417677629 5361863345868271656629111)
            ·
              refine ⟨8042795018802407484943667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5361863345868271656629111 8042795018802407484943667)
              ·
                refine ⟨12064192528203611227415501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8042795018802407484943667 12064192528203611227415501)
                ·
                  refine ⟨4524072198076354210280813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12064192528203611227415501 4524072198076354210280813)
                  ·
                    refine ⟨1696527074278632828855305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4524072198076354210280813 1696527074278632828855305)
                    ·
                      refine ⟨1272395305708974621641479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1696527074278632828855305 1272395305708974621641479)
                      ·
                        rfl

theorem cell23_2477981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_2477981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2477981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2477981 prefixEnd_2477981 := by exact prefixLift 2477981
  have htrace : WordTrace (prefixWord ++ tailWord_2477981) baseStart_2477981 baseEnd_2477981 := by
    simpa [prefixWord, tailWord_2477981, baseEnd_2477981] using wordTrace_append hprefix tailTrace_2477981
  have hstable : (prefixWord ++ tailWord_2477981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477981).length < 2 ^ (prefixWord ++ tailWord_2477981).sum := by decide
  have hdescent : baseEnd_2477981 < baseStart_2477981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478007 : List Nat := [1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 4]
def baseStart_2478007 : Nat := 118140960795 + 2478007 * 2 ^ 59
def prefixEnd_2478007 : Nat := 4983230072969 + 3 ^ 40 * 2478007 * 2
def baseEnd_2478007 : Nat := 1272408656205991519916359

theorem tailTrace_2478007 : CollatzResearch.WordTrace tailWord_2478007 prefixEnd_2478007 1272408656205991519916359 := by
  unfold tailWord_2478007
  simp only [CollatzResearch.WordTrace]
  refine ⟨90380340333611323747248275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60253560222407549164832183 90380340333611323747248275)
  ·
    refine ⟨135570510500416985620872413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90380340333611323747248275 135570510500416985620872413)
    ·
      refine ⟨50838941437656369607827155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135570510500416985620872413 50838941437656369607827155)
      ·
        refine ⟨76258412156484554411740733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50838941437656369607827155 76258412156484554411740733)
        ·
          refine ⟨28596904558681707904402775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76258412156484554411740733 28596904558681707904402775)
          ·
            refine ⟨42895356838022561856604163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28596904558681707904402775 42895356838022561856604163)
            ·
              refine ⟨64343035257033842784906245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42895356838022561856604163 64343035257033842784906245)
              ·
                refine ⟨12064319110693845522169921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64343035257033842784906245 12064319110693845522169921)
                ·
                  refine ⟨9048239333020384141627441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12064319110693845522169921 9048239333020384141627441)
                  ·
                    refine ⟨6786179499765288106220581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9048239333020384141627441 6786179499765288106220581)
                    ·
                      refine ⟨1272408656205991519916359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6786179499765288106220581 1272408656205991519916359)
                      ·
                        rfl

theorem cell23_2478007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_2478007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478007 prefixEnd_2478007 := by exact prefixLift 2478007
  have htrace : WordTrace (prefixWord ++ tailWord_2478007) baseStart_2478007 baseEnd_2478007 := by
    simpa [prefixWord, tailWord_2478007, baseEnd_2478007] using wordTrace_append hprefix tailTrace_2478007
  have hstable : (prefixWord ++ tailWord_2478007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478007).length < 2 ^ (prefixWord ++ tailWord_2478007).sum := by decide
  have hdescent : baseEnd_2478007 < baseStart_2478007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478011 : List Nat := [1, 1, 1, 1, 1, 2, 2, 8, 2, 2, 2]
def baseStart_2478011 : Nat := 118140960795 + 2478011 * 2 ^ 59
def prefixEnd_2478011 : Nat := 4983230072969 + 3 ^ 40 * 2478011 * 2
def baseEnd_2478011 : Nat := 1272410710128609504266341

theorem tailTrace_2478011 : CollatzResearch.WordTrace tailWord_2478011 prefixEnd_2478011 1272410710128609504266341 := by
  unfold tailWord_2478011
  simp only [CollatzResearch.WordTrace]
  refine ⟨90380486225596832430393887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60253657483731221620262591 90380486225596832430393887)
  ·
    refine ⟨135570729338395248645590831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90380486225596832430393887 135570729338395248645590831)
    ·
      refine ⟨203356094007592872968386247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135570729338395248645590831 203356094007592872968386247)
      ·
        refine ⟨305034141011389309452579371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203356094007592872968386247 305034141011389309452579371)
        ·
          refine ⟨457551211517083964178869057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305034141011389309452579371 457551211517083964178869057)
          ·
            refine ⟨343163408637812973134151793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 457551211517083964178869057 343163408637812973134151793)
            ·
              refine ⟨257372556478359729850613845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 343163408637812973134151793 257372556478359729850613845)
              ·
                refine ⟨3016084646230778084186881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 257372556478359729850613845 3016084646230778084186881)
                ·
                  refine ⟨2262063484673083563140161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3016084646230778084186881 2262063484673083563140161)
                  ·
                    refine ⟨1696547613504812672355121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2262063484673083563140161 1696547613504812672355121)
                    ·
                      refine ⟨1272410710128609504266341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1696547613504812672355121 1272410710128609504266341)
                      ·
                        rfl

theorem cell23_2478011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2, 2, 2].length) (baseStart_2478011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478011 prefixEnd_2478011 := by exact prefixLift 2478011
  have htrace : WordTrace (prefixWord ++ tailWord_2478011) baseStart_2478011 baseEnd_2478011 := by
    simpa [prefixWord, tailWord_2478011, baseEnd_2478011] using wordTrace_append hprefix tailTrace_2478011
  have hstable : (prefixWord ++ tailWord_2478011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478011).length < 2 ^ (prefixWord ++ tailWord_2478011).sum := by decide
  have hdescent : baseEnd_2478011 < baseStart_2478011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478014 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3]
def baseStart_2478014 : Nat := 118140960795 + 2478014 * 2 ^ 59
def prefixEnd_2478014 : Nat := 4983230072969 + 3 ^ 40 * 2478014 * 2
def baseEnd_2478014 : Nat := 1272412250570572992528827

theorem tailTrace_2478014 : CollatzResearch.WordTrace tailWord_2478014 prefixEnd_2478014 1272412250570572992528827 := by
  unfold tailWord_2478014
  simp only [CollatzResearch.WordTrace]
  refine ⟨11297574455573245492844137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60253730429723975961835397 11297574455573245492844137)
  ·
    refine ⟨8473180841679934119633103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11297574455573245492844137 8473180841679934119633103)
    ·
      refine ⟨12709771262519901179449655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8473180841679934119633103 12709771262519901179449655)
      ·
        refine ⟨19064656893779851769174483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12709771262519901179449655 19064656893779851769174483)
        ·
          refine ⟨28596985340669777653761725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19064656893779851769174483 28596985340669777653761725)
          ·
            refine ⟨10723869502751166620160647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28596985340669777653761725 10723869502751166620160647)
            ·
              refine ⟨16085804254126749930240971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10723869502751166620160647 16085804254126749930240971)
              ·
                refine ⟨24128706381190124895361457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16085804254126749930240971 24128706381190124895361457)
                ·
                  refine ⟨18096529785892593671521093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24128706381190124895361457 18096529785892593671521093)
                  ·
                    refine ⟨3393099334854861313410205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18096529785892593671521093 3393099334854861313410205)
                    ·
                      refine ⟨1272412250570572992528827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3393099334854861313410205 1272412250570572992528827)
                      ·
                        rfl

theorem cell23_2478014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_2478014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478014 prefixEnd_2478014 := by exact prefixLift 2478014
  have htrace : WordTrace (prefixWord ++ tailWord_2478014) baseStart_2478014 baseEnd_2478014 := by
    simpa [prefixWord, tailWord_2478014, baseEnd_2478014] using wordTrace_append hprefix tailTrace_2478014
  have hstable : (prefixWord ++ tailWord_2478014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478014).length < 2 ^ (prefixWord ++ tailWord_2478014).sum := by decide
  have hdescent : baseEnd_2478014 < baseStart_2478014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478024 : List Nat := [2, 1, 3, 1, 4, 2, 1, 1, 2, 2, 4]
def baseStart_2478024 : Nat := 118140960795 + 2478024 * 2 ^ 59
def prefixEnd_2478024 : Nat := 4983230072969 + 3 ^ 40 * 2478024 * 2
def baseEnd_2478024 : Nat := 1272417385377117953403781

theorem tailTrace_2478024 : CollatzResearch.WordTrace tailWord_2478024 prefixEnd_2478024 1272417385377117953403781 := by
  unfold tailWord_2478024
  simp only [CollatzResearch.WordTrace]
  refine ⟨45190480187274867825308563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60253973583033157100411417 45190480187274867825308563)
  ·
    refine ⟨67785720280912301737962845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45190480187274867825308563 67785720280912301737962845)
    ·
      refine ⟨25419645105342113151736067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67785720280912301737962845 25419645105342113151736067)
      ·
        refine ⟨38129467658013169727604101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25419645105342113151736067 38129467658013169727604101)
        ·
          refine ⟨7149275185877469323925769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38129467658013169727604101 7149275185877469323925769)
          ·
            refine ⟨5361956389408101992944327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7149275185877469323925769 5361956389408101992944327)
            ·
              refine ⟨8042934584112152989416491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5361956389408101992944327 8042934584112152989416491)
              ·
                refine ⟨12064401876168229484124737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8042934584112152989416491 12064401876168229484124737)
                ·
                  refine ⟨9048301407126172113093553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12064401876168229484124737 9048301407126172113093553)
                  ·
                    refine ⟨6786226055344629084820165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9048301407126172113093553 6786226055344629084820165)
                    ·
                      refine ⟨1272417385377117953403781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6786226055344629084820165 1272417385377117953403781)
                      ·
                        rfl

theorem cell23_2478024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_2478024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478024 prefixEnd_2478024 := by exact prefixLift 2478024
  have htrace : WordTrace (prefixWord ++ tailWord_2478024) baseStart_2478024 baseEnd_2478024 := by
    simpa [prefixWord, tailWord_2478024, baseEnd_2478024] using wordTrace_append hprefix tailTrace_2478024
  have hstable : (prefixWord ++ tailWord_2478024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478024).length < 2 ^ (prefixWord ++ tailWord_2478024).sum := by decide
  have hdescent : baseEnd_2478024 < baseStart_2478024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478028 : List Nat := [2, 2, 1, 4, 1, 2, 2, 3, 2, 2, 2]
def baseStart_2478028 : Nat := 118140960795 + 2478028 * 2 ^ 59
def prefixEnd_2478028 : Nat := 4983230072969 + 3 ^ 40 * 2478028 * 2
def baseEnd_2478028 : Nat := 1272419439299735937753763

theorem tailTrace_2478028 : CollatzResearch.WordTrace tailWord_2478028 prefixEnd_2478028 1272419439299735937753763 := by
  unfold tailWord_2478028
  simp only [CollatzResearch.WordTrace]
  refine ⟨45190553133267622166881369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60254070844356829555841825 45190553133267622166881369)
  ·
    refine ⟨33892914849950716625161027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45190553133267622166881369 33892914849950716625161027)
    ·
      refine ⟨50839372274926074937741541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33892914849950716625161027 50839372274926074937741541)
      ·
        refine ⟨9532382301548639050826539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50839372274926074937741541 9532382301548639050826539)
        ·
          refine ⟨14298573452322958576239809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9532382301548639050826539 14298573452322958576239809)
          ·
            refine ⟨10723930089242218932179857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14298573452322958576239809 10723930089242218932179857)
            ·
              refine ⟨8042947566931664199134893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10723930089242218932179857 8042947566931664199134893)
              ·
                refine ⟨3016105337599374074675585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8042947566931664199134893 3016105337599374074675585)
                ·
                  refine ⟨2262079003199530556006689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3016105337599374074675585 2262079003199530556006689)
                  ·
                    refine ⟨1696559252399647917005017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2262079003199530556006689 1696559252399647917005017)
                    ·
                      refine ⟨1272419439299735937753763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1696559252399647917005017 1272419439299735937753763)
                      ·
                        rfl

theorem cell23_2478028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_2478028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478028 prefixEnd_2478028 := by exact prefixLift 2478028
  have htrace : WordTrace (prefixWord ++ tailWord_2478028) baseStart_2478028 baseEnd_2478028 := by
    simpa [prefixWord, tailWord_2478028, baseEnd_2478028] using wordTrace_append hprefix tailTrace_2478028
  have hstable : (prefixWord ++ tailWord_2478028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478028).length < 2 ^ (prefixWord ++ tailWord_2478028).sum := by decide
  have hdescent : baseEnd_2478028 < baseStart_2478028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478051 : List Nat := [1, 1, 1, 6, 1, 3, 2, 3, 5]
def baseStart_2478051 : Nat := 118140960795 + 2478051 * 2 ^ 59
def prefixEnd_2478051 : Nat := 4983230072969 + 3 ^ 40 * 2478051 * 2
def baseEnd_2478051 : Nat := 141381249928309927529573

theorem tailTrace_2478051 : CollatzResearch.WordTrace tailWord_2478051 prefixEnd_2478051 141381249928309927529573 := by
  unfold tailWord_2478051
  simp only [CollatzResearch.WordTrace]
  refine ⟨90381945145451919261850007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60254630096967946174566671 90381945145451919261850007)
  ·
    refine ⟨135572917718177878892775011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90381945145451919261850007 135572917718177878892775011)
    ·
      refine ⟨203359376577266818339162517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135572917718177878892775011 203359376577266818339162517)
      ·
        refine ⟨9532470777059382109648243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 203359376577266818339162517 9532470777059382109648243)
        ·
          refine ⟨14298706165589073164472365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9532470777059382109648243 14298706165589073164472365)
          ·
            refine ⟨5362014812095902436677137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14298706165589073164472365 5362014812095902436677137)
            ·
              refine ⟨4021511109071926827507853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5362014812095902436677137 4021511109071926827507853)
              ·
                refine ⟨1508066665901972560315445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4021511109071926827507853 1508066665901972560315445)
                ·
                  refine ⟨141381249928309927529573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1508066665901972560315445 141381249928309927529573)
                  ·
                    rfl

theorem cell23_2478051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3, 5].length) (baseStart_2478051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478051 prefixEnd_2478051 := by exact prefixLift 2478051
  have htrace : WordTrace (prefixWord ++ tailWord_2478051) baseStart_2478051 baseEnd_2478051 := by
    simpa [prefixWord, tailWord_2478051, baseEnd_2478051] using wordTrace_append hprefix tailTrace_2478051
  have hstable : (prefixWord ++ tailWord_2478051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478051).length < 2 ^ (prefixWord ++ tailWord_2478051).sum := by decide
  have hdescent : baseEnd_2478051 < baseStart_2478051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478104 : List Nat := [2, 1, 2, 3, 2, 1, 1, 3, 1, 4, 3]
def baseStart_2478104 : Nat := 118140960795 + 2478104 * 2 ^ 59
def prefixEnd_2478104 : Nat := 4983230072969 + 3 ^ 40 * 2478104 * 2
def baseEnd_2478104 : Nat := 1272458463829477640403413

theorem tailTrace_2478104 : CollatzResearch.WordTrace tailWord_2478104 prefixEnd_2478104 1272458463829477640403413 := by
  unfold tailWord_2478104
  simp only [CollatzResearch.WordTrace]
  refine ⟨45191939107129954656764683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60255918809506606209019577 45191939107129954656764683)
  ·
    refine ⟨67787908660694931985147025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45191939107129954656764683 67787908660694931985147025)
    ·
      refine ⟨50840931495521198988860269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67787908660694931985147025 50840931495521198988860269)
      ·
        refine ⟨19065349310820449620822601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50840931495521198988860269 19065349310820449620822601)
        ·
          refine ⟨14299011983115337215616951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19065349310820449620822601 14299011983115337215616951)
          ·
            refine ⟨21448517974673005823425427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14299011983115337215616951 21448517974673005823425427)
            ·
              refine ⟨32172776962009508735138141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21448517974673005823425427 32172776962009508735138141)
              ·
                refine ⟨12064791360753565775676803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32172776962009508735138141 12064791360753565775676803)
                ·
                  refine ⟨18097187041130348663515205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12064791360753565775676803 18097187041130348663515205)
                  ·
                    refine ⟨3393222570211940374409101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18097187041130348663515205 3393222570211940374409101)
                    ·
                      refine ⟨1272458463829477640403413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3393222570211940374409101 1272458463829477640403413)
                      ·
                        rfl

theorem cell23_2478104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_2478104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478104 prefixEnd_2478104 := by exact prefixLift 2478104
  have htrace : WordTrace (prefixWord ++ tailWord_2478104) baseStart_2478104 baseEnd_2478104 := by
    simpa [prefixWord, tailWord_2478104, baseEnd_2478104] using wordTrace_append hprefix tailTrace_2478104
  have hstable : (prefixWord ++ tailWord_2478104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478104).length < 2 ^ (prefixWord ++ tailWord_2478104).sum := by decide
  have hdescent : baseEnd_2478104 < baseStart_2478104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478127 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 6]
def baseStart_2478127 : Nat := 118140960795 + 2478127 * 2 ^ 59
def prefixEnd_2478127 : Nat := 4983230072969 + 3 ^ 40 * 2478127 * 2
def baseEnd_2478127 : Nat := 1272470273884531050415807

theorem tailTrace_2478127 : CollatzResearch.WordTrace tailWord_2478127 prefixEnd_2478127 1272470273884531050415807 := by
  unfold tailWord_2478127
  simp only [CollatzResearch.WordTrace]
  refine ⟨90384717093176584241616635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60256478062117722827744423 90384717093176584241616635)
  ·
    refine ⟨135577075639764876362424953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90384717093176584241616635 135577075639764876362424953)
    ·
      refine ⟨101682806729823657271818715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135577075639764876362424953 101682806729823657271818715)
      ·
        refine ⟨152524210094735485907728073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101682806729823657271818715 152524210094735485907728073)
        ·
          refine ⟨114393157571051614430796055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152524210094735485907728073 114393157571051614430796055)
          ·
            refine ⟨171589736356577421646194083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114393157571051614430796055 171589736356577421646194083)
            ·
              refine ⟨257384604534866132469291125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171589736356577421646194083 257384604534866132469291125)
              ·
                refine ⟨24129806675143699918996043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 257384604534866132469291125 24129806675143699918996043)
                ·
                  refine ⟨36194710012715549878494065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24129806675143699918996043 36194710012715549878494065)
                  ·
                    refine ⟨27146032509536662408870549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36194710012715549878494065 27146032509536662408870549)
                    ·
                      refine ⟨1272470273884531050415807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27146032509536662408870549 1272470273884531050415807)
                      ·
                        rfl

theorem cell23_2478127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 6].length) (baseStart_2478127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478127 prefixEnd_2478127 := by exact prefixLift 2478127
  have htrace : WordTrace (prefixWord ++ tailWord_2478127) baseStart_2478127 baseEnd_2478127 := by
    simpa [prefixWord, tailWord_2478127, baseEnd_2478127] using wordTrace_append hprefix tailTrace_2478127
  have hstable : (prefixWord ++ tailWord_2478127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478127).length < 2 ^ (prefixWord ++ tailWord_2478127).sum := by decide
  have hdescent : baseEnd_2478127 < baseStart_2478127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478147 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 7]
def baseStart_2478147 : Nat := 118140960795 + 2478147 * 2 ^ 59
def prefixEnd_2478147 : Nat := 4983230072969 + 3 ^ 40 * 2478147 * 2
def baseEnd_2478147 : Nat := 1272480543497620972165715

theorem tailTrace_2478147 : CollatzResearch.WordTrace tailWord_2478147 prefixEnd_2478147 1272480543497620972165715 := by
  unfold tailWord_2478147
  simp only [CollatzResearch.WordTrace]
  refine ⟨90385446553104127657344695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60256964368736085104896463 90385446553104127657344695)
  ·
    refine ⟨135578169829656191486017043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90385446553104127657344695 135578169829656191486017043)
    ·
      refine ⟨203367254744484287229025565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135578169829656191486017043 203367254744484287229025565)
      ·
        refine ⟨76262720529181607710884587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203367254744484287229025565 76262720529181607710884587)
        ·
          refine ⟨114394080793772411566326881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76262720529181607710884587 114394080793772411566326881)
          ·
            refine ⟨85795560595329308674745161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114394080793772411566326881 85795560595329308674745161)
            ·
              refine ⟨64346670446496981506058871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85795560595329308674745161 64346670446496981506058871)
              ·
                refine ⟨96520005669745472259088307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64346670446496981506058871 96520005669745472259088307)
                ·
                  refine ⟨144780008504618208388632461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96520005669745472259088307 144780008504618208388632461)
                  ·
                    refine ⟨54292503189231828145737173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 144780008504618208388632461 54292503189231828145737173)
                    ·
                      refine ⟨1272480543497620972165715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54292503189231828145737173 1272480543497620972165715)
                      ·
                        rfl

theorem cell23_2478147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_2478147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478147 prefixEnd_2478147 := by exact prefixLift 2478147
  have htrace : WordTrace (prefixWord ++ tailWord_2478147) baseStart_2478147 baseEnd_2478147 := by
    simpa [prefixWord, tailWord_2478147, baseEnd_2478147] using wordTrace_append hprefix tailTrace_2478147
  have hstable : (prefixWord ++ tailWord_2478147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478147).length < 2 ^ (prefixWord ++ tailWord_2478147).sum := by decide
  have hdescent : baseEnd_2478147 < baseStart_2478147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478151 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 5, 1, 3]
def baseStart_2478151 : Nat := 118140960795 + 2478151 * 2 ^ 59
def prefixEnd_2478151 : Nat := 4983230072969 + 3 ^ 40 * 2478151 * 2
def baseEnd_2478151 : Nat := 1272482597420238956515697

theorem tailTrace_2478151 : CollatzResearch.WordTrace tailWord_2478151 prefixEnd_2478151 1272482597420238956515697 := by
  unfold tailWord_2478151
  simp only [CollatzResearch.WordTrace]
  refine ⟨90385592445089636340490307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60257061630059757560326871 90385592445089636340490307)
  ·
    refine ⟨135578388667634454510735461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90385592445089636340490307 135578388667634454510735461)
    ·
      refine ⟨25420947875181460220762899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135578388667634454510735461 25420947875181460220762899)
      ·
        refine ⟨38131421812772190331144349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25420947875181460220762899 38131421812772190331144349)
        ·
          refine ⟨14299283179789571374179131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38131421812772190331144349 14299283179789571374179131)
          ·
            refine ⟨21448924769684357061268697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14299283179789571374179131 21448924769684357061268697)
            ·
              refine ⟨16086693577263267795951523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21448924769684357061268697 16086693577263267795951523)
              ·
                refine ⟨24130040365894901693927285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16086693577263267795951523 24130040365894901693927285)
                ·
                  refine ⟨2262191284302647033805683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24130040365894901693927285 2262191284302647033805683)
                  ·
                    refine ⟨3393286926453970550708525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2262191284302647033805683 3393286926453970550708525)
                    ·
                      refine ⟨1272482597420238956515697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3393286926453970550708525 1272482597420238956515697)
                      ·
                        rfl

theorem cell23_2478151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_2478151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478151 prefixEnd_2478151 := by exact prefixLift 2478151
  have htrace : WordTrace (prefixWord ++ tailWord_2478151) baseStart_2478151 baseEnd_2478151 := by
    simpa [prefixWord, tailWord_2478151, baseEnd_2478151] using wordTrace_append hprefix tailTrace_2478151
  have hstable : (prefixWord ++ tailWord_2478151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478151).length < 2 ^ (prefixWord ++ tailWord_2478151).sum := by decide
  have hdescent : baseEnd_2478151 < baseStart_2478151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478201 : List Nat := [1, 2, 1, 3, 4, 2, 2, 1, 1, 6]
def baseStart_2478201 : Nat := 118140960795 + 2478201 * 2 ^ 59
def prefixEnd_2478201 : Nat := 4983230072969 + 3 ^ 40 * 2478201 * 2
def baseEnd_2478201 : Nat := 424169423817654586963489

theorem tailTrace_2478201 : CollatzResearch.WordTrace tailWord_2478201 prefixEnd_2478201 424169423817654586963489 := by
  unfold tailWord_2478201
  simp only [CollatzResearch.WordTrace]
  refine ⟨90387416094908494879810457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60258277396605663253206971 90387416094908494879810457)
  ·
    refine ⟨67790562071181371159857843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90387416094908494879810457 67790562071181371159857843)
    ·
      refine ⟨101685843106772056739786765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67790562071181371159857843 101685843106772056739786765)
      ·
        refine ⟨38132191165039521277420037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101685843106772056739786765 38132191165039521277420037)
        ·
          refine ⟨7149785843444910239516257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38132191165039521277420037 7149785843444910239516257)
          ·
            refine ⟨5362339382583682679637193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7149785843444910239516257 5362339382583682679637193)
            ·
              refine ⟨4021754536937762009727895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5362339382583682679637193 4021754536937762009727895)
              ·
                refine ⟨6032631805406643014591843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4021754536937762009727895 6032631805406643014591843)
                ·
                  refine ⟨9048947708109964521887765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6032631805406643014591843 9048947708109964521887765)
                  ·
                    refine ⟨424169423817654586963489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9048947708109964521887765 424169423817654586963489)
                    ·
                      rfl

theorem cell23_2478201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 6].length) (baseStart_2478201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478201 prefixEnd_2478201 := by exact prefixLift 2478201
  have htrace : WordTrace (prefixWord ++ tailWord_2478201) baseStart_2478201 baseEnd_2478201 := by
    simpa [prefixWord, tailWord_2478201, baseEnd_2478201] using wordTrace_append hprefix tailTrace_2478201
  have hstable : (prefixWord ++ tailWord_2478201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478201).length < 2 ^ (prefixWord ++ tailWord_2478201).sum := by decide
  have hdescent : baseEnd_2478201 < baseStart_2478201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478211 : List Nat := [1, 1, 1, 3, 3, 3, 2, 1, 3, 2, 3]
def baseStart_2478211 : Nat := 118140960795 + 2478211 * 2 ^ 59
def prefixEnd_2478211 : Nat := 4983230072969 + 3 ^ 40 * 2478211 * 2
def baseEnd_2478211 : Nat := 1272513406259508721765421

theorem tailTrace_2478211 : CollatzResearch.WordTrace tailWord_2478211 prefixEnd_2478211 1272513406259508721765421 := by
  unfold tailWord_2478211
  simp only [CollatzResearch.WordTrace]
  refine ⟨90387780824872266587674487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60258520549914844391782991 90387780824872266587674487)
  ·
    refine ⟨135581671237308399881511731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90387780824872266587674487 135581671237308399881511731)
    ·
      refine ⟨203372506855962599822267597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135581671237308399881511731 203372506855962599822267597)
      ·
        refine ⟨76264690070985974933350349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203372506855962599822267597 76264690070985974933350349)
        ·
          refine ⟨28599258776619740600006381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76264690070985974933350349 28599258776619740600006381)
          ·
            refine ⟨10724722041232402725002393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28599258776619740600006381 10724722041232402725002393)
            ·
              refine ⟨8043541530924302043751795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10724722041232402725002393 8043541530924302043751795)
              ·
                refine ⟨12065312296386453065627693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8043541530924302043751795 12065312296386453065627693)
                ·
                  refine ⟨4524492111144919899610385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12065312296386453065627693 4524492111144919899610385)
                  ·
                    refine ⟨3393369083358689924707789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4524492111144919899610385 3393369083358689924707789)
                    ·
                      refine ⟨1272513406259508721765421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3393369083358689924707789 1272513406259508721765421)
                      ·
                        rfl

theorem cell23_2478211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2, 3].length) (baseStart_2478211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478211 prefixEnd_2478211 := by exact prefixLift 2478211
  have htrace : WordTrace (prefixWord ++ tailWord_2478211) baseStart_2478211 baseEnd_2478211 := by
    simpa [prefixWord, tailWord_2478211, baseEnd_2478211] using wordTrace_append hprefix tailTrace_2478211
  have hstable : (prefixWord ++ tailWord_2478211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478211).length < 2 ^ (prefixWord ++ tailWord_2478211).sum := by decide
  have hdescent : baseEnd_2478211 < baseStart_2478211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478222 : List Nat := [4, 1, 1, 3, 4, 1, 2, 1, 1, 5]
def baseStart_2478222 : Nat := 118140960795 + 2478222 * 2 ^ 59
def prefixEnd_2478222 : Nat := 4983230072969 + 3 ^ 40 * 2478222 * 2
def baseEnd_2478222 : Nat := 424173018182236059575957

theorem tailTrace_2478222 : CollatzResearch.WordTrace tailWord_2478222 prefixEnd_2478222 424173018182236059575957 := by
  unfold tailWord_2478222
  simp only [CollatzResearch.WordTrace]
  refine ⟨11298522753479051933290615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60258788018554943644216613 11298522753479051933290615)
  ·
    refine ⟨16947784130218577899935923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11298522753479051933290615 16947784130218577899935923)
    ·
      refine ⟨25421676195327866849903885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16947784130218577899935923 25421676195327866849903885)
      ·
        refine ⟨9533128573247950068713957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25421676195327866849903885 9533128573247950068713957)
        ·
          refine ⟨1787461607483990637883867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9533128573247950068713957 1787461607483990637883867)
          ·
            refine ⟨2681192411225985956825801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1787461607483990637883867 2681192411225985956825801)
            ·
              refine ⟨2010894308419489467619351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2681192411225985956825801 2010894308419489467619351)
              ·
                refine ⟨3016341462629234201429027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2010894308419489467619351 3016341462629234201429027)
                ·
                  refine ⟨4524512193943851302143541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3016341462629234201429027 4524512193943851302143541)
                  ·
                    refine ⟨424173018182236059575957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4524512193943851302143541 424173018182236059575957)
                    ·
                      rfl

theorem cell23_2478222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_2478222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478222 prefixEnd_2478222 := by exact prefixLift 2478222
  have htrace : WordTrace (prefixWord ++ tailWord_2478222) baseStart_2478222 baseEnd_2478222 := by
    simpa [prefixWord, tailWord_2478222, baseEnd_2478222] using wordTrace_append hprefix tailTrace_2478222
  have hstable : (prefixWord ++ tailWord_2478222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478222).length < 2 ^ (prefixWord ++ tailWord_2478222).sum := by decide
  have hdescent : baseEnd_2478222 < baseStart_2478222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478242 : List Nat := [3, 3, 1, 3, 1, 2, 2, 1, 3, 2, 2]
def baseStart_2478242 : Nat := 118140960795 + 2478242 * 2 ^ 59
def prefixEnd_2478242 : Nat := 4983230072969 + 3 ^ 40 * 2478242 * 2
def baseEnd_2478242 : Nat := 1272529324159798100477779

theorem tailTrace_2478242 : CollatzResearch.WordTrace tailWord_2478242 prefixEnd_2478242 1272529324159798100477779 := by
  unfold tailWord_2478242
  simp only [CollatzResearch.WordTrace]
  refine ⟨22597227871939989720513245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60259274325173305921368653 22597227871939989720513245)
  ·
    refine ⟨8473960451977496145192467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22597227871939989720513245 8473960451977496145192467)
    ·
      refine ⟨12710940677966244217788701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8473960451977496145192467 12710940677966244217788701)
      ·
        refine ⟨4766602754237341581670763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12710940677966244217788701 4766602754237341581670763)
        ·
          refine ⟨7149904131356012372506145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4766602754237341581670763 7149904131356012372506145)
          ·
            refine ⟨5362428098517009279379609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7149904131356012372506145 5362428098517009279379609)
            ·
              refine ⟨4021821073887756959534707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5362428098517009279379609 4021821073887756959534707)
              ·
                refine ⟨6032731610831635439302061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4021821073887756959534707 6032731610831635439302061)
                ·
                  refine ⟨2262274354061863289738273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6032731610831635439302061 2262274354061863289738273)
                  ·
                    refine ⟨1696705765546397467303705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2262274354061863289738273 1696705765546397467303705)
                    ·
                      refine ⟨1272529324159798100477779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1696705765546397467303705 1272529324159798100477779)
                      ·
                        rfl

theorem cell23_2478242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_2478242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478242 prefixEnd_2478242 := by exact prefixLift 2478242
  have htrace : WordTrace (prefixWord ++ tailWord_2478242) baseStart_2478242 baseEnd_2478242 := by
    simpa [prefixWord, tailWord_2478242, baseEnd_2478242] using wordTrace_append hprefix tailTrace_2478242
  have hstable : (prefixWord ++ tailWord_2478242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478242).length < 2 ^ (prefixWord ++ tailWord_2478242).sum := by decide
  have hdescent : baseEnd_2478242 < baseStart_2478242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478315 : List Nat := [1, 1, 1, 1, 2, 5, 3, 3, 2, 2, 2]
def baseStart_2478315 : Nat := 118140960795 + 2478315 * 2 ^ 59
def prefixEnd_2478315 : Nat := 4983230072969 + 3 ^ 40 * 2478315 * 2
def baseEnd_2478315 : Nat := 1272566808247576314864943

theorem tailTrace_2478315 : CollatzResearch.WordTrace tailWord_2478315 prefixEnd_2478315 1272566808247576314864943 := by
  unfold tailWord_2478315
  simp only [CollatzResearch.WordTrace]
  refine ⟨90391574016495492349460399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60261049344330328232973599 90391574016495492349460399)
  ·
    refine ⟨135587361024743238524190599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90391574016495492349460399 135587361024743238524190599)
    ·
      refine ⟨203381041537114857786285899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135587361024743238524190599 203381041537114857786285899)
      ·
        refine ⟨305071562305672286679428849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203381041537114857786285899 305071562305672286679428849)
        ·
          refine ⟨228803671729254215009571637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305071562305672286679428849 228803671729254215009571637)
          ·
            refine ⟨21450344224617582657147341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 228803671729254215009571637 21450344224617582657147341)
            ·
              refine ⟨8043879084231593496430253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21450344224617582657147341 8043879084231593496430253)
              ·
                refine ⟨3016454656586847561161345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8043879084231593496430253 3016454656586847561161345)
                ·
                  refine ⟨2262340992440135670871009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3016454656586847561161345 2262340992440135670871009)
                  ·
                    refine ⟨1696755744330101753153257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2262340992440135670871009 1696755744330101753153257)
                    ·
                      refine ⟨1272566808247576314864943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1696755744330101753153257 1272566808247576314864943)
                      ·
                        rfl

theorem cell23_2478315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2, 2, 2].length) (baseStart_2478315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478315 prefixEnd_2478315 := by exact prefixLift 2478315
  have htrace : WordTrace (prefixWord ++ tailWord_2478315) baseStart_2478315 baseEnd_2478315 := by
    simpa [prefixWord, tailWord_2478315, baseEnd_2478315] using wordTrace_append hprefix tailTrace_2478315
  have hstable : (prefixWord ++ tailWord_2478315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478315).length < 2 ^ (prefixWord ++ tailWord_2478315).sum := by decide
  have hdescent : baseEnd_2478315 < baseStart_2478315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478365 : List Nat := [1, 4, 2, 3, 2, 1, 1, 1, 2, 3, 3]
def baseStart_2478365 : Nat := 118140960795 + 2478365 * 2 ^ 59
def prefixEnd_2478365 : Nat := 4983230072969 + 3 ^ 40 * 2478365 * 2
def baseEnd_2478365 : Nat := 1272592482280301119239713

theorem tailTrace_2478365 : CollatzResearch.WordTrace tailWord_2478365 prefixEnd_2478365 1272592482280301119239713 := by
  unfold tailWord_2478365
  simp only [CollatzResearch.WordTrace]
  refine ⟨90393397666314350888780549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60262265110876233925853699 90393397666314350888780549)
  ·
    refine ⟨16948762062433940791646353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90393397666314350888780549 16948762062433940791646353)
    ·
      refine ⟨12711571546825455593734765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16948762062433940791646353 12711571546825455593734765)
      ·
        refine ⟨4766839330059545847650537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12711571546825455593734765 4766839330059545847650537)
        ·
          refine ⟨3575129497544659385737903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4766839330059545847650537 3575129497544659385737903)
          ·
            refine ⟨5362694246316989078606855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3575129497544659385737903 5362694246316989078606855)
            ·
              refine ⟨8044041369475483617910283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5362694246316989078606855 8044041369475483617910283)
              ·
                refine ⟨12066062054213225426865425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8044041369475483617910283 12066062054213225426865425)
                ·
                  refine ⟨9049546540659919070149069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12066062054213225426865425 9049546540659919070149069)
                  ·
                    refine ⟨3393579952747469651305901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9049546540659919070149069 3393579952747469651305901)
                    ·
                      refine ⟨1272592482280301119239713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3393579952747469651305901 1272592482280301119239713)
                      ·
                        rfl

theorem cell23_2478365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_2478365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478365 prefixEnd_2478365 := by exact prefixLift 2478365
  have htrace : WordTrace (prefixWord ++ tailWord_2478365) baseStart_2478365 baseEnd_2478365 := by
    simpa [prefixWord, tailWord_2478365, baseEnd_2478365] using wordTrace_append hprefix tailTrace_2478365
  have hstable : (prefixWord ++ tailWord_2478365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478365).length < 2 ^ (prefixWord ++ tailWord_2478365).sum := by decide
  have hdescent : baseEnd_2478365 < baseStart_2478365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478371 : List Nat := [1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 4]
def baseStart_2478371 : Nat := 118140960795 + 2478371 * 2 ^ 59
def prefixEnd_2478371 : Nat := 4983230072969 + 3 ^ 40 * 2478371 * 2
def baseEnd_2478371 : Nat := 1272595563164228095764685

theorem tailTrace_2478371 : CollatzResearch.WordTrace tailWord_2478371 prefixEnd_2478371 1272595563164228095764685 := by
  unfold tailWord_2478371
  simp only [CollatzResearch.WordTrace]
  refine ⟨90393616504292613913498967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60262411002861742608999311 90393616504292613913498967)
  ·
    refine ⟨135590424756438920870248451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90393616504292613913498967 135590424756438920870248451)
    ·
      refine ⟨203385637134658381305372677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135590424756438920870248451 203385637134658381305372677)
      ·
        refine ⟨38134806962748446494757377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 203385637134658381305372677 38134806962748446494757377)
        ·
          refine ⟨28601105222061334871068033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38134806962748446494757377 28601105222061334871068033)
          ·
            refine ⟨21450828916546001153301025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28601105222061334871068033 21450828916546001153301025)
            ·
              refine ⟨16088121687409500864975769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21450828916546001153301025 16088121687409500864975769)
              ·
                refine ⟨12066091265557125648731827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16088121687409500864975769 12066091265557125648731827)
                ·
                  refine ⟨18099136898335688473097741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12066091265557125648731827 18099136898335688473097741)
                  ·
                    refine ⟨6787176336875883177411653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18099136898335688473097741 6787176336875883177411653)
                    ·
                      refine ⟨1272595563164228095764685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6787176336875883177411653 1272595563164228095764685)
                      ·
                        rfl

theorem cell23_2478371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_2478371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478371 prefixEnd_2478371 := by exact prefixLift 2478371
  have htrace : WordTrace (prefixWord ++ tailWord_2478371) baseStart_2478371 baseEnd_2478371 := by
    simpa [prefixWord, tailWord_2478371, baseEnd_2478371] using wordTrace_append hprefix tailTrace_2478371
  have hstable : (prefixWord ++ tailWord_2478371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478371).length < 2 ^ (prefixWord ++ tailWord_2478371).sum := by decide
  have hdescent : baseEnd_2478371 < baseStart_2478371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478385 : List Nat := [1, 2, 2, 3, 4, 2, 1, 1, 2, 5]
def baseStart_2478385 : Nat := 118140960795 + 2478385 * 2 ^ 59
def prefixEnd_2478385 : Nat := 4983230072969 + 3 ^ 40 * 2478385 * 2
def baseEnd_2478385 : Nat := 424200917297797013663207

theorem tailTrace_2478385 : CollatzResearch.WordTrace tailWord_2478385 prefixEnd_2478385 424200917297797013663207 := by
  unfold tailWord_2478385
  simp only [CollatzResearch.WordTrace]
  refine ⟨90394127126241894304508609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60262751417494596203005739 90394127126241894304508609)
  ·
    refine ⟨67795595344681420728381457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90394127126241894304508609 67795595344681420728381457)
    ·
      refine ⟨50846696508511065546286093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67795595344681420728381457 50846696508511065546286093)
      ·
        refine ⟨19067511190691649579857285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50846696508511065546286093 19067511190691649579857285)
        ·
          refine ⟨3575158348254684296223241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19067511190691649579857285 3575158348254684296223241)
          ·
            refine ⟨2681368761191013222167431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3575158348254684296223241 2681368761191013222167431)
            ·
              refine ⟨4022053141786519833251147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2681368761191013222167431 4022053141786519833251147)
              ·
                refine ⟨6033079712679779749876721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4022053141786519833251147 6033079712679779749876721)
                ·
                  refine ⟨4524809784509834812407541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6033079712679779749876721 4524809784509834812407541)
                  ·
                    refine ⟨424200917297797013663207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4524809784509834812407541 424200917297797013663207)
                    ·
                      rfl

theorem cell23_2478385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 5].length) (baseStart_2478385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478385 prefixEnd_2478385 := by exact prefixLift 2478385
  have htrace : WordTrace (prefixWord ++ tailWord_2478385) baseStart_2478385 baseEnd_2478385 := by
    simpa [prefixWord, tailWord_2478385, baseEnd_2478385] using wordTrace_append hprefix tailTrace_2478385
  have hstable : (prefixWord ++ tailWord_2478385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478385).length < 2 ^ (prefixWord ++ tailWord_2478385).sum := by decide
  have hdescent : baseEnd_2478385 < baseStart_2478385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478408 : List Nat := [2, 1, 3, 1, 1, 2, 2, 4, 2, 2, 3]
def baseStart_2478408 : Nat := 118140960795 + 2478408 * 2 ^ 59
def prefixEnd_2478408 : Nat := 4983230072969 + 3 ^ 40 * 2478408 * 2
def baseEnd_2478408 : Nat := 1272614561948444451002015

theorem tailTrace_2478408 : CollatzResearch.WordTrace tailWord_2478408 prefixEnd_2478408 1272614561948444451002015 := by
  unfold tailWord_2478408
  simp only [CollatzResearch.WordTrace]
  refine ⟨45197483002579284616297939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60263310670105712821730585 45197483002579284616297939)
  ·
    refine ⟨67796224503868926924446909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45197483002579284616297939 67796224503868926924446909)
    ·
      refine ⟨25423584188950847596667591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67796224503868926924446909 25423584188950847596667591)
      ·
        refine ⟨38135376283426271395001387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25423584188950847596667591 38135376283426271395001387)
        ·
          refine ⟨57203064425139407092502081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38135376283426271395001387 57203064425139407092502081)
          ·
            refine ⟨42902298318854555319376561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57203064425139407092502081 42902298318854555319376561)
            ·
              refine ⟨32176723739140916489532421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42902298318854555319376561 32176723739140916489532421)
              ·
                refine ⟨6033135701088921841787329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32176723739140916489532421 6033135701088921841787329)
                ·
                  refine ⟨4524851775816691381340497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6033135701088921841787329 4524851775816691381340497)
                  ·
                    refine ⟨3393638831862518536005373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4524851775816691381340497 3393638831862518536005373)
                    ·
                      refine ⟨1272614561948444451002015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3393638831862518536005373 1272614561948444451002015)
                      ·
                        rfl

theorem cell23_2478408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_2478408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478408 prefixEnd_2478408 := by exact prefixLift 2478408
  have htrace : WordTrace (prefixWord ++ tailWord_2478408) baseStart_2478408 baseEnd_2478408 := by
    simpa [prefixWord, tailWord_2478408, baseEnd_2478408] using wordTrace_append hprefix tailTrace_2478408
  have hstable : (prefixWord ++ tailWord_2478408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478408).length < 2 ^ (prefixWord ++ tailWord_2478408).sum := by decide
  have hdescent : baseEnd_2478408 < baseStart_2478408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478411 : List Nat := [1, 1, 1, 1, 3, 1, 1, 8, 6]
def baseStart_2478411 : Nat := 118140960795 + 2478411 * 2 ^ 59
def prefixEnd_2478411 : Nat := 4983230072969 + 3 ^ 40 * 2478411 * 2
def baseEnd_2478411 : Nat := 141401789154489771029389

theorem tailTrace_2478411 : CollatzResearch.WordTrace tailWord_2478411 prefixEnd_2478411 141401789154489771029389 := by
  unfold tailWord_2478411
  simp only [CollatzResearch.WordTrace]
  refine ⟨90395075424147700744955087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60263383616098467163303391 90395075424147700744955087)
  ·
    refine ⟨135592613136221551117432631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90395075424147700744955087 135592613136221551117432631)
    ·
      refine ⟨203388919704332326676148947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135592613136221551117432631 203388919704332326676148947)
      ·
        refine ⟨305083379556498490014223421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203388919704332326676148947 305083379556498490014223421)
        ·
          refine ⟨114406267333686933755333783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 305083379556498490014223421 114406267333686933755333783)
          ·
            refine ⟨171609401000530400633000675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114406267333686933755333783 171609401000530400633000675)
            ·
              refine ⟨257414101500795600949501013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171609401000530400633000675 257414101500795600949501013)
              ·
                refine ⟨3016571501962448448626965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 257414101500795600949501013 3016571501962448448626965)
                ·
                  refine ⟨141401789154489771029389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3016571501962448448626965 141401789154489771029389)
                  ·
                    rfl

theorem cell23_2478411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 6].length) (baseStart_2478411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478411 prefixEnd_2478411 := by exact prefixLift 2478411
  have htrace : WordTrace (prefixWord ++ tailWord_2478411) baseStart_2478411 baseEnd_2478411 := by
    simpa [prefixWord, tailWord_2478411, baseEnd_2478411] using wordTrace_append hprefix tailTrace_2478411
  have hstable : (prefixWord ++ tailWord_2478411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478411).length < 2 ^ (prefixWord ++ tailWord_2478411).sum := by decide
  have hdescent : baseEnd_2478411 < baseStart_2478411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478466 : List Nat := [3, 4, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_2478466 : Nat := 118140960795 + 2478466 * 2 ^ 59
def prefixEnd_2478466 : Nat := 4983230072969 + 3 ^ 40 * 2478466 * 2
def baseEnd_2478466 : Nat := 424214781275468408025583

theorem tailTrace_2478466 : CollatzResearch.WordTrace tailWord_2478466 prefixEnd_2478466 424214781275468408025583 := by
  unfold tailWord_2478466
  simp only [CollatzResearch.WordTrace]
  refine ⟨22599270359737111284551813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60264720959298963425471501 22599270359737111284551813)
  ·
    refine ⟨4237363192450708365853465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22599270359737111284551813 4237363192450708365853465)
    ·
      refine ⟨3178022394338031274390099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4237363192450708365853465 3178022394338031274390099)
      ·
        refine ⟨4767033591507046911585149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3178022394338031274390099 4767033591507046911585149)
        ·
          refine ⟨1787637596815142591844431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4767033591507046911585149 1787637596815142591844431)
          ·
            refine ⟨2681456395222713887766647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1787637596815142591844431 2681456395222713887766647)
            ·
              refine ⟨4022184592834070831649971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2681456395222713887766647 4022184592834070831649971)
              ·
                refine ⟨6033276889251106247474957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4022184592834070831649971 6033276889251106247474957)
                ·
                  refine ⟨2262478833469164842803109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6033276889251106247474957 2262478833469164842803109)
                  ·
                    refine ⟨424214781275468408025583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2262478833469164842803109 424214781275468408025583)
                    ·
                      rfl

theorem cell23_2478466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_2478466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478466 prefixEnd_2478466 := by exact prefixLift 2478466
  have htrace : WordTrace (prefixWord ++ tailWord_2478466) baseStart_2478466 baseEnd_2478466 := by
    simpa [prefixWord, tailWord_2478466, baseEnd_2478466] using wordTrace_append hprefix tailTrace_2478466
  have hstable : (prefixWord ++ tailWord_2478466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478466).length < 2 ^ (prefixWord ++ tailWord_2478466).sum := by decide
  have hdescent : baseEnd_2478466 < baseStart_2478466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478501 : List Nat := [1, 3, 1, 2, 1, 1, 3, 11]
def baseStart_2478501 : Nat := 118140960795 + 2478501 * 2 ^ 59
def prefixEnd_2478501 : Nat := 4983230072969 + 3 ^ 40 * 2478501 * 2
def baseEnd_2478501 : Nat := 47135641320344910634781

theorem tailTrace_2478501 : CollatzResearch.WordTrace tailWord_2478501 prefixEnd_2478501 47135641320344910634781 := by
  unfold tailWord_2478501
  simp only [CollatzResearch.WordTrace]
  refine ⟨90398357993821646115731357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60265571995881097410487571 90398357993821646115731357)
  ·
    refine ⟨33899384247683117293399259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90398357993821646115731357 33899384247683117293399259)
    ·
      refine ⟨50849076371524675940098889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33899384247683117293399259 50849076371524675940098889)
      ·
        refine ⟨38136807278643506955074167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50849076371524675940098889 38136807278643506955074167)
        ·
          refine ⟨57205210917965260432611251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38136807278643506955074167 57205210917965260432611251)
          ·
            refine ⟨85807816376947890648916877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57205210917965260432611251 85807816376947890648916877)
            ·
              refine ⟨32177931141355458993343829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85807816376947890648916877 32177931141355458993343829)
              ·
                refine ⟨47135641320344910634781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 32177931141355458993343829 47135641320344910634781)
                ·
                  rfl

theorem cell23_2478501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 11].length) (baseStart_2478501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478501 prefixEnd_2478501 := by exact prefixLift 2478501
  have htrace : WordTrace (prefixWord ++ tailWord_2478501) baseStart_2478501 baseEnd_2478501 := by
    simpa [prefixWord, tailWord_2478501, baseEnd_2478501] using wordTrace_append hprefix tailTrace_2478501
  have hstable : (prefixWord ++ tailWord_2478501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478501).length < 2 ^ (prefixWord ++ tailWord_2478501).sum := by decide
  have hdescent : baseEnd_2478501 < baseStart_2478501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478509 : List Nat := [1, 5, 2, 2, 2, 1, 3, 1, 1, 5]
def baseStart_2478509 : Nat := 118140960795 + 2478509 * 2 ^ 59
def prefixEnd_2478509 : Nat := 4983230072969 + 3 ^ 40 * 2478509 * 2
def baseEnd_2478509 : Nat := 424222141164849518613017

theorem tailTrace_2478509 : CollatzResearch.WordTrace tailWord_2478509 prefixEnd_2478509 424222141164849518613017 := by
  unfold tailWord_2478509
  simp only [CollatzResearch.WordTrace]
  refine ⟨90398649777792663482022581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60265766518528442321348387 90398649777792663482022581)
  ·
    refine ⟨8474873416668062201439617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90398649777792663482022581 8474873416668062201439617)
    ·
      refine ⟨6356155062501046651079713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8474873416668062201439617 6356155062501046651079713)
      ·
        refine ⟨4767116296875784988309785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6356155062501046651079713 4767116296875784988309785)
        ·
          refine ⟨3575337222656838741232339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4767116296875784988309785 3575337222656838741232339)
          ·
            refine ⟨5363005833985258111848509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3575337222656838741232339 5363005833985258111848509)
            ·
              refine ⟨2011127187744471791943191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5363005833985258111848509 2011127187744471791943191)
              ·
                refine ⟨3016690781616707687914787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2011127187744471791943191 3016690781616707687914787)
                ·
                  refine ⟨4525036172425061531872181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3016690781616707687914787 4525036172425061531872181)
                  ·
                    refine ⟨424222141164849518613017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4525036172425061531872181 424222141164849518613017)
                    ·
                      rfl

theorem cell23_2478509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_2478509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478509 prefixEnd_2478509 := by exact prefixLift 2478509
  have htrace : WordTrace (prefixWord ++ tailWord_2478509) baseStart_2478509 baseEnd_2478509 := by
    simpa [prefixWord, tailWord_2478509, baseEnd_2478509] using wordTrace_append hprefix tailTrace_2478509
  have hstable : (prefixWord ++ tailWord_2478509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478509).length < 2 ^ (prefixWord ++ tailWord_2478509).sum := by decide
  have hdescent : baseEnd_2478509 < baseStart_2478509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478528 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 3]
def baseStart_2478528 : Nat := 118140960795 + 2478528 * 2 ^ 59
def prefixEnd_2478528 : Nat := 4983230072969 + 3 ^ 40 * 2478528 * 2
def baseEnd_2478528 : Nat := 1272676179626983981501463

theorem tailTrace_2478528 : CollatzResearch.WordTrace tailWord_2478528 prefixEnd_2478528 1272676179626983981501463 := by
  unfold tailWord_2478528
  simp only [CollatzResearch.WordTrace]
  refine ⟨45199671382361914863482119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60266228509815886484642825 45199671382361914863482119)
  ·
    refine ⟨67799507073542872295223179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45199671382361914863482119 67799507073542872295223179)
    ·
      refine ⟨101699260610314308442834769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67799507073542872295223179 101699260610314308442834769)
      ·
        refine ⟨76274445457735731332126077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101699260610314308442834769 76274445457735731332126077)
        ·
          refine ⟨28602917046650899249547279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76274445457735731332126077 28602917046650899249547279)
          ·
            refine ⟨42904375569976348874320919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28602917046650899249547279 42904375569976348874320919)
            ·
              refine ⟨64356563354964523311481379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42904375569976348874320919 64356563354964523311481379)
              ·
                refine ⟨96534845032446784967222069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64356563354964523311481379 96534845032446784967222069)
                ·
                  refine ⟨9050141721791886090677069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 96534845032446784967222069 9050141721791886090677069)
                  ·
                    refine ⟨3393803145671957284003901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9050141721791886090677069 3393803145671957284003901)
                    ·
                      refine ⟨1272676179626983981501463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3393803145671957284003901 1272676179626983981501463)
                      ·
                        rfl

theorem cell23_2478528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 3].length) (baseStart_2478528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478528 prefixEnd_2478528 := by exact prefixLift 2478528
  have htrace : WordTrace (prefixWord ++ tailWord_2478528) baseStart_2478528 baseEnd_2478528 := by
    simpa [prefixWord, tailWord_2478528, baseEnd_2478528] using wordTrace_append hprefix tailTrace_2478528
  have hstable : (prefixWord ++ tailWord_2478528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478528).length < 2 ^ (prefixWord ++ tailWord_2478528).sum := by decide
  have hdescent : baseEnd_2478528 < baseStart_2478528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478546 : List Nat := [3, 2, 2, 4, 1, 1, 1, 2, 3, 2, 2]
def baseStart_2478546 : Nat := 118140960795 + 2478546 * 2 ^ 59
def prefixEnd_2478546 : Nat := 4983230072969 + 3 ^ 40 * 2478546 * 2
def baseEnd_2478546 : Nat := 1272685422278764911076381

theorem tailTrace_2478546 : CollatzResearch.WordTrace tailWord_2478546 prefixEnd_2478546 1272685422278764911076381 := by
  unfold tailWord_2478546
  simp only [CollatzResearch.WordTrace]
  refine ⟨22599999819664654700279873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60266666185772412534079661 22599999819664654700279873)
  ·
    refine ⟨16949999864748491025209905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22599999819664654700279873 16949999864748491025209905)
    ·
      refine ⟨12712499898561368268907429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16949999864748491025209905 12712499898561368268907429)
      ·
        refine ⟨2383593730980256550420143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12712499898561368268907429 2383593730980256550420143)
        ·
          refine ⟨3575390596470384825630215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2383593730980256550420143 3575390596470384825630215)
          ·
            refine ⟨5363085894705577238445323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3575390596470384825630215 5363085894705577238445323)
            ·
              refine ⟨8044628842058365857667985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5363085894705577238445323 8044628842058365857667985)
              ·
                refine ⟨6033471631543774393250989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8044628842058365857667985 6033471631543774393250989)
                ·
                  refine ⟨2262551861828915397469121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6033471631543774393250989 2262551861828915397469121)
                  ·
                    refine ⟨1696913896371686548101841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2262551861828915397469121 1696913896371686548101841)
                    ·
                      refine ⟨1272685422278764911076381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1696913896371686548101841 1272685422278764911076381)
                      ·
                        rfl

theorem cell23_2478546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_2478546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478546 prefixEnd_2478546 := by exact prefixLift 2478546
  have htrace : WordTrace (prefixWord ++ tailWord_2478546) baseStart_2478546 baseEnd_2478546 := by
    simpa [prefixWord, tailWord_2478546, baseEnd_2478546] using wordTrace_append hprefix tailTrace_2478546
  have hstable : (prefixWord ++ tailWord_2478546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478546).length < 2 ^ (prefixWord ++ tailWord_2478546).sum := by decide
  have hdescent : baseEnd_2478546 < baseStart_2478546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478572 : List Nat := [2, 2, 1, 1, 2, 1, 5, 3, 1, 3, 2]
def baseStart_2478572 : Nat := 118140960795 + 2478572 * 2 ^ 59
def prefixEnd_2478572 : Nat := 4983230072969 + 3 ^ 40 * 2478572 * 2
def baseEnd_2478572 : Nat := 1272698772775781809351261

theorem tailTrace_2478572 : CollatzResearch.WordTrace tailWord_2478572 prefixEnd_2478572 1272698772775781809351261 := by
  unfold tailWord_2478572
  simp only [CollatzResearch.WordTrace]
  refine ⟨45200473788282212620782985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60267298384376283494377313 45200473788282212620782985)
  ·
    refine ⟨33900355341211659465587239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45200473788282212620782985 33900355341211659465587239)
    ·
      refine ⟨50850533011817489198380859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33900355341211659465587239 50850533011817489198380859)
      ·
        refine ⟨76275799517726233797571289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50850533011817489198380859 76275799517726233797571289)
        ·
          refine ⟨57206849638294675348178467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76275799517726233797571289 57206849638294675348178467)
          ·
            refine ⟨85810274457442013022267701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57206849638294675348178467 85810274457442013022267701)
            ·
              refine ⟨8044713230385188720837597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85810274457442013022267701 8044713230385188720837597)
              ·
                refine ⟨3016767461394445770314099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8044713230385188720837597 3016767461394445770314099)
                ·
                  refine ⟨4525151192091668655471149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3016767461394445770314099 4525151192091668655471149)
                  ·
                    refine ⟨1696931697034375745801681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4525151192091668655471149 1696931697034375745801681)
                    ·
                      refine ⟨1272698772775781809351261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1696931697034375745801681 1272698772775781809351261)
                      ·
                        rfl

theorem cell23_2478572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 3, 2].length) (baseStart_2478572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478572 prefixEnd_2478572 := by exact prefixLift 2478572
  have htrace : WordTrace (prefixWord ++ tailWord_2478572) baseStart_2478572 baseEnd_2478572 := by
    simpa [prefixWord, tailWord_2478572, baseEnd_2478572] using wordTrace_append hprefix tailTrace_2478572
  have hstable : (prefixWord ++ tailWord_2478572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478572).length < 2 ^ (prefixWord ++ tailWord_2478572).sum := by decide
  have hdescent : baseEnd_2478572 < baseStart_2478572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478585 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 3, 4, 2]
def baseStart_2478585 : Nat := 118140960795 + 2478585 * 2 ^ 59
def prefixEnd_2478585 : Nat := 4983230072969 + 3 ^ 40 * 2478585 * 2
def baseEnd_2478585 : Nat := 1272705448024290258488701

theorem tailTrace_2478585 : CollatzResearch.WordTrace tailWord_2478585 prefixEnd_2478585 1272705448024290258488701 := by
  unfold tailWord_2478585
  simp only [CollatzResearch.WordTrace]
  refine ⟨90401421725517328461789209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60267614483678218974526139 90401421725517328461789209)
  ·
    refine ⟨67801066294137996346341907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90401421725517328461789209 67801066294137996346341907)
    ·
      refine ⟨101701599441206994519512861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67801066294137996346341907 101701599441206994519512861)
      ·
        refine ⟨38138099790452622944817323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101701599441206994519512861 38138099790452622944817323)
        ·
          refine ⟨57207149685678934417225985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38138099790452622944817323 57207149685678934417225985)
          ·
            refine ⟨42905362264259200812919489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57207149685678934417225985 42905362264259200812919489)
            ·
              refine ⟨32179021698194400609689617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42905362264259200812919489 32179021698194400609689617)
              ·
                refine ⟨24134266273645800457267213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32179021698194400609689617 24134266273645800457267213)
                ·
                  refine ⟨9050349852617175171475205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24134266273645800457267213 9050349852617175171475205)
                  ·
                    refine ⟨1696940597365720344651601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9050349852617175171475205 1696940597365720344651601)
                    ·
                      refine ⟨1272705448024290258488701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1696940597365720344651601 1272705448024290258488701)
                      ·
                        rfl

theorem cell23_2478585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 4, 2].length) (baseStart_2478585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478585 prefixEnd_2478585 := by exact prefixLift 2478585
  have htrace : WordTrace (prefixWord ++ tailWord_2478585) baseStart_2478585 baseEnd_2478585 := by
    simpa [prefixWord, tailWord_2478585, baseEnd_2478585] using wordTrace_append hprefix tailTrace_2478585
  have hstable : (prefixWord ++ tailWord_2478585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478585).length < 2 ^ (prefixWord ++ tailWord_2478585).sum := by decide
  have hdescent : baseEnd_2478585 < baseStart_2478585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478588 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 4, 1, 5]
def baseStart_2478588 : Nat := 118140960795 + 2478588 * 2 ^ 59
def prefixEnd_2478588 : Nat := 4983230072969 + 3 ^ 40 * 2478588 * 2
def baseEnd_2478588 : Nat := 1272706988466253746751187

theorem tailTrace_2478588 : CollatzResearch.WordTrace tailWord_2478588 prefixEnd_2478588 1272706988466253746751187 := by
  unfold tailWord_2478588
  simp only [CollatzResearch.WordTrace]
  refine ⟨45200765572253229987074209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60267687429670973316098945 45200765572253229987074209)
  ·
    refine ⟨33900574179189922490305657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45200765572253229987074209 33900574179189922490305657)
    ·
      refine ⟨25425430634392441867729243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33900574179189922490305657 25425430634392441867729243)
      ·
        refine ⟨38138145951588662801593865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25425430634392441867729243 38138145951588662801593865)
        ·
          refine ⟨28603609463691497101195399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38138145951588662801593865 28603609463691497101195399)
          ·
            refine ⟨42905414195537245651793099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28603609463691497101195399 42905414195537245651793099)
            ·
              refine ⟨64358121293305868477689649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42905414195537245651793099 64358121293305868477689649)
              ·
                refine ⟨48268590969979401358267237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64358121293305868477689649 48268590969979401358267237)
                ·
                  refine ⟨9050360806871137754675107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48268590969979401358267237 9050360806871137754675107)
                  ·
                    refine ⟨13575541210306706632012661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9050360806871137754675107 13575541210306706632012661)
                    ·
                      refine ⟨1272706988466253746751187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13575541210306706632012661 1272706988466253746751187)
                      ·
                        rfl

theorem cell23_2478588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_2478588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478588 prefixEnd_2478588 := by exact prefixLift 2478588
  have htrace : WordTrace (prefixWord ++ tailWord_2478588) baseStart_2478588 baseEnd_2478588 := by
    simpa [prefixWord, tailWord_2478588, baseEnd_2478588] using wordTrace_append hprefix tailTrace_2478588
  have hstable : (prefixWord ++ tailWord_2478588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478588).length < 2 ^ (prefixWord ++ tailWord_2478588).sum := by decide
  have hdescent : baseEnd_2478588 < baseStart_2478588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478596 : List Nat := [2, 3, 2, 3, 1, 2, 3, 1, 2, 1, 3]
def baseStart_2478596 : Nat := 118140960795 + 2478596 * 2 ^ 59
def prefixEnd_2478596 : Nat := 4983230072969 + 3 ^ 40 * 2478596 * 2
def baseEnd_2478596 : Nat := 1272711096311489715451151

theorem tailTrace_2478596 : CollatzResearch.WordTrace tailWord_2478596 prefixEnd_2478596 1272711096311489715451151 := by
  unfold tailWord_2478596
  simp only [CollatzResearch.WordTrace]
  refine ⟨45200911464238738670219821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60267881952318318226959761 45200911464238738670219821)
  ·
    refine ⟨16950341799089527001332433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45200911464238738670219821 16950341799089527001332433)
    ·
      refine ⟨12712756349317145250999325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16950341799089527001332433 12712756349317145250999325)
      ·
        refine ⟨4767283630993929469124747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12712756349317145250999325 4767283630993929469124747)
        ·
          refine ⟨7150925446490894203687121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4767283630993929469124747 7150925446490894203687121)
          ·
            refine ⟨5363194084868170652765341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7150925446490894203687121 5363194084868170652765341)
            ·
              refine ⟨2011197781825563994787003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5363194084868170652765341 2011197781825563994787003)
              ·
                refine ⟨3016796672738345992180505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2011197781825563994787003 3016796672738345992180505)
                ·
                  refine ⟨2262597504553759494135379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3016796672738345992180505 2262597504553759494135379)
                  ·
                    refine ⟨3393896256830639241203069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2262597504553759494135379 3393896256830639241203069)
                    ·
                      refine ⟨1272711096311489715451151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3393896256830639241203069 1272711096311489715451151)
                      ·
                        rfl

theorem cell23_2478596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_2478596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478596 prefixEnd_2478596 := by exact prefixLift 2478596
  have htrace : WordTrace (prefixWord ++ tailWord_2478596) baseStart_2478596 baseEnd_2478596 := by
    simpa [prefixWord, tailWord_2478596, baseEnd_2478596] using wordTrace_append hprefix tailTrace_2478596
  have hstable : (prefixWord ++ tailWord_2478596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478596).length < 2 ^ (prefixWord ++ tailWord_2478596).sum := by decide
  have hdescent : baseEnd_2478596 < baseStart_2478596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478653 : List Nat := [1, 4, 1, 3, 2, 3, 2, 1, 2, 2, 2]
def baseStart_2478653 : Nat := 118140960795 + 2478653 * 2 ^ 59
def prefixEnd_2478653 : Nat := 4983230072969 + 3 ^ 40 * 2478653 * 2
def baseEnd_2478653 : Nat := 1272740364708795992438389

theorem tailTrace_2478653 : CollatzResearch.WordTrace tailWord_2478653 prefixEnd_2478653 1272740364708795992438389 := by
  unfold tailWord_2478653
  simp only [CollatzResearch.WordTrace]
  refine ⟨90403901889270976075264613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60269267926180650716843075 90403901889270976075264613)
  ·
    refine ⟨16950731604238308014112115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90403901889270976075264613 16950731604238308014112115)
    ·
      refine ⟨25426097406357462021168173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16950731604238308014112115 25426097406357462021168173)
      ·
        refine ⟨9534786527384048257938065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25426097406357462021168173 9534786527384048257938065)
        ·
          refine ⟨7151089895538036193453549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9534786527384048257938065 7151089895538036193453549)
          ·
            refine ⟨2681658710826763572545081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7151089895538036193453549 2681658710826763572545081)
            ·
              refine ⟨2011244033120072679408811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2681658710826763572545081 2011244033120072679408811)
              ·
                refine ⟨3016866049680109019113217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2011244033120072679408811 3016866049680109019113217)
                ·
                  refine ⟨2262649537260081764334913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3016866049680109019113217 2262649537260081764334913)
                  ·
                    refine ⟨1696987152945061323251185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2262649537260081764334913 1696987152945061323251185)
                    ·
                      refine ⟨1272740364708795992438389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1696987152945061323251185 1272740364708795992438389)
                      ·
                        rfl

theorem cell23_2478653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_2478653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478653 prefixEnd_2478653 := by exact prefixLift 2478653
  have htrace : WordTrace (prefixWord ++ tailWord_2478653) baseStart_2478653 baseEnd_2478653 := by
    simpa [prefixWord, tailWord_2478653, baseEnd_2478653] using wordTrace_append hprefix tailTrace_2478653
  have hstable : (prefixWord ++ tailWord_2478653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478653).length < 2 ^ (prefixWord ++ tailWord_2478653).sum := by decide
  have hdescent : baseEnd_2478653 < baseStart_2478653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478692 : List Nat := [2, 3, 1, 1, 2, 2, 2, 2, 2, 4, 2]
def baseStart_2478692 : Nat := 118140960795 + 2478692 * 2 ^ 59
def prefixEnd_2478692 : Nat := 4983230072969 + 3 ^ 40 * 2478692 * 2
def baseEnd_2478692 : Nat := 1272760390454321339850709

theorem tailTrace_2478692 : CollatzResearch.WordTrace tailWord_2478692 prefixEnd_2478692 1272760390454321339850709 := by
  unfold tailWord_2478692
  simp only [CollatzResearch.WordTrace]
  refine ⟨45202662168064842867967165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60270216224086457157289553 45202662168064842867967165)
  ·
    refine ⟨16950998313024316075487687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45202662168064842867967165 16950998313024316075487687)
    ·
      refine ⟨25426497469536474113231531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16950998313024316075487687 25426497469536474113231531)
      ·
        refine ⟨38139746204304711169847297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25426497469536474113231531 38139746204304711169847297)
        ·
          refine ⟨28604809653228533377385473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38139746204304711169847297 28604809653228533377385473)
          ·
            refine ⟨21453607239921400033039105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28604809653228533377385473 21453607239921400033039105)
            ·
              refine ⟨16090205429941050024779329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21453607239921400033039105 16090205429941050024779329)
              ·
                refine ⟨12067654072455787518584497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16090205429941050024779329 12067654072455787518584497)
                ·
                  refine ⟨9050740554341840638938373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12067654072455787518584497 9050740554341840638938373)
                  ·
                    refine ⟨1697013853939095119800945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9050740554341840638938373 1697013853939095119800945)
                    ·
                      refine ⟨1272760390454321339850709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1697013853939095119800945 1272760390454321339850709)
                      ·
                        rfl

theorem cell23_2478692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 2, 4, 2].length) (baseStart_2478692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478692 prefixEnd_2478692 := by exact prefixLift 2478692
  have htrace : WordTrace (prefixWord ++ tailWord_2478692) baseStart_2478692 baseEnd_2478692 := by
    simpa [prefixWord, tailWord_2478692, baseEnd_2478692] using wordTrace_append hprefix tailTrace_2478692
  have hstable : (prefixWord ++ tailWord_2478692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478692).length < 2 ^ (prefixWord ++ tailWord_2478692).sum := by decide
  have hdescent : baseEnd_2478692 < baseStart_2478692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478695 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 3, 4, 3]
def baseStart_2478695 : Nat := 118140960795 + 2478695 * 2 ^ 59
def prefixEnd_2478695 : Nat := 4983230072969 + 3 ^ 40 * 2478695 * 2
def baseEnd_2478695 : Nat := 1272761930896284828113195

theorem tailTrace_2478695 : CollatzResearch.WordTrace tailWord_2478695 prefixEnd_2478695 1272761930896284828113195 := by
  unfold tailWord_2478695
  simp only [CollatzResearch.WordTrace]
  refine ⟨90405433755118817248293539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60270289170079211498862359 90405433755118817248293539)
  ·
    refine ⟨135608150632678225872440309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90405433755118817248293539 135608150632678225872440309)
    ·
      refine ⟨12713264121813583675541279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135608150632678225872440309 12713264121813583675541279)
      ·
        refine ⟨19069896182720375513311919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12713264121813583675541279 19069896182720375513311919)
        ·
          refine ⟨28604844274080563269967879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19069896182720375513311919 28604844274080563269967879)
          ·
            refine ⟨42907266411120844904951819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28604844274080563269967879 42907266411120844904951819)
            ·
              refine ⟨64360899616681267357427729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42907266411120844904951819 64360899616681267357427729)
              ·
                refine ⟨48270674712510950518070797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64360899616681267357427729 48270674712510950518070797)
                ·
                  refine ⟨18101503017191606444276549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48270674712510950518070797 18101503017191606444276549)
                  ·
                    refine ⟨3394031815723426208301853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18101503017191606444276549 3394031815723426208301853)
                    ·
                      refine ⟨1272761930896284828113195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3394031815723426208301853 1272761930896284828113195)
                      ·
                        rfl

theorem cell23_2478695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_2478695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478695 prefixEnd_2478695 := by exact prefixLift 2478695
  have htrace : WordTrace (prefixWord ++ tailWord_2478695) baseStart_2478695 baseEnd_2478695 := by
    simpa [prefixWord, tailWord_2478695, baseEnd_2478695] using wordTrace_append hprefix tailTrace_2478695
  have hstable : (prefixWord ++ tailWord_2478695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478695).length < 2 ^ (prefixWord ++ tailWord_2478695).sum := by decide
  have hdescent : baseEnd_2478695 < baseStart_2478695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478766 : List Nat := [4, 1, 4, 1, 1, 2, 3, 1, 6]
def baseStart_2478766 : Nat := 118140960795 + 2478766 * 2 ^ 59
def prefixEnd_2478766 : Nat := 4983230072969 + 3 ^ 40 * 2478766 * 2
def baseEnd_2478766 : Nat := 141422043113639338925041

theorem tailTrace_2478766 : CollatzResearch.WordTrace tailWord_2478766 prefixEnd_2478766 141422043113639338925041 := by
  unfold tailWord_2478766
  simp only [CollatzResearch.WordTrace]
  refine ⟨11301002917232699546766019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60272015558574397582752101 11301002917232699546766019)
  ·
    refine ⟨16951504375849049320149029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11301002917232699546766019 16951504375849049320149029)
    ·
      refine ⟨3178407070471696747527943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16951504375849049320149029 3178407070471696747527943)
      ·
        refine ⟨4767610605707545121291915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3178407070471696747527943 4767610605707545121291915)
        ·
          refine ⟨7151415908561317681937873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4767610605707545121291915 7151415908561317681937873)
          ·
            refine ⟨5363561931420988261453405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7151415908561317681937873 5363561931420988261453405)
            ·
              refine ⟨2011335724282870598045027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5363561931420988261453405 2011335724282870598045027)
              ·
                refine ⟨3017003586424305897067541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2011335724282870598045027 3017003586424305897067541)
                ·
                  refine ⟨141422043113639338925041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3017003586424305897067541 141422043113639338925041)
                  ·
                    rfl

theorem cell23_2478766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 6].length) (baseStart_2478766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478766 prefixEnd_2478766 := by exact prefixLift 2478766
  have htrace : WordTrace (prefixWord ++ tailWord_2478766) baseStart_2478766 baseEnd_2478766 := by
    simpa [prefixWord, tailWord_2478766, baseEnd_2478766] using wordTrace_append hprefix tailTrace_2478766
  have hstable : (prefixWord ++ tailWord_2478766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478766).length < 2 ^ (prefixWord ++ tailWord_2478766).sum := by decide
  have hdescent : baseEnd_2478766 < baseStart_2478766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478792 : List Nat := [2, 1, 3, 1, 2, 3, 1, 2, 4, 4]
def baseStart_2478792 : Nat := 118140960795 + 2478792 * 2 ^ 59
def prefixEnd_2478792 : Nat := 4983230072969 + 3 ^ 40 * 2478792 * 2
def baseEnd_2478792 : Nat := 424270579506590316200083

theorem tailTrace_2478792 : CollatzResearch.WordTrace tailWord_2478792 prefixEnd_2478792 424270579506590316200083 := by
  unfold tailWord_2478792
  simp only [CollatzResearch.WordTrace]
  refine ⟨45204485817883701407287315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60272647757178268543049753 45204485817883701407287315)
  ·
    refine ⟨67806728726825552110930973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45204485817883701407287315 67806728726825552110930973)
    ·
      refine ⟨25427523272559582041599115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67806728726825552110930973 25427523272559582041599115)
      ·
        refine ⟨38141284908839373062398673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25427523272559582041599115 38141284908839373062398673)
        ·
          refine ⟨28605963681629529796799005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38141284908839373062398673 28605963681629529796799005)
          ·
            refine ⟨10727236380611073673799627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28605963681629529796799005 10727236380611073673799627)
            ·
              refine ⟨16090854570916610510699441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10727236380611073673799627 16090854570916610510699441)
              ·
                refine ⟨12068140928187457883024581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16090854570916610510699441 12068140928187457883024581)
                ·
                  refine ⟨2262776424035148353067109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12068140928187457883024581 2262776424035148353067109)
                  ·
                    refine ⟨424270579506590316200083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2262776424035148353067109 424270579506590316200083)
                    ·
                      rfl

theorem cell23_2478792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_2478792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478792 prefixEnd_2478792 := by exact prefixLift 2478792
  have htrace : WordTrace (prefixWord ++ tailWord_2478792) baseStart_2478792 baseEnd_2478792 := by
    simpa [prefixWord, tailWord_2478792, baseEnd_2478792] using wordTrace_append hprefix tailTrace_2478792
  have hstable : (prefixWord ++ tailWord_2478792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478792).length < 2 ^ (prefixWord ++ tailWord_2478792).sum := by decide
  have hdescent : baseEnd_2478792 < baseStart_2478792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478832 : List Nat := [2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 3]
def baseStart_2478832 : Nat := 118140960795 + 2478832 * 2 ^ 59
def prefixEnd_2478832 : Nat := 4983230072969 + 3 ^ 40 * 2478832 * 2
def baseEnd_2478832 : Nat := 1272832277745950792100065

theorem tailTrace_2478832 : CollatzResearch.WordTrace tailWord_2478832 prefixEnd_2478832 1272832277745950792100065 := by
  unfold tailWord_2478832
  simp only [CollatzResearch.WordTrace]
  refine ⟨45205215277811244823015375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60273620370414993097353833 45205215277811244823015375)
  ·
    refine ⟨67807822916716867234523063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45205215277811244823015375 67807822916716867234523063)
    ·
      refine ⟨101711734375075300851784595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67807822916716867234523063 101711734375075300851784595)
      ·
        refine ⟨152567601562612951277676893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101711734375075300851784595 152567601562612951277676893)
        ·
          refine ⟨57212850585979856729128835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152567601562612951277676893 57212850585979856729128835)
          ·
            refine ⟨85819275878969785093693253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57212850585979856729128835 85819275878969785093693253)
            ·
              refine ⟨16091114227306834705067485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85819275878969785093693253 16091114227306834705067485)
              ·
                refine ⟨6034167835240063014400307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16091114227306834705067485 6034167835240063014400307)
                ·
                  refine ⟨9051251752860094521600461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6034167835240063014400307 9051251752860094521600461)
                  ·
                    refine ⟨3394219407322535445600173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9051251752860094521600461 3394219407322535445600173)
                    ·
                      refine ⟨1272832277745950792100065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3394219407322535445600173 1272832277745950792100065)
                      ·
                        rfl

theorem cell23_2478832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 3].length) (baseStart_2478832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478832 prefixEnd_2478832 := by exact prefixLift 2478832
  have htrace : WordTrace (prefixWord ++ tailWord_2478832) baseStart_2478832 baseEnd_2478832 := by
    simpa [prefixWord, tailWord_2478832, baseEnd_2478832] using wordTrace_append hprefix tailTrace_2478832
  have hstable : (prefixWord ++ tailWord_2478832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478832).length < 2 ^ (prefixWord ++ tailWord_2478832).sum := by decide
  have hdescent : baseEnd_2478832 < baseStart_2478832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478882 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 1, 8]
def baseStart_2478882 : Nat := 118140960795 + 2478882 * 2 ^ 59
def prefixEnd_2478882 : Nat := 4983230072969 + 3 ^ 40 * 2478882 * 2
def baseEnd_2478882 : Nat := 424285983926225198824945

theorem tailTrace_2478882 : CollatzResearch.WordTrace tailWord_2478882 prefixEnd_2478882 424285983926225198824945 := by
  unfold tailWord_2478882
  simp only [CollatzResearch.WordTrace]
  refine ⟨22603063551360337046337725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60274836136960898790233933 22603063551360337046337725)
  ·
    refine ⟨8476148831760126392376647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22603063551360337046337725 8476148831760126392376647)
    ·
      refine ⟨12714223247640189588564971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8476148831760126392376647 12714223247640189588564971)
      ·
        refine ⟨19071334871460284382847457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12714223247640189588564971 19071334871460284382847457)
        ·
          refine ⟨14303501153595213287135593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19071334871460284382847457 14303501153595213287135593)
          ·
            refine ⟨10727625865196409965351695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14303501153595213287135593 10727625865196409965351695)
            ·
              refine ⟨16091438797794614948027543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10727625865196409965351695 16091438797794614948027543)
              ·
                refine ⟨24137158196691922422041315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16091438797794614948027543 24137158196691922422041315)
                ·
                  refine ⟨36205737295037883633061973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24137158196691922422041315 36205737295037883633061973)
                  ·
                    refine ⟨424285983926225198824945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36205737295037883633061973 424285983926225198824945)
                    ·
                      rfl

theorem cell23_2478882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_2478882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478882 prefixEnd_2478882 := by exact prefixLift 2478882
  have htrace : WordTrace (prefixWord ++ tailWord_2478882) baseStart_2478882 baseEnd_2478882 := by
    simpa [prefixWord, tailWord_2478882, baseEnd_2478882] using wordTrace_append hprefix tailTrace_2478882
  have hstable : (prefixWord ++ tailWord_2478882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478882).length < 2 ^ (prefixWord ++ tailWord_2478882).sum := by decide
  have hdescent : baseEnd_2478882 < baseStart_2478882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478892 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 3]
def baseStart_2478892 : Nat := 118140960795 + 2478892 * 2 ^ 59
def prefixEnd_2478892 : Nat := 4983230072969 + 3 ^ 40 * 2478892 * 2
def baseEnd_2478892 : Nat := 1272863086585220557349789

theorem tailTrace_2478892 : CollatzResearch.WordTrace tailWord_2478892 prefixEnd_2478892 1272863086585220557349789 := by
  unfold tailWord_2478892
  simp only [CollatzResearch.WordTrace]
  refine ⟨45206309467702559946607465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60275079290270079928809953 45206309467702559946607465)
  ·
    refine ⟨33904732100776919959955599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45206309467702559946607465 33904732100776919959955599)
    ·
      refine ⟨50857098151165379939933399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33904732100776919959955599 50857098151165379939933399)
      ·
        refine ⟨76285647226748069909900099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50857098151165379939933399 76285647226748069909900099)
        ·
          refine ⟨114428470840122104864850149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76285647226748069909900099 114428470840122104864850149)
          ·
            refine ⟨21455338282522894662159403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114428470840122104864850149 21455338282522894662159403)
            ·
              refine ⟨32183007423784341993239105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21455338282522894662159403 32183007423784341993239105)
              ·
                refine ⟨24137255567838256494929329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32183007423784341993239105 24137255567838256494929329)
                ·
                  refine ⟨18102941675878692371196997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24137255567838256494929329 18102941675878692371196997)
                  ·
                    refine ⟨3394301564227254819599437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18102941675878692371196997 3394301564227254819599437)
                    ·
                      refine ⟨1272863086585220557349789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3394301564227254819599437 1272863086585220557349789)
                      ·
                        rfl

theorem cell23_2478892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 3].length) (baseStart_2478892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478892 prefixEnd_2478892 := by exact prefixLift 2478892
  have htrace : WordTrace (prefixWord ++ tailWord_2478892) baseStart_2478892 baseEnd_2478892 := by
    simpa [prefixWord, tailWord_2478892, baseEnd_2478892] using wordTrace_append hprefix tailTrace_2478892
  have hstable : (prefixWord ++ tailWord_2478892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478892).length < 2 ^ (prefixWord ++ tailWord_2478892).sum := by decide
  have hdescent : baseEnd_2478892 < baseStart_2478892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478929 : List Nat := [1, 2, 2, 1, 6, 1, 2, 1, 7]
def baseStart_2478929 : Nat := 118140960795 + 2478929 * 2 ^ 59
def prefixEnd_2478929 : Nat := 4983230072969 + 3 ^ 40 * 2478929 * 2
def baseEnd_2478929 : Nat := 141431342818826323620791

theorem tailTrace_2478929 : CollatzResearch.WordTrace tailWord_2478929 prefixEnd_2478929 141431342818826323620791 := by
  unfold tailWord_2478929
  simp only [CollatzResearch.WordTrace]
  refine ⟨90413968436271075212311841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60275978957514050141541227 90413968436271075212311841)
  ·
    refine ⟨67810476327203306409233881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90413968436271075212311841 67810476327203306409233881)
    ·
      refine ⟨50857857245402479806925411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67810476327203306409233881 50857857245402479806925411)
      ·
        refine ⟨76286785868103719710388117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50857857245402479806925411 76286785868103719710388117)
        ·
          refine ⟨3575943087567361861424443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 76286785868103719710388117 3575943087567361861424443)
          ·
            refine ⟨5363914631351042792136665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3575943087567361861424443 5363914631351042792136665)
            ·
              refine ⟨4022935973513282094102499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5363914631351042792136665 4022935973513282094102499)
              ·
                refine ⟨6034403960269923141153749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4022935973513282094102499 6034403960269923141153749)
                ·
                  refine ⟨141431342818826323620791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6034403960269923141153749 141431342818826323620791)
                  ·
                    rfl

theorem cell23_2478929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 7].length) (baseStart_2478929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478929 prefixEnd_2478929 := by exact prefixLift 2478929
  have htrace : WordTrace (prefixWord ++ tailWord_2478929) baseStart_2478929 baseEnd_2478929 := by
    simpa [prefixWord, tailWord_2478929, baseEnd_2478929] using wordTrace_append hprefix tailTrace_2478929
  have hstable : (prefixWord ++ tailWord_2478929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478929).length < 2 ^ (prefixWord ++ tailWord_2478929).sum := by decide
  have hdescent : baseEnd_2478929 < baseStart_2478929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478949 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 2, 5, 2]
def baseStart_2478949 : Nat := 118140960795 + 2478949 * 2 ^ 59
def prefixEnd_2478949 : Nat := 4983230072969 + 3 ^ 40 * 2478949 * 2
def baseEnd_2478949 : Nat := 1272892354982526834337027

theorem tailTrace_2478949 : CollatzResearch.WordTrace tailWord_2478949 prefixEnd_2478949 1272892354982526834337027 := by
  unfold tailWord_2478949
  simp only [CollatzResearch.WordTrace]
  refine ⟨90414697896198618628039901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60276465264132412418693267 90414697896198618628039901)
  ·
    refine ⟨33905511711074481985514963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90414697896198618628039901 33905511711074481985514963)
    ·
      refine ⟨50858267566611722978272445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33905511711074481985514963 50858267566611722978272445)
      ·
        refine ⟨19071850337479396116852167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50858267566611722978272445 19071850337479396116852167)
        ·
          refine ⟨28607775506219094175278251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19071850337479396116852167 28607775506219094175278251)
          ·
            refine ⟨42911663259328641262917377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28607775506219094175278251 42911663259328641262917377)
            ·
              refine ⟨32183747444496480947188033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42911663259328641262917377 32183747444496480947188033)
              ·
                refine ⟨24137810583372360710391025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32183747444496480947188033 24137810583372360710391025)
                ·
                  refine ⟨18103357937529270532793269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24137810583372360710391025 18103357937529270532793269)
                  ·
                    refine ⟨1697189806643369112449369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18103357937529270532793269 1697189806643369112449369)
                    ·
                      refine ⟨1272892354982526834337027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1697189806643369112449369 1272892354982526834337027)
                      ·
                        rfl

theorem cell23_2478949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_2478949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478949 prefixEnd_2478949 := by exact prefixLift 2478949
  have htrace : WordTrace (prefixWord ++ tailWord_2478949) baseStart_2478949 baseEnd_2478949 := by
    simpa [prefixWord, tailWord_2478949, baseEnd_2478949] using wordTrace_append hprefix tailTrace_2478949
  have hstable : (prefixWord ++ tailWord_2478949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478949).length < 2 ^ (prefixWord ++ tailWord_2478949).sum := by decide
  have hdescent : baseEnd_2478949 < baseStart_2478949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478979 : List Nat := [1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 4]
def baseStart_2478979 : Nat := 118140960795 + 2478979 * 2 ^ 59
def prefixEnd_2478979 : Nat := 4983230072969 + 3 ^ 40 * 2478979 * 2
def baseEnd_2478979 : Nat := 1272907759402161716961889

theorem tailTrace_2478979 : CollatzResearch.WordTrace tailWord_2478979 prefixEnd_2478979 1272907759402161716961889 := by
  unfold tailWord_2478979
  simp only [CollatzResearch.WordTrace]
  refine ⟨90415792086089933751631991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60277194724059955834421327 90415792086089933751631991)
  ·
    refine ⟨135623688129134900627447987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90415792086089933751631991 135623688129134900627447987)
    ·
      refine ⟨203435532193702350941171981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135623688129134900627447987 203435532193702350941171981)
      ·
        refine ⟨76288324572638381602939493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203435532193702350941171981 76288324572638381602939493)
        ·
          refine ⟨14304060857369696550551155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76288324572638381602939493 14304060857369696550551155)
          ·
            refine ⟨21456091286054544825826733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14304060857369696550551155 21456091286054544825826733)
            ·
              refine ⟨8046034232270454309685025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21456091286054544825826733 8046034232270454309685025)
              ·
                refine ⟨6034525674202840732263769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8046034232270454309685025 6034525674202840732263769)
                ·
                  refine ⟨4525894255652130549197827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6034525674202840732263769 4525894255652130549197827)
                  ·
                    refine ⟨6788841383478195823796741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4525894255652130549197827 6788841383478195823796741)
                    ·
                      refine ⟨1272907759402161716961889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6788841383478195823796741 1272907759402161716961889)
                      ·
                        rfl

theorem cell23_2478979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_2478979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478979 prefixEnd_2478979 := by exact prefixLift 2478979
  have htrace : WordTrace (prefixWord ++ tailWord_2478979) baseStart_2478979 baseEnd_2478979 := by
    simpa [prefixWord, tailWord_2478979, baseEnd_2478979] using wordTrace_append hprefix tailTrace_2478979
  have hstable : (prefixWord ++ tailWord_2478979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478979).length < 2 ^ (prefixWord ++ tailWord_2478979).sum := by decide
  have hdescent : baseEnd_2478979 < baseStart_2478979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478996 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 1, 6, 2]
def baseStart_2478996 : Nat := 118140960795 + 2478996 * 2 ^ 59
def prefixEnd_2478996 : Nat := 4983230072969 + 3 ^ 40 * 2478996 * 2
def baseEnd_2478996 : Nat := 1272916488573288150449311

theorem tailTrace_2478996 : CollatzResearch.WordTrace tailWord_2478996 prefixEnd_2478996 1272916488573288150449311 := by
  unfold tailWord_2478996
  simp only [CollatzResearch.WordTrace]
  refine ⟨45208206063514172827500421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60277608084685563770000561 45208206063514172827500421)
  ·
    refine ⟨8476538636908907405156329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45208206063514172827500421 8476538636908907405156329)
    ·
      refine ⟨6357403977681680553867247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8476538636908907405156329 6357403977681680553867247)
      ·
        refine ⟨9536105966522520830800871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6357403977681680553867247 9536105966522520830800871)
        ·
          refine ⟨14304158949783781246201307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9536105966522520830800871 14304158949783781246201307)
          ·
            refine ⟨21456238424675671869301961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14304158949783781246201307 21456238424675671869301961)
            ·
              refine ⟨16092178818506753901976471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21456238424675671869301961 16092178818506753901976471)
              ·
                refine ⟨24138268227760130852964707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16092178818506753901976471 24138268227760130852964707)
                ·
                  refine ⟨36207402341640196279447061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24138268227760130852964707 36207402341640196279447061)
                  ·
                    refine ⟨1697221984764384200599081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 36207402341640196279447061 1697221984764384200599081)
                    ·
                      refine ⟨1272916488573288150449311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1697221984764384200599081 1272916488573288150449311)
                      ·
                        rfl

theorem cell23_2478996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_2478996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478996 prefixEnd_2478996 := by exact prefixLift 2478996
  have htrace : WordTrace (prefixWord ++ tailWord_2478996) baseStart_2478996 baseEnd_2478996 := by
    simpa [prefixWord, tailWord_2478996, baseEnd_2478996] using wordTrace_append hprefix tailTrace_2478996
  have hstable : (prefixWord ++ tailWord_2478996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478996).length < 2 ^ (prefixWord ++ tailWord_2478996).sum := by decide
  have hdescent : baseEnd_2478996 < baseStart_2478996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478999 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 4, 2, 3]
def baseStart_2478999 : Nat := 118140960795 + 2478999 * 2 ^ 59
def prefixEnd_2478999 : Nat := 4983230072969 + 3 ^ 40 * 2478999 * 2
def baseEnd_2478999 : Nat := 1272918029015251638711797

theorem tailTrace_2478999 : CollatzResearch.WordTrace tailWord_2478999 prefixEnd_2478999 1272918029015251638711797 := by
  unfold tailWord_2478999
  simp only [CollatzResearch.WordTrace]
  refine ⟨90416521546017477167360051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60277681030678318111573367 90416521546017477167360051)
  ·
    refine ⟨135624782319026215751040077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90416521546017477167360051 135624782319026215751040077)
    ·
      refine ⟨50859293369634830906640029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135624782319026215751040077 50859293369634830906640029)
      ·
        refine ⟨19072235013613061589990011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50859293369634830906640029 19072235013613061589990011)
        ·
          refine ⟨28608352520419592384985017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19072235013613061589990011 28608352520419592384985017)
          ·
            refine ⟨21456264390314694288738763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28608352520419592384985017 21456264390314694288738763)
            ·
              refine ⟨32184396585472041433108145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21456264390314694288738763 32184396585472041433108145)
              ·
                refine ⟨24138297439104031074831109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32184396585472041433108145 24138297439104031074831109)
                ·
                  refine ⟨4525930769832005826530833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24138297439104031074831109 4525930769832005826530833)
                  ·
                    refine ⟨3394448077374004369898125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4525930769832005826530833 3394448077374004369898125)
                    ·
                      refine ⟨1272918029015251638711797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3394448077374004369898125 1272918029015251638711797)
                      ·
                        rfl

theorem cell23_2478999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_2478999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2478999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2478999 prefixEnd_2478999 := by exact prefixLift 2478999
  have htrace : WordTrace (prefixWord ++ tailWord_2478999) baseStart_2478999 baseEnd_2478999 := by
    simpa [prefixWord, tailWord_2478999, baseEnd_2478999] using wordTrace_append hprefix tailTrace_2478999
  have hstable : (prefixWord ++ tailWord_2478999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478999).length < 2 ^ (prefixWord ++ tailWord_2478999).sum := by decide
  have hdescent : baseEnd_2478999 < baseStart_2478999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479040 : List Nat := [2, 1, 1, 2, 3, 5, 2, 2, 1, 4]
def baseStart_2479040 : Nat := 118140960795 + 2479040 * 2 ^ 59
def prefixEnd_2479040 : Nat := 4983230072969 + 3 ^ 40 * 2479040 * 2
def baseEnd_2479040 : Nat := 424313027240695326099703

theorem tailTrace_2479040 : CollatzResearch.WordTrace tailWord_2479040 prefixEnd_2479040 424313027240695326099703 := by
  unfold tailWord_2479040
  simp only [CollatzResearch.WordTrace]
  refine ⟨45209008469434470584801287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60278677959245960779735049 45209008469434470584801287)
  ·
    refine ⟨67813512704151705877201931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45209008469434470584801287 67813512704151705877201931)
    ·
      refine ⟨101720269056227558815802897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67813512704151705877201931 101720269056227558815802897)
      ·
        refine ⟨76290201792170669111852173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101720269056227558815802897 76290201792170669111852173)
        ·
          refine ⟨28608825672064000916944565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76290201792170669111852173 28608825672064000916944565)
          ·
            refine ⟨2682077406756000085963553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28608825672064000916944565 2682077406756000085963553)
            ·
              refine ⟨2011558055067000064472665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2682077406756000085963553 2011558055067000064472665)
              ·
                refine ⟨1508668541300250048354499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2011558055067000064472665 1508668541300250048354499)
                ·
                  refine ⟨2263002811950375072531749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1508668541300250048354499 2263002811950375072531749)
                  ·
                    refine ⟨424313027240695326099703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2263002811950375072531749 424313027240695326099703)
                    ·
                      rfl

theorem cell23_2479040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2, 1, 4].length) (baseStart_2479040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479040 prefixEnd_2479040 := by exact prefixLift 2479040
  have htrace : WordTrace (prefixWord ++ tailWord_2479040) baseStart_2479040 baseEnd_2479040 := by
    simpa [prefixWord, tailWord_2479040, baseEnd_2479040] using wordTrace_append hprefix tailTrace_2479040
  have hstable : (prefixWord ++ tailWord_2479040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479040).length < 2 ^ (prefixWord ++ tailWord_2479040).sum := by decide
  have hdescent : baseEnd_2479040 < baseStart_2479040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479116 : List Nat := [2, 2, 1, 2, 3, 2, 3, 1, 1, 2, 4]
def baseStart_2479116 : Nat := 118140960795 + 2479116 * 2 ^ 59
def prefixEnd_2479116 : Nat := 4983230072969 + 3 ^ 40 * 2479116 * 2
def baseEnd_2479116 : Nat := 1272978106251827680948759

theorem tailTrace_2479116 : CollatzResearch.WordTrace tailWord_2479116 prefixEnd_2479116 1272978106251827680948759 := by
  unfold tailWord_2479116
  simp only [CollatzResearch.WordTrace]
  refine ⟨45210394443296803074684601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60280525924395737432912801 45210394443296803074684601)
  ·
    refine ⟨33907795832472602306013451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45210394443296803074684601 33907795832472602306013451)
    ·
      refine ⟨50861693748708903459020177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33907795832472602306013451 50861693748708903459020177)
      ·
        refine ⟨38146270311531677594265133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50861693748708903459020177 38146270311531677594265133)
        ·
          refine ⟨14304851366824379097849425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38146270311531677594265133 14304851366824379097849425)
          ·
            refine ⟨10728638525118284323387069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14304851366824379097849425 10728638525118284323387069)
            ·
              refine ⟨4023239446919356621270151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10728638525118284323387069 4023239446919356621270151)
              ·
                refine ⟨6034859170379034931905227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4023239446919356621270151 6034859170379034931905227)
                ·
                  refine ⟨9052288755568552397857841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6034859170379034931905227 9052288755568552397857841)
                  ·
                    refine ⟨6789216566676414298393381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9052288755568552397857841 6789216566676414298393381)
                    ·
                      refine ⟨1272978106251827680948759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6789216566676414298393381 1272978106251827680948759)
                      ·
                        rfl

theorem cell23_2479116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_2479116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479116 prefixEnd_2479116 := by exact prefixLift 2479116
  have htrace : WordTrace (prefixWord ++ tailWord_2479116) baseStart_2479116 baseEnd_2479116 := by
    simpa [prefixWord, tailWord_2479116, baseEnd_2479116] using wordTrace_append hprefix tailTrace_2479116
  have hstable : (prefixWord ++ tailWord_2479116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479116).length < 2 ^ (prefixWord ++ tailWord_2479116).sum := by decide
  have hdescent : baseEnd_2479116 < baseStart_2479116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479119 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 7, 3, 3]
def baseStart_2479119 : Nat := 118140960795 + 2479119 * 2 ^ 59
def prefixEnd_2479119 : Nat := 4983230072969 + 3 ^ 40 * 2479119 * 2
def baseEnd_2479119 : Nat := 1272979646693791169211245

theorem tailTrace_2479119 : CollatzResearch.WordTrace tailWord_2479119 prefixEnd_2479119 1272979646693791169211245 := by
  unfold tailWord_2479119
  simp only [CollatzResearch.WordTrace]
  refine ⟨90420898305582737661728411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60280598870388491774485607 90420898305582737661728411)
  ·
    refine ⟨135631347458374106492592617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90420898305582737661728411 135631347458374106492592617)
    ·
      refine ⟨101723510593780579869444463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135631347458374106492592617 101723510593780579869444463)
      ·
        refine ⟨152585265890670869804166695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101723510593780579869444463 152585265890670869804166695)
        ·
          refine ⟨228877898836006304706250043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152585265890670869804166695 228877898836006304706250043)
          ·
            refine ⟨343316848254009457059375065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228877898836006304706250043 343316848254009457059375065)
            ·
              refine ⟨257487636190507092794531299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 343316848254009457059375065 257487636190507092794531299)
              ·
                refine ⟨386231454285760639191796949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257487636190507092794531299 386231454285760639191796949)
                ·
                  refine ⟨9052299709822514981057741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 386231454285760639191796949 9052299709822514981057741)
                  ·
                    refine ⟨3394612391183443117896653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9052299709822514981057741 3394612391183443117896653)
                    ·
                      refine ⟨1272979646693791169211245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3394612391183443117896653 1272979646693791169211245)
                      ·
                        rfl

theorem cell23_2479119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3, 3].length) (baseStart_2479119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479119 prefixEnd_2479119 := by exact prefixLift 2479119
  have htrace : WordTrace (prefixWord ++ tailWord_2479119) baseStart_2479119 baseEnd_2479119 := by
    simpa [prefixWord, tailWord_2479119, baseEnd_2479119] using wordTrace_append hprefix tailTrace_2479119
  have hstable : (prefixWord ++ tailWord_2479119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479119).length < 2 ^ (prefixWord ++ tailWord_2479119).sum := by decide
  have hdescent : baseEnd_2479119 < baseStart_2479119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479137 : List Nat := [1, 2, 3, 2, 3, 1, 3, 3, 1, 2, 2]
def baseStart_2479137 : Nat := 118140960795 + 2479137 * 2 ^ 59
def prefixEnd_2479137 : Nat := 4983230072969 + 3 ^ 40 * 2479137 * 2
def baseEnd_2479137 : Nat := 1272988889345572098786163

theorem tailTrace_2479137 : CollatzResearch.WordTrace tailWord_2479137 prefixEnd_2479137 1272988889345572098786163 := by
  unfold tailWord_2479137
  simp only [CollatzResearch.WordTrace]
  refine ⟨90421554819517526735883665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60281036546345017823922443 90421554819517526735883665)
  ·
    refine ⟨67816166114638145051912749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90421554819517526735883665 67816166114638145051912749)
    ·
      refine ⟨25431062292989304394467281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67816166114638145051912749 25431062292989304394467281)
      ·
        refine ⟨19073296719741978295850461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25431062292989304394467281 19073296719741978295850461)
        ·
          refine ⟨7152486269903241860943923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19073296719741978295850461 7152486269903241860943923)
          ·
            refine ⟨10728729404854862791415885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7152486269903241860943923 10728729404854862791415885)
            ·
              refine ⟨4023273526820573546780957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10728729404854862791415885 4023273526820573546780957)
              ·
                refine ⟨1508727572557715080042859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4023273526820573546780957 1508727572557715080042859)
                ·
                  refine ⟨2263091358836572620064289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1508727572557715080042859 2263091358836572620064289)
                  ·
                    refine ⟨1697318519127429465048217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2263091358836572620064289 1697318519127429465048217)
                    ·
                      refine ⟨1272988889345572098786163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1697318519127429465048217 1272988889345572098786163)
                      ·
                        rfl

theorem cell23_2479137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_2479137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479137 prefixEnd_2479137 := by exact prefixLift 2479137
  have htrace : WordTrace (prefixWord ++ tailWord_2479137) baseStart_2479137 baseEnd_2479137 := by
    simpa [prefixWord, tailWord_2479137, baseEnd_2479137] using wordTrace_append hprefix tailTrace_2479137
  have hstable : (prefixWord ++ tailWord_2479137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479137).length < 2 ^ (prefixWord ++ tailWord_2479137).sum := by decide
  have hdescent : baseEnd_2479137 < baseStart_2479137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479153 : List Nat := [1, 2, 2, 3, 1, 2, 2, 4, 2, 1, 3]
def baseStart_2479153 : Nat := 118140960795 + 2479153 * 2 ^ 59
def prefixEnd_2479153 : Nat := 4983230072969 + 3 ^ 40 * 2479153 * 2
def baseEnd_2479153 : Nat := 1272997105036044036186089

theorem tailTrace_2479153 : CollatzResearch.WordTrace tailWord_2479153 prefixEnd_2479153 1272997105036044036186089 := by
  unfold tailWord_2479153
  simp only [CollatzResearch.WordTrace]
  refine ⟨90422138387459561468466113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60281425591639707645644075 90422138387459561468466113)
  ·
    refine ⟨67816603790594671101349585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90422138387459561468466113 67816603790594671101349585)
    ·
      refine ⟨50862452842946003326012189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67816603790594671101349585 50862452842946003326012189)
      ·
        refine ⟨19073419816104751247254571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50862452842946003326012189 19073419816104751247254571)
        ·
          refine ⟨28610129724157126870881857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19073419816104751247254571 28610129724157126870881857)
          ·
            refine ⟨21457597293117845153161393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28610129724157126870881857 21457597293117845153161393)
            ·
              refine ⟨16093197969838383864871045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21457597293117845153161393 16093197969838383864871045)
              ·
                refine ⟨3017474619344696974663321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16093197969838383864871045 3017474619344696974663321)
                ·
                  refine ⟨2263105964508522730997491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3017474619344696974663321 2263105964508522730997491)
                  ·
                    refine ⟨3394658946762784096496237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2263105964508522730997491 3394658946762784096496237)
                    ·
                      refine ⟨1272997105036044036186089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3394658946762784096496237 1272997105036044036186089)
                      ·
                        rfl

theorem cell23_2479153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_2479153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479153 prefixEnd_2479153 := by exact prefixLift 2479153
  have htrace : WordTrace (prefixWord ++ tailWord_2479153) baseStart_2479153 baseEnd_2479153 := by
    simpa [prefixWord, tailWord_2479153, baseEnd_2479153] using wordTrace_append hprefix tailTrace_2479153
  have hstable : (prefixWord ++ tailWord_2479153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479153).length < 2 ^ (prefixWord ++ tailWord_2479153).sum := by decide
  have hdescent : baseEnd_2479153 < baseStart_2479153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479159 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 4]
def baseStart_2479159 : Nat := 118140960795 + 2479159 * 2 ^ 59
def prefixEnd_2479159 : Nat := 4983230072969 + 3 ^ 40 * 2479159 * 2
def baseEnd_2479159 : Nat := 1273000185919971012711061

theorem tailTrace_2479159 : CollatzResearch.WordTrace tailWord_2479159 prefixEnd_2479159 1273000185919971012711061 := by
  unfold tailWord_2479159
  simp only [CollatzResearch.WordTrace]
  refine ⟨90422357225437824493184531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60281571483625216328789687 90422357225437824493184531)
  ·
    refine ⟨135633535838156736739776797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90422357225437824493184531 135633535838156736739776797)
    ·
      refine ⟨50862575939308776277416299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135633535838156736739776797 50862575939308776277416299)
      ·
        refine ⟨76293863908963164416124449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50862575939308776277416299 76293863908963164416124449)
        ·
          refine ⟨57220397931722373312093337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76293863908963164416124449 57220397931722373312093337)
          ·
            refine ⟨42915298448791779984070003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57220397931722373312093337 42915298448791779984070003)
            ·
              refine ⟨64372947673187669976105005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42915298448791779984070003 64372947673187669976105005)
              ·
                refine ⟨24139855377445376241039377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64372947673187669976105005 24139855377445376241039377)
                ·
                  refine ⟨18104891533084032180779533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24139855377445376241039377 18104891533084032180779533)
                  ·
                    refine ⟨6789334324906512067792325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18104891533084032180779533 6789334324906512067792325)
                    ·
                      refine ⟨1273000185919971012711061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6789334324906512067792325 1273000185919971012711061)
                      ·
                        rfl

theorem cell23_2479159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_2479159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479159 prefixEnd_2479159 := by exact prefixLift 2479159
  have htrace : WordTrace (prefixWord ++ tailWord_2479159) baseStart_2479159 baseEnd_2479159 := by
    simpa [prefixWord, tailWord_2479159, baseEnd_2479159] using wordTrace_append hprefix tailTrace_2479159
  have hstable : (prefixWord ++ tailWord_2479159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479159).length < 2 ^ (prefixWord ++ tailWord_2479159).sum := by decide
  have hdescent : baseEnd_2479159 < baseStart_2479159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479193 : List Nat := [1, 2, 1, 2, 2, 1, 2, 4, 4, 2, 2]
def baseStart_2479193 : Nat := 118140960795 + 2479193 * 2 ^ 59
def prefixEnd_2479193 : Nat := 4983230072969 + 3 ^ 40 * 2479193 * 2
def baseEnd_2479193 : Nat := 1273017644262223879685905

theorem tailTrace_2479193 : CollatzResearch.WordTrace tailWord_2479193 prefixEnd_2479193 1273017644262223879685905 := by
  unfold tailWord_2479193
  simp only [CollatzResearch.WordTrace]
  refine ⟨90423597307314648299922233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60282398204876432199948155 90423597307314648299922233)
  ·
    refine ⟨67817697980485986224941675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90423597307314648299922233 67817697980485986224941675)
    ·
      refine ⟨101726546970728979337412513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67817697980485986224941675 101726546970728979337412513)
      ·
        refine ⟨76294910228046734503059385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101726546970728979337412513 76294910228046734503059385)
        ·
          refine ⟨57221182671035050877294539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76294910228046734503059385 57221182671035050877294539)
          ·
            refine ⟨85831774006552576315941809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57221182671035050877294539 85831774006552576315941809)
            ·
              refine ⟨64373830504914432236956357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85831774006552576315941809 64373830504914432236956357)
              ·
                refine ⟨12070093219671456044429317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64373830504914432236956357 12070093219671456044429317)
                ·
                  refine ⟨2263142478688398008330497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12070093219671456044429317 2263142478688398008330497)
                  ·
                    refine ⟨1697356859016298506247873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2263142478688398008330497 1697356859016298506247873)
                    ·
                      refine ⟨1273017644262223879685905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1697356859016298506247873 1273017644262223879685905)
                      ·
                        rfl

theorem cell23_2479193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4, 2, 2].length) (baseStart_2479193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479193 prefixEnd_2479193 := by exact prefixLift 2479193
  have htrace : WordTrace (prefixWord ++ tailWord_2479193) baseStart_2479193 baseEnd_2479193 := by
    simpa [prefixWord, tailWord_2479193, baseEnd_2479193] using wordTrace_append hprefix tailTrace_2479193
  have hstable : (prefixWord ++ tailWord_2479193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479193).length < 2 ^ (prefixWord ++ tailWord_2479193).sum := by decide
  have hdescent : baseEnd_2479193 < baseStart_2479193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479196 : List Nat := [2, 2, 4, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_2479196 : Nat := 118140960795 + 2479196 * 2 ^ 59
def prefixEnd_2479196 : Nat := 4983230072969 + 3 ^ 40 * 2479196 * 2
def baseEnd_2479196 : Nat := 1273019184704187367948391

theorem tailTrace_2479196 : CollatzResearch.WordTrace tailWord_2479196 prefixEnd_2479196 1273019184704187367948391 := by
  unfold tailWord_2479196
  simp only [CollatzResearch.WordTrace]
  refine ⟨45211853363151889906140721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60282471150869186541520961 45211853363151889906140721)
  ·
    refine ⟨33908890022363917429605541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45211853363151889906140721 33908890022363917429605541)
    ·
      refine ⟨6357916879193234518051039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33908890022363917429605541 6357916879193234518051039)
      ·
        refine ⟨9536875318789851777076559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6357916879193234518051039 9536875318789851777076559)
        ·
          refine ⟨14305312978184777665614839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9536875318789851777076559 14305312978184777665614839)
          ·
            refine ⟨21457969467277166498422259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14305312978184777665614839 21457969467277166498422259)
            ·
              refine ⟨32186954200915749747633389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21457969467277166498422259 32186954200915749747633389)
              ·
                refine ⟨12070107825343406155362521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32186954200915749747633389 12070107825343406155362521)
                ·
                  refine ⟨9052580869007554616521891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12070107825343406155362521 9052580869007554616521891)
                  ·
                    refine ⟨13578871303511331924782837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9052580869007554616521891 13578871303511331924782837)
                    ·
                      refine ⟨1273019184704187367948391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13578871303511331924782837 1273019184704187367948391)
                      ·
                        rfl

theorem cell23_2479196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_2479196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479196 prefixEnd_2479196 := by exact prefixLift 2479196
  have htrace : WordTrace (prefixWord ++ tailWord_2479196) baseStart_2479196 baseEnd_2479196 := by
    simpa [prefixWord, tailWord_2479196, baseEnd_2479196] using wordTrace_append hprefix tailTrace_2479196
  have hstable : (prefixWord ++ tailWord_2479196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479196).length < 2 ^ (prefixWord ++ tailWord_2479196).sum := by decide
  have hdescent : baseEnd_2479196 < baseStart_2479196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479250 : List Nat := [3, 2, 3, 1, 1, 3, 2, 3, 5]
def baseStart_2479250 : Nat := 118140960795 + 2479250 * 2 ^ 59
def prefixEnd_2479250 : Nat := 4983230072969 + 3 ^ 40 * 2479250 * 2
def baseEnd_2479250 : Nat := 141449656962170017408127

theorem tailTrace_2479250 : CollatzResearch.WordTrace tailWord_2479250 prefixEnd_2479250 141449656962170017408127 := by
  unfold tailWord_2479250
  simp only [CollatzResearch.WordTrace]
  refine ⟨22606419067027036758686801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60283784178738764689831469 22606419067027036758686801)
  ·
    refine ⟨16954814300270277569015101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22606419067027036758686801 16954814300270277569015101)
    ·
      refine ⟨6358055362601354088380663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16954814300270277569015101 6358055362601354088380663)
      ·
        refine ⟨9537083043902031132570995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6358055362601354088380663 9537083043902031132570995)
        ·
          refine ⟨14305624565853046698856493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9537083043902031132570995 14305624565853046698856493)
          ·
            refine ⟨5364609212194892512071185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14305624565853046698856493 5364609212194892512071185)
            ·
              refine ⟨4023456909146169384053389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5364609212194892512071185 4023456909146169384053389)
              ·
                refine ⟨1508796340929813519020021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4023456909146169384053389 1508796340929813519020021)
                ·
                  refine ⟨141449656962170017408127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1508796340929813519020021 141449656962170017408127)
                  ·
                    rfl

theorem cell23_2479250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3, 5].length) (baseStart_2479250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479250 prefixEnd_2479250 := by exact prefixLift 2479250
  have htrace : WordTrace (prefixWord ++ tailWord_2479250) baseStart_2479250 baseEnd_2479250 := by
    simpa [prefixWord, tailWord_2479250, baseEnd_2479250] using wordTrace_append hprefix tailTrace_2479250
  have hstable : (prefixWord ++ tailWord_2479250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479250).length < 2 ^ (prefixWord ++ tailWord_2479250).sum := by decide
  have hdescent : baseEnd_2479250 < baseStart_2479250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479283 : List Nat := [1, 1, 1, 2, 3, 2, 4, 1, 2, 4, 2]
def baseStart_2479283 : Nat := 118140960795 + 2479283 * 2 ^ 59
def prefixEnd_2479283 : Nat := 4983230072969 + 3 ^ 40 * 2479283 * 2
def baseEnd_2479283 : Nat := 1273063857521128527560491

theorem tailTrace_2479283 : CollatzResearch.WordTrace tailWord_2479283 prefixEnd_2479283 1273063857521128527560491 := by
  unfold tailWord_2479283
  simp only [CollatzResearch.WordTrace]
  refine ⟨90426879876988593670698503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60284586584659062447132335 90426879876988593670698503)
  ·
    refine ⟨135640319815482890506047755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90426879876988593670698503 135640319815482890506047755)
    ·
      refine ⟨203460479723224335759071633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135640319815482890506047755 203460479723224335759071633)
      ·
        refine ⟨152595359792418251819303725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203460479723224335759071633 152595359792418251819303725)
        ·
          refine ⟨57223259922156844432238897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152595359792418251819303725 57223259922156844432238897)
          ·
            refine ⟨42917444941617633324179173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57223259922156844432238897 42917444941617633324179173)
            ·
              refine ⟨8047020926553306248283595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42917444941617633324179173 8047020926553306248283595)
              ·
                refine ⟨12070531389829959372425393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8047020926553306248283595 12070531389829959372425393)
                ·
                  refine ⟨9052898542372469529319045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12070531389829959372425393 9052898542372469529319045)
                  ·
                    refine ⟨1697418476694838036747321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9052898542372469529319045 1697418476694838036747321)
                    ·
                      refine ⟨1273063857521128527560491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1697418476694838036747321 1273063857521128527560491)
                      ·
                        rfl

theorem cell23_2479283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 4, 2].length) (baseStart_2479283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479283 prefixEnd_2479283 := by exact prefixLift 2479283
  have htrace : WordTrace (prefixWord ++ tailWord_2479283) baseStart_2479283 baseEnd_2479283 := by
    simpa [prefixWord, tailWord_2479283, baseEnd_2479283] using wordTrace_append hprefix tailTrace_2479283
  have hstable : (prefixWord ++ tailWord_2479283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479283).length < 2 ^ (prefixWord ++ tailWord_2479283).sum := by decide
  have hdescent : baseEnd_2479283 < baseStart_2479283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479293 : List Nat := [1, 4, 1, 2, 1, 1, 4, 2, 3, 4]
def baseStart_2479293 : Nat := 118140960795 + 2479293 * 2 ^ 59
def prefixEnd_2479293 : Nat := 4983230072969 + 3 ^ 40 * 2479293 * 2
def baseEnd_2479293 : Nat := 424356330775891162811815

theorem tailTrace_2479293 : CollatzResearch.WordTrace tailWord_2479293 prefixEnd_2479293 424356330775891162811815 := by
  unfold tailWord_2479293
  simp only [CollatzResearch.WordTrace]
  refine ⟨90427244606952365378562533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60284829737968243585708355 90427244606952365378562533)
  ·
    refine ⟨16955108363803568508480475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90427244606952365378562533 16955108363803568508480475)
    ·
      refine ⟨25432662545705352762720713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16955108363803568508480475 25432662545705352762720713)
      ·
        refine ⟨19074496909279014572040535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25432662545705352762720713 19074496909279014572040535)
        ·
          refine ⟨28611745363918521858060803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19074496909279014572040535 28611745363918521858060803)
          ·
            refine ⟨42917618045877782787091205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28611745363918521858060803 42917618045877782787091205)
            ·
              refine ⟨8047053383602084272579601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42917618045877782787091205 8047053383602084272579601)
              ·
                refine ⟨6035290037701563204434701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8047053383602084272579601 6035290037701563204434701)
                ·
                  refine ⟨2263233764138086201663013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6035290037701563204434701 2263233764138086201663013)
                  ·
                    refine ⟨424356330775891162811815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2263233764138086201663013 424356330775891162811815)
                    ·
                      rfl

theorem cell23_2479293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_2479293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479293 prefixEnd_2479293 := by exact prefixLift 2479293
  have htrace : WordTrace (prefixWord ++ tailWord_2479293) baseStart_2479293 baseEnd_2479293 := by
    simpa [prefixWord, tailWord_2479293, baseEnd_2479293] using wordTrace_append hprefix tailTrace_2479293
  have hstable : (prefixWord ++ tailWord_2479293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479293).length < 2 ^ (prefixWord ++ tailWord_2479293).sum := by decide
  have hdescent : baseEnd_2479293 < baseStart_2479293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479306 : List Nat := [3, 1, 2, 1, 3, 2, 1, 2, 8]
def baseStart_2479306 : Nat := 118140960795 + 2479306 * 2 ^ 59
def prefixEnd_2479306 : Nat := 4983230072969 + 3 ^ 40 * 2479306 * 2
def baseEnd_2479306 : Nat := 141452851952909104174765

theorem tailTrace_2479306 : CollatzResearch.WordTrace tailWord_2479306 prefixEnd_2479306 141452851952909104174765 := by
  unfold tailWord_2479306
  simp only [CollatzResearch.WordTrace]
  refine ⟨22606929688976317149696443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60285145837270179065857181 22606929688976317149696443)
  ·
    refine ⟨33910394533464475724544665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22606929688976317149696443 33910394533464475724544665)
    ·
      refine ⟨25432795900098356793408499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33910394533464475724544665 25432795900098356793408499)
      ·
        refine ⟨38149193850147535190112749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25432795900098356793408499 38149193850147535190112749)
        ·
          refine ⟨14305947693805325696292281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38149193850147535190112749 14305947693805325696292281)
          ·
            refine ⟨10729460770353994272219211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14305947693805325696292281 10729460770353994272219211)
            ·
              refine ⟨16094191155530991408328817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10729460770353994272219211 16094191155530991408328817)
              ·
                refine ⟨12070643366648243556246613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16094191155530991408328817 12070643366648243556246613)
                ·
                  refine ⟨141452851952909104174765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12070643366648243556246613 141452851952909104174765)
                  ·
                    rfl

theorem cell23_2479306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 8].length) (baseStart_2479306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479306 prefixEnd_2479306 := by exact prefixLift 2479306
  have htrace : WordTrace (prefixWord ++ tailWord_2479306) baseStart_2479306 baseEnd_2479306 := by
    simpa [prefixWord, tailWord_2479306, baseEnd_2479306] using wordTrace_append hprefix tailTrace_2479306
  have hstable : (prefixWord ++ tailWord_2479306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479306).length < 2 ^ (prefixWord ++ tailWord_2479306).sum := by decide
  have hdescent : baseEnd_2479306 < baseStart_2479306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479320 : List Nat := [2, 1, 2, 2, 5, 1, 1, 2, 2, 2, 3]
def baseStart_2479320 : Nat := 118140960795 + 2479320 * 2 ^ 59
def prefixEnd_2479320 : Nat := 4983230072969 + 3 ^ 40 * 2479320 * 2
def baseEnd_2479320 : Nat := 1273082856305344882797821

theorem tailTrace_2479320 : CollatzResearch.WordTrace tailWord_2479320 prefixEnd_2479320 1273082856305344882797821 := by
  unfold tailWord_2479320
  simp only [CollatzResearch.WordTrace]
  refine ⟨45214114688927274494897707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60285486251903032659863609 45214114688927274494897707)
  ·
    refine ⟨67821172033390911742346561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45214114688927274494897707 67821172033390911742346561)
    ·
      refine ⟨50865879025043183806759921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67821172033390911742346561 50865879025043183806759921)
      ·
        refine ⟨38149409268782387855069941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50865879025043183806759921 38149409268782387855069941)
        ·
          refine ⟨3576507118948348861412807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38149409268782387855069941 3576507118948348861412807)
          ·
            refine ⟨5364760678422523292119211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3576507118948348861412807 5364760678422523292119211)
            ·
              refine ⟨8047141017633784938178817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5364760678422523292119211 8047141017633784938178817)
              ·
                refine ⟨6035355763225338703634113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8047141017633784938178817 6035355763225338703634113)
                ·
                  refine ⟨4526516822419004027725585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6035355763225338703634113 4526516822419004027725585)
                  ·
                    refine ⟨3394887616814253020794189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4526516822419004027725585 3394887616814253020794189)
                    ·
                      refine ⟨1273082856305344882797821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3394887616814253020794189 1273082856305344882797821)
                      ·
                        rfl

theorem cell23_2479320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_2479320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479320 prefixEnd_2479320 := by exact prefixLift 2479320
  have htrace : WordTrace (prefixWord ++ tailWord_2479320) baseStart_2479320 baseEnd_2479320 := by
    simpa [prefixWord, tailWord_2479320, baseEnd_2479320] using wordTrace_append hprefix tailTrace_2479320
  have hstable : (prefixWord ++ tailWord_2479320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479320).length < 2 ^ (prefixWord ++ tailWord_2479320).sum := by decide
  have hdescent : baseEnd_2479320 < baseStart_2479320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479340 : List Nat := [2, 2, 1, 1, 2, 6, 2, 1, 6]
def baseStart_2479340 : Nat := 118140960795 + 2479340 * 2 ^ 59
def prefixEnd_2479340 : Nat := 4983230072969 + 3 ^ 40 * 2479340 * 2
def baseEnd_2479340 : Nat := 141454791768714978283081

theorem tailTrace_2479340 : CollatzResearch.WordTrace tailWord_2479340 prefixEnd_2479340 141454791768714978283081 := by
  unfold tailWord_2479340
  simp only [CollatzResearch.WordTrace]
  refine ⟨45214479418891046202761737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60285972558521394937015649 45214479418891046202761737)
  ·
    refine ⟨33910859564168284652071303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45214479418891046202761737 33910859564168284652071303)
    ·
      refine ⟨50866289346252426978106955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33910859564168284652071303 50866289346252426978106955)
      ·
        refine ⟨76299434019378640467160433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50866289346252426978106955 76299434019378640467160433)
        ·
          refine ⟨57224575514533980350370325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76299434019378640467160433 57224575514533980350370325)
          ·
            refine ⟨2682401977243780328923609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57224575514533980350370325 2682401977243780328923609)
            ·
              refine ⟨2011801482932835246692707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2682401977243780328923609 2011801482932835246692707)
              ·
                refine ⟨3017702224399252870039061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2011801482932835246692707 3017702224399252870039061)
                ·
                  refine ⟨141454791768714978283081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3017702224399252870039061 141454791768714978283081)
                  ·
                    rfl

theorem cell23_2479340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 6].length) (baseStart_2479340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479340 prefixEnd_2479340 := by exact prefixLift 2479340
  have htrace : WordTrace (prefixWord ++ tailWord_2479340) baseStart_2479340 baseEnd_2479340 := by
    simpa [prefixWord, tailWord_2479340, baseEnd_2479340] using wordTrace_append hprefix tailTrace_2479340
  have hstable : (prefixWord ++ tailWord_2479340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479340).length < 2 ^ (prefixWord ++ tailWord_2479340).sum := by decide
  have hdescent : baseEnd_2479340 < baseStart_2479340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479350 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3]
def baseStart_2479350 : Nat := 118140960795 + 2479350 * 2 ^ 59
def prefixEnd_2479350 : Nat := 4983230072969 + 3 ^ 40 * 2479350 * 2
def baseEnd_2479350 : Nat := 1273098260724979765422683

theorem tailTrace_2479350 : CollatzResearch.WordTrace tailWord_2479350 prefixEnd_2479350 1273098260724979765422683 := by
  unfold tailWord_2479350
  simp only [CollatzResearch.WordTrace]
  refine ⟨5651832722984116507086719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60286215711830576075591669 5651832722984116507086719)
  ·
    refine ⟨8477749084476174760630079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5651832722984116507086719 8477749084476174760630079)
    ·
      refine ⟨12716623626714262140945119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8477749084476174760630079 12716623626714262140945119)
      ·
        refine ⟨19074935440071393211417679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12716623626714262140945119 19074935440071393211417679)
        ·
          refine ⟨28612403160107089817126519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19074935440071393211417679 28612403160107089817126519)
          ·
            refine ⟨42918604740160634725689779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28612403160107089817126519 42918604740160634725689779)
            ·
              refine ⟨64377907110240952088534669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42918604740160634725689779 64377907110240952088534669)
              ·
                refine ⟨24141715166340357033200501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64377907110240952088534669 24141715166340357033200501)
                ·
                  refine ⟨2263285796844408471862547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24141715166340357033200501 2263285796844408471862547)
                  ·
                    refine ⟨3394928695266612707793821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2263285796844408471862547 3394928695266612707793821)
                    ·
                      refine ⟨1273098260724979765422683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3394928695266612707793821 1273098260724979765422683)
                      ·
                        rfl

theorem cell23_2479350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_2479350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479350 prefixEnd_2479350 := by exact prefixLift 2479350
  have htrace : WordTrace (prefixWord ++ tailWord_2479350) baseStart_2479350 baseEnd_2479350 := by
    simpa [prefixWord, tailWord_2479350, baseEnd_2479350] using wordTrace_append hprefix tailTrace_2479350
  have hstable : (prefixWord ++ tailWord_2479350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479350).length < 2 ^ (prefixWord ++ tailWord_2479350).sum := by decide
  have hdescent : baseEnd_2479350 < baseStart_2479350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479378 : List Nat := [3, 2, 4, 2, 1, 2, 2, 2, 1, 4]
def baseStart_2479378 : Nat := 118140960795 + 2479378 * 2 ^ 59
def prefixEnd_2479378 : Nat := 4983230072969 + 3 ^ 40 * 2479378 * 2
def baseEnd_2479378 : Nat := 424370879394435218624185

theorem tailTrace_2479378 : CollatzResearch.WordTrace tailWord_2479378 prefixEnd_2479378 424370879394435218624185 := by
  unfold tailWord_2479378
  simp only [CollatzResearch.WordTrace]
  refine ⟨22607586202911106223851697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60286896541096283263604525 22607586202911106223851697)
  ·
    refine ⟨16955689652183329667888773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22607586202911106223851697 16955689652183329667888773)
    ·
      refine ⟨3179191809784374312729145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16955689652183329667888773 3179191809784374312729145)
      ·
        refine ⟨2384393857338280734546859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3179191809784374312729145 2384393857338280734546859)
        ·
          refine ⟨3576590786007421101820289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2384393857338280734546859 3576590786007421101820289)
          ·
            refine ⟨2682443089505565826365217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3576590786007421101820289 2682443089505565826365217)
            ·
              refine ⟨2011832317129174369773913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2682443089505565826365217 2011832317129174369773913)
              ·
                refine ⟨1508874237846880777330435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2011832317129174369773913 1508874237846880777330435)
                ·
                  refine ⟨2263311356770321165995653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1508874237846880777330435 2263311356770321165995653)
                  ·
                    refine ⟨424370879394435218624185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2263311356770321165995653 424370879394435218624185)
                    ·
                      rfl

theorem cell23_2479378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_2479378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479378 prefixEnd_2479378 := by exact prefixLift 2479378
  have htrace : WordTrace (prefixWord ++ tailWord_2479378) baseStart_2479378 baseEnd_2479378 := by
    simpa [prefixWord, tailWord_2479378, baseEnd_2479378] using wordTrace_append hprefix tailTrace_2479378
  have hstable : (prefixWord ++ tailWord_2479378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479378).length < 2 ^ (prefixWord ++ tailWord_2479378).sum := by decide
  have hdescent : baseEnd_2479378 < baseStart_2479378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479384 : List Nat := [2, 1, 2, 3, 1, 3, 4, 2, 1, 1, 3]
def baseStart_2479384 : Nat := 118140960795 + 2479384 * 2 ^ 59
def prefixEnd_2479384 : Nat := 4983230072969 + 3 ^ 40 * 2479384 * 2
def baseEnd_2479384 : Nat := 1273115719067232632397527

theorem tailTrace_2479384 : CollatzResearch.WordTrace tailWord_2479384 prefixEnd_2479384 1273115719067232632397527 := by
  unfold tailWord_2479384
  simp only [CollatzResearch.WordTrace]
  refine ⟨45215281824811343960062603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60287042433081791946750137 45215281824811343960062603)
  ·
    refine ⟨67822922737217015940093905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45215281824811343960062603 67822922737217015940093905)
    ·
      refine ⟨50867192052912761955070429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67822922737217015940093905 50867192052912761955070429)
      ·
        refine ⟨19075197019842285733151411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50867192052912761955070429 19075197019842285733151411)
        ·
          refine ⟨28612795529763428599727117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19075197019842285733151411 28612795529763428599727117)
          ·
            refine ⟨10729798323661285724897669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28612795529763428599727117 10729798323661285724897669)
            ·
              refine ⟨2011837185686491073418313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10729798323661285724897669 2011837185686491073418313)
              ·
                refine ⟨1508877889264868305063735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2011837185686491073418313 1508877889264868305063735)
                ·
                  refine ⟨2263316833897302457595603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1508877889264868305063735 2263316833897302457595603)
                  ·
                    refine ⟨3394975250845953686393405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2263316833897302457595603 3394975250845953686393405)
                    ·
                      refine ⟨1273115719067232632397527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3394975250845953686393405 1273115719067232632397527)
                      ·
                        rfl

theorem cell23_2479384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_2479384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479384 prefixEnd_2479384 := by exact prefixLift 2479384
  have htrace : WordTrace (prefixWord ++ tailWord_2479384) baseStart_2479384 baseEnd_2479384 := by
    simpa [prefixWord, tailWord_2479384, baseEnd_2479384] using wordTrace_append hprefix tailTrace_2479384
  have hstable : (prefixWord ++ tailWord_2479384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479384).length < 2 ^ (prefixWord ++ tailWord_2479384).sum := by decide
  have hdescent : baseEnd_2479384 < baseStart_2479384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479400 : List Nat := [2, 1, 5, 1, 2, 2, 2, 1, 1, 6]
def baseStart_2479400 : Nat := 118140960795 + 2479400 * 2 ^ 59
def prefixEnd_2479400 : Nat := 4983230072969 + 3 ^ 40 * 2479400 * 2
def baseEnd_2479400 : Nat := 424374644919234856599151

theorem tailTrace_2479400 : CollatzResearch.WordTrace tailWord_2479400 prefixEnd_2479400 424374644919234856599151 := by
  unfold tailWord_2479400
  simp only [CollatzResearch.WordTrace]
  refine ⟨45215573608782361326353827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60287431478376481768471769 45215573608782361326353827)
  ·
    refine ⟨67823360413173541989530741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45215573608782361326353827 67823360413173541989530741)
    ·
      refine ⟨6358440038735019561518507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67823360413173541989530741 6358440038735019561518507)
      ·
        refine ⟨9537660058102529342277761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6358440038735019561518507 9537660058102529342277761)
        ·
          refine ⟨7153245043576897006708321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9537660058102529342277761 7153245043576897006708321)
          ·
            refine ⟨5364933782682672755031241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7153245043576897006708321 5364933782682672755031241)
            ·
              refine ⟨4023700337012004566273431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5364933782682672755031241 4023700337012004566273431)
              ·
                refine ⟨6035550505518006849410147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4023700337012004566273431 6035550505518006849410147)
                ·
                  refine ⟨9053325758277010274115221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6035550505518006849410147 9053325758277010274115221)
                  ·
                    refine ⟨424374644919234856599151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9053325758277010274115221 424374644919234856599151)
                    ·
                      rfl

theorem cell23_2479400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_2479400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479400 prefixEnd_2479400 := by exact prefixLift 2479400
  have htrace : WordTrace (prefixWord ++ tailWord_2479400) baseStart_2479400 baseEnd_2479400 := by
    simpa [prefixWord, tailWord_2479400, baseEnd_2479400] using wordTrace_append hprefix tailTrace_2479400
  have hstable : (prefixWord ++ tailWord_2479400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479400).length < 2 ^ (prefixWord ++ tailWord_2479400).sum := by decide
  have hdescent : baseEnd_2479400 < baseStart_2479400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479410 : List Nat := [3, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3]
def baseStart_2479410 : Nat := 118140960795 + 2479410 * 2 ^ 59
def prefixEnd_2479410 : Nat := 4983230072969 + 3 ^ 40 * 2479410 * 2
def baseEnd_2479410 : Nat := 1273129069564249530672407

theorem tailTrace_2479410 : CollatzResearch.WordTrace tailWord_2479410 prefixEnd_2479410 1273129069564249530672407 := by
  unfold tailWord_2479410
  simp only [CollatzResearch.WordTrace]
  refine ⟨22607877986882123590142921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60287674631685662907047789 22607877986882123590142921)
  ·
    refine ⟨16955908490161592692607191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22607877986882123590142921 16955908490161592692607191)
    ·
      refine ⟨25433862735242389038910787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16955908490161592692607191 25433862735242389038910787)
      ·
        refine ⟨38150794102863583558366181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25433862735242389038910787 38150794102863583558366181)
        ·
          refine ⟨7153273894286921917193659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38150794102863583558366181 7153273894286921917193659)
          ·
            refine ⟨10729910841430382875790489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7153273894286921917193659 10729910841430382875790489)
            ·
              refine ⟨8047433131072787156842867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10729910841430382875790489 8047433131072787156842867)
              ·
                refine ⟨12071149696609180735264301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8047433131072787156842867 12071149696609180735264301)
                ·
                  refine ⟨4526681136228442775724113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12071149696609180735264301 4526681136228442775724113)
                  ·
                    refine ⟨3395010852171332081793085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4526681136228442775724113 3395010852171332081793085)
                    ·
                      refine ⟨1273129069564249530672407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3395010852171332081793085 1273129069564249530672407)
                      ·
                        rfl

theorem cell23_2479410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_2479410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479410 prefixEnd_2479410 := by exact prefixLift 2479410
  have htrace : WordTrace (prefixWord ++ tailWord_2479410) baseStart_2479410 baseEnd_2479410 := by
    simpa [prefixWord, tailWord_2479410, baseEnd_2479410] using wordTrace_append hprefix tailTrace_2479410
  have hstable : (prefixWord ++ tailWord_2479410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479410).length < 2 ^ (prefixWord ++ tailWord_2479410).sum := by decide
  have hdescent : baseEnd_2479410 < baseStart_2479410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479421 : List Nat := [1, 4, 1, 5, 2, 1, 2, 1, 1, 5]
def baseStart_2479421 : Nat := 118140960795 + 2479421 * 2 ^ 59
def prefixEnd_2479421 : Nat := 4983230072969 + 3 ^ 40 * 2479421 * 2
def baseEnd_2479421 : Nat := 424378239283816329211619

theorem tailTrace_2479421 : CollatzResearch.WordTrace tailWord_2479421 prefixEnd_2479421 424378239283816329211619 := by
  unfold tailWord_2479421
  simp only [CollatzResearch.WordTrace]
  refine ⟨90431913150488643239222117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60287942100325762159481411 90431913150488643239222117)
  ·
    refine ⟨16955983715716620607354147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90431913150488643239222117 16955983715716620607354147)
    ·
      refine ⟨25433975573574930911031221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16955983715716620607354147 25433975573574930911031221)
      ·
        refine ⟨2384435210022649772909177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25433975573574930911031221 2384435210022649772909177)
        ·
          refine ⟨1788326407516987329681883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2384435210022649772909177 1788326407516987329681883)
          ·
            refine ⟨2682489611275480994522825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1788326407516987329681883 2682489611275480994522825)
            ·
              refine ⟨2011867208456610745892119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2682489611275480994522825 2011867208456610745892119)
              ·
                refine ⟨3017800812684916118838179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2011867208456610745892119 3017800812684916118838179)
                ·
                  refine ⟨4526701219027374178257269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3017800812684916118838179 4526701219027374178257269)
                  ·
                    refine ⟨424378239283816329211619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4526701219027374178257269 424378239283816329211619)
                    ·
                      rfl

theorem cell23_2479421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_2479421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479421 prefixEnd_2479421 := by exact prefixLift 2479421
  have htrace : WordTrace (prefixWord ++ tailWord_2479421) baseStart_2479421 baseEnd_2479421 := by
    simpa [prefixWord, tailWord_2479421, baseEnd_2479421] using wordTrace_append hprefix tailTrace_2479421
  have hstable : (prefixWord ++ tailWord_2479421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479421).length < 2 ^ (prefixWord ++ tailWord_2479421).sum := by decide
  have hdescent : baseEnd_2479421 < baseStart_2479421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479424 : List Nat := [2, 1, 1, 2, 2, 1, 6, 3, 1, 2, 2]
def baseStart_2479424 : Nat := 118140960795 + 2479424 * 2 ^ 59
def prefixEnd_2479424 : Nat := 4983230072969 + 3 ^ 40 * 2479424 * 2
def baseEnd_2479424 : Nat := 1273136258293412475897343

theorem tailTrace_2479424 : CollatzResearch.WordTrace tailWord_2479424 prefixEnd_2479424 1273136258293412475897343 := by
  unfold tailWord_2479424
  simp only [CollatzResearch.WordTrace]
  refine ⟨45216011284738887375790663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60288015046318516501054217 45216011284738887375790663)
  ·
    refine ⟨67824016927108331063685995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45216011284738887375790663 67824016927108331063685995)
    ·
      refine ⟨101736025390662496595528993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67824016927108331063685995 101736025390662496595528993)
      ·
        refine ⟨76302019042996872446646745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101736025390662496595528993 76302019042996872446646745)
        ·
          refine ⟨57226514282247654334985059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76302019042996872446646745 57226514282247654334985059)
          ·
            refine ⟨85839771423371481502477589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57226514282247654334985059 85839771423371481502477589)
            ·
              refine ⟨4023739285470538195428637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85839771423371481502477589 4023739285470538195428637)
              ·
                refine ⟨1508902232051451823285739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4023739285470538195428637 1508902232051451823285739)
                ·
                  refine ⟨2263353348077177734928609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1508902232051451823285739 2263353348077177734928609)
                  ·
                    refine ⟨1697515011057883301196457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2263353348077177734928609 1697515011057883301196457)
                    ·
                      refine ⟨1273136258293412475897343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1697515011057883301196457 1273136258293412475897343)
                      ·
                        rfl

theorem cell23_2479424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3, 1, 2, 2].length) (baseStart_2479424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479424 prefixEnd_2479424 := by exact prefixLift 2479424
  have htrace : WordTrace (prefixWord ++ tailWord_2479424) baseStart_2479424 baseEnd_2479424 := by
    simpa [prefixWord, tailWord_2479424, baseEnd_2479424] using wordTrace_append hprefix tailTrace_2479424
  have hstable : (prefixWord ++ tailWord_2479424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479424).length < 2 ^ (prefixWord ++ tailWord_2479424).sum := by decide
  have hdescent : baseEnd_2479424 < baseStart_2479424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479440 : List Nat := [2, 1, 1, 1, 1, 5, 3, 1, 4, 1, 3]
def baseStart_2479440 : Nat := 118140960795 + 2479440 * 2 ^ 59
def prefixEnd_2479440 : Nat := 4983230072969 + 3 ^ 40 * 2479440 * 2
def baseEnd_2479440 : Nat := 1273144473983884413297269

theorem tailTrace_2479440 : CollatzResearch.WordTrace tailWord_2479440 prefixEnd_2479440 1273144473983884413297269 := by
  unfold tailWord_2479440
  simp only [CollatzResearch.WordTrace]
  refine ⟨45216303068709904742081887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60288404091613206322775849 45216303068709904742081887)
  ·
    refine ⟨67824454603064857113122831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45216303068709904742081887 67824454603064857113122831)
    ·
      refine ⟨101736681904597285669684247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67824454603064857113122831 101736681904597285669684247)
      ·
        refine ⟨152605022856895928504526371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101736681904597285669684247 152605022856895928504526371)
        ·
          refine ⟨228907534285343892756789557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152605022856895928504526371 228907534285343892756789557)
          ·
            refine ⟨21460081339250989945949021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 228907534285343892756789557 21460081339250989945949021)
            ·
              refine ⟨8047530502219121229730883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21460081339250989945949021 8047530502219121229730883)
              ·
                refine ⟨12071295753328681844596325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8047530502219121229730883 12071295753328681844596325)
                ·
                  refine ⟨2263367953749127845861811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12071295753328681844596325 2263367953749127845861811)
                  ·
                    refine ⟨3395051930623691768792717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2263367953749127845861811 3395051930623691768792717)
                    ·
                      refine ⟨1273144473983884413297269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3395051930623691768792717 1273144473983884413297269)
                      ·
                        rfl

theorem cell23_2479440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 4, 1, 3].length) (baseStart_2479440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479440 prefixEnd_2479440 := by exact prefixLift 2479440
  have htrace : WordTrace (prefixWord ++ tailWord_2479440) baseStart_2479440 baseEnd_2479440 := by
    simpa [prefixWord, tailWord_2479440, baseEnd_2479440] using wordTrace_append hprefix tailTrace_2479440
  have hstable : (prefixWord ++ tailWord_2479440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479440).length < 2 ^ (prefixWord ++ tailWord_2479440).sum := by decide
  have hdescent : baseEnd_2479440 < baseStart_2479440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479450 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2]
def baseStart_2479450 : Nat := 118140960795 + 2479450 * 2 ^ 59
def prefixEnd_2479450 : Nat := 4983230072969 + 3 ^ 40 * 2479450 * 2
def baseEnd_2479450 : Nat := 1273149608790429374172223

theorem tailTrace_2479450 : CollatzResearch.WordTrace tailWord_2479450 prefixEnd_2479450 1273149608790429374172223 := by
  unfold tailWord_2479450
  simp only [CollatzResearch.WordTrace]
  refine ⟨22608242716845895298006951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60288647244922387461351869 22608242716845895298006951)
  ·
    refine ⟨33912364075268842947010427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22608242716845895298006951 33912364075268842947010427)
    ·
      refine ⟨50868546112903264420515641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33912364075268842947010427 50868546112903264420515641)
      ·
        refine ⟨38151409584677448315386731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50868546112903264420515641 38151409584677448315386731)
        ·
          refine ⟨57227114377016172473080097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38151409584677448315386731 57227114377016172473080097)
          ·
            refine ⟨42920335782762129354810073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57227114377016172473080097 42920335782762129354810073)
            ·
              refine ⟨32190251837071597016107555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42920335782762129354810073 32190251837071597016107555)
              ·
                refine ⟨48285377755607395524161333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32190251837071597016107555 48285377755607395524161333)
                ·
                  refine ⟨4526754164588193330390125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48285377755607395524161333 4526754164588193330390125)
                  ·
                    refine ⟨1697532811720572498896297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4526754164588193330390125 1697532811720572498896297)
                    ·
                      refine ⟨1273149608790429374172223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1697532811720572498896297 1273149608790429374172223)
                      ·
                        rfl

theorem cell23_2479450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2].length) (baseStart_2479450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479450 prefixEnd_2479450 := by exact prefixLift 2479450
  have htrace : WordTrace (prefixWord ++ tailWord_2479450) baseStart_2479450 baseEnd_2479450 := by
    simpa [prefixWord, tailWord_2479450, baseEnd_2479450] using wordTrace_append hprefix tailTrace_2479450
  have hstable : (prefixWord ++ tailWord_2479450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479450).length < 2 ^ (prefixWord ++ tailWord_2479450).sum := by decide
  have hdescent : baseEnd_2479450 < baseStart_2479450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479483 : List Nat := [1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 5]
def baseStart_2479483 : Nat := 118140960795 + 2479483 * 2 ^ 59
def prefixEnd_2479483 : Nat := 4983230072969 + 3 ^ 40 * 2479483 * 2
def baseEnd_2479483 : Nat := 1273166553652027745059571

theorem tailTrace_2479483 : CollatzResearch.WordTrace tailWord_2479483 prefixEnd_2479483 1273166553652027745059571 := by
  unfold tailWord_2479483
  simp only [CollatzResearch.WordTrace]
  refine ⟨90434174476264027827979103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60289449650842685218652735 90434174476264027827979103)
  ·
    refine ⟨135651261714396041741968655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90434174476264027827979103 135651261714396041741968655)
    ·
      refine ⟨203476892571594062612952983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135651261714396041741968655 203476892571594062612952983)
      ·
        refine ⟨305215338857391093919429475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203476892571594062612952983 305215338857391093919429475)
        ·
          refine ⟨457823008286086640879144213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305215338857391093919429475 457823008286086640879144213)
          ·
            refine ⟨21460453513410311291209885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 457823008286086640879144213 21460453513410311291209885)
            ·
              refine ⟨8047670067528866734203707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21460453513410311291209885 8047670067528866734203707)
              ·
                refine ⟨12071505101293300101305561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8047670067528866734203707 12071505101293300101305561)
                ·
                  refine ⟨9053628825969975075979171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12071505101293300101305561 9053628825969975075979171)
                  ·
                    refine ⟨13580443238954962613968757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9053628825969975075979171 13580443238954962613968757)
                    ·
                      refine ⟨1273166553652027745059571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13580443238954962613968757 1273166553652027745059571)
                      ·
                        rfl

theorem cell23_2479483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 5].length) (baseStart_2479483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479483 prefixEnd_2479483 := by exact prefixLift 2479483
  have htrace : WordTrace (prefixWord ++ tailWord_2479483) baseStart_2479483 baseEnd_2479483 := by
    simpa [prefixWord, tailWord_2479483, baseEnd_2479483] using wordTrace_append hprefix tailTrace_2479483
  have hstable : (prefixWord ++ tailWord_2479483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479483).length < 2 ^ (prefixWord ++ tailWord_2479483).sum := by decide
  have hdescent : baseEnd_2479483 < baseStart_2479483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479493 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 4, 2, 4]
def baseStart_2479493 : Nat := 118140960795 + 2479493 * 2 ^ 59
def prefixEnd_2479493 : Nat := 4983230072969 + 3 ^ 40 * 2479493 * 2
def baseEnd_2479493 : Nat := 1273171688458572705934525

theorem tailTrace_2479493 : CollatzResearch.WordTrace tailWord_2479493 prefixEnd_2479493 1273171688458572705934525 := by
  unfold tailWord_2479493
  simp only [CollatzResearch.WordTrace]
  refine ⟨90434539206227799535843133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60289692804151866357228755 90434539206227799535843133)
  ·
    refine ⟨33912952202335424825941175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90434539206227799535843133 33912952202335424825941175)
    ·
      refine ⟨50869428303503137238911763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33912952202335424825941175 50869428303503137238911763)
      ·
        refine ⟨76304142455254705858367645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50869428303503137238911763 76304142455254705858367645)
        ·
          refine ⟨28614053420720514696887867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76304142455254705858367645 28614053420720514696887867)
          ·
            refine ⟨42921080131080772045331801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28614053420720514696887867 42921080131080772045331801)
            ·
              refine ⟨32190810098310579033998851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42921080131080772045331801 32190810098310579033998851)
              ·
                refine ⟨48286215147465868550998277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32190810098310579033998851 48286215147465868550998277)
                ·
                  refine ⟨9053665340149850353312177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48286215147465868550998277 9053665340149850353312177)
                  ·
                    refine ⟨6790249005112387764984133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9053665340149850353312177 6790249005112387764984133)
                    ·
                      refine ⟨1273171688458572705934525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6790249005112387764984133 1273171688458572705934525)
                      ·
                        rfl

theorem cell23_2479493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_2479493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479493 prefixEnd_2479493 := by exact prefixLift 2479493
  have htrace : WordTrace (prefixWord ++ tailWord_2479493) baseStart_2479493 baseEnd_2479493 := by
    simpa [prefixWord, tailWord_2479493, baseEnd_2479493] using wordTrace_append hprefix tailTrace_2479493
  have hstable : (prefixWord ++ tailWord_2479493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479493).length < 2 ^ (prefixWord ++ tailWord_2479493).sum := by decide
  have hdescent : baseEnd_2479493 < baseStart_2479493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479514 : List Nat := [3, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2]
def baseStart_2479514 : Nat := 118140960795 + 2479514 * 2 ^ 59
def prefixEnd_2479514 : Nat := 4983230072969 + 3 ^ 40 * 2479514 * 2
def baseEnd_2479514 : Nat := 1273182471552317123771929

theorem tailTrace_2479514 : CollatzResearch.WordTrace tailWord_2479514 prefixEnd_2479514 1273182471552317123771929 := by
  unfold tailWord_2479514
  simp only [CollatzResearch.WordTrace]
  refine ⟨22608826284787930030589399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60290203426101146748238397 22608826284787930030589399)
  ·
    refine ⟨33913239427181895045884099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22608826284787930030589399 33913239427181895045884099)
    ·
      refine ⟨50869859140772842568826149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33913239427181895045884099 50869859140772842568826149)
      ·
        refine ⟨9538098588894907981654903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50869859140772842568826149 9538098588894907981654903)
        ·
          refine ⟨14307147883342361972482355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9538098588894907981654903 14307147883342361972482355)
          ·
            refine ⟨21460721825013542958723533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14307147883342361972482355 21460721825013542958723533)
            ·
              refine ⟨8047770684380078609521325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21460721825013542958723533 8047770684380078609521325)
              ·
                refine ⟨3017914006642529478570497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8047770684380078609521325 3017914006642529478570497)
                ·
                  refine ⟨2263435504981897108927873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3017914006642529478570497 2263435504981897108927873)
                  ·
                    refine ⟨1697576628736422831695905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2263435504981897108927873 1697576628736422831695905)
                    ·
                      refine ⟨1273182471552317123771929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1697576628736422831695905 1273182471552317123771929)
                      ·
                        rfl

theorem cell23_2479514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_2479514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479514 prefixEnd_2479514 := by exact prefixLift 2479514
  have htrace : WordTrace (prefixWord ++ tailWord_2479514) baseStart_2479514 baseEnd_2479514 := by
    simpa [prefixWord, tailWord_2479514, baseEnd_2479514] using wordTrace_append hprefix tailTrace_2479514
  have hstable : (prefixWord ++ tailWord_2479514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479514).length < 2 ^ (prefixWord ++ tailWord_2479514).sum := by decide
  have hdescent : baseEnd_2479514 < baseStart_2479514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479518 : List Nat := [4, 3, 1, 2, 2, 2, 1, 2, 1, 3, 2]
def baseStart_2479518 : Nat := 118140960795 + 2479518 * 2 ^ 59
def prefixEnd_2479518 : Nat := 4983230072969 + 3 ^ 40 * 2479518 * 2
def baseEnd_2479518 : Nat := 1273184525474935108121911

theorem tailTrace_2479518 : CollatzResearch.WordTrace tailWord_2479518 prefixEnd_2479518 1273184525474935108121911 := by
  unfold tailWord_2479518
  simp only [CollatzResearch.WordTrace]
  refine ⟨11304431378892153600687901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60290300687424819203668805 11304431378892153600687901)
  ·
    refine ⟨4239161767084557600257963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11304431378892153600687901 4239161767084557600257963)
    ·
      refine ⟨6358742650626836400386945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4239161767084557600257963 6358742650626836400386945)
      ·
        refine ⟨4769056987970127300290209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6358742650626836400386945 4769056987970127300290209)
        ·
          refine ⟨3576792740977595475217657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4769056987970127300290209 3576792740977595475217657)
          ·
            refine ⟨2682594555733196606413243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3576792740977595475217657 2682594555733196606413243)
            ·
              refine ⟨4023891833599794909619865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2682594555733196606413243 4023891833599794909619865)
              ·
                refine ⟨3017918875199846182214899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4023891833599794909619865 3017918875199846182214899)
                ·
                  refine ⟨4526878312799769273322349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3017918875199846182214899 4526878312799769273322349)
                  ·
                    refine ⟨1697579367299913477495881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4526878312799769273322349 1697579367299913477495881)
                    ·
                      refine ⟨1273184525474935108121911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1697579367299913477495881 1273184525474935108121911)
                      ·
                        rfl

theorem cell23_2479518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_2479518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479518 prefixEnd_2479518 := by exact prefixLift 2479518
  have htrace : WordTrace (prefixWord ++ tailWord_2479518) baseStart_2479518 baseEnd_2479518 := by
    simpa [prefixWord, tailWord_2479518, baseEnd_2479518] using wordTrace_append hprefix tailTrace_2479518
  have hstable : (prefixWord ++ tailWord_2479518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479518).length < 2 ^ (prefixWord ++ tailWord_2479518).sum := by decide
  have hdescent : baseEnd_2479518 < baseStart_2479518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479543 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 5]
def baseStart_2479543 : Nat := 118140960795 + 2479543 * 2 ^ 59
def prefixEnd_2479543 : Nat := 4983230072969 + 3 ^ 40 * 2479543 * 2
def baseEnd_2479543 : Nat := 1273197362491297510309295

theorem tailTrace_2479543 : CollatzResearch.WordTrace tailWord_2479543 prefixEnd_2479543 1273197362491297510309295 := by
  unfold tailWord_2479543
  simp only [CollatzResearch.WordTrace]
  refine ⟨90436362856046658075163283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60290908570697772050108855 90436362856046658075163283)
  ·
    refine ⟨135654544284069987112744925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90436362856046658075163283 135654544284069987112744925)
    ·
      refine ⟨50870454106526245167279347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135654544284069987112744925 50870454106526245167279347)
      ·
        refine ⟨76305681159789367750919021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50870454106526245167279347 76305681159789367750919021)
        ·
          refine ⟨28614630434921012906594633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76305681159789367750919021 28614630434921012906594633)
          ·
            refine ⟨21460972826190759679945975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28614630434921012906594633 21460972826190759679945975)
            ·
              refine ⟨32191459239286139519918963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21460972826190759679945975 32191459239286139519918963)
              ·
                refine ⟨48287188858929209279878445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32191459239286139519918963 48287188858929209279878445)
                ·
                  refine ⟨18107695822098453479954417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48287188858929209279878445 18107695822098453479954417)
                  ·
                    refine ⟨13580771866573840109965813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18107695822098453479954417 13580771866573840109965813)
                    ·
                      refine ⟨1273197362491297510309295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13580771866573840109965813 1273197362491297510309295)
                      ·
                        rfl

theorem cell23_2479543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_2479543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479543 prefixEnd_2479543 := by exact prefixLift 2479543
  have htrace : WordTrace (prefixWord ++ tailWord_2479543) baseStart_2479543 baseEnd_2479543 := by
    simpa [prefixWord, tailWord_2479543, baseEnd_2479543] using wordTrace_append hprefix tailTrace_2479543
  have hstable : (prefixWord ++ tailWord_2479543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479543).length < 2 ^ (prefixWord ++ tailWord_2479543).sum := by decide
  have hdescent : baseEnd_2479543 < baseStart_2479543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479587 : List Nat := [1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 4]
def baseStart_2479587 : Nat := 118140960795 + 2479587 * 2 ^ 59
def prefixEnd_2479587 : Nat := 4983230072969 + 3 ^ 40 * 2479587 * 2
def baseEnd_2479587 : Nat := 1273219955640095338159093

theorem tailTrace_2479587 : CollatzResearch.WordTrace tailWord_2479587 prefixEnd_2479587 1273219955640095338159093 := by
  unfold tailWord_2479587
  simp only [CollatzResearch.WordTrace]
  refine ⟨90437967667887253589765015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60291978445258169059843343 90437967667887253589765015)
  ·
    refine ⟨135656951501830880384647523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90437967667887253589765015 135656951501830880384647523)
    ·
      refine ⟨203485427252746320576971285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135656951501830880384647523 203485427252746320576971285)
      ·
        refine ⟨9538379402472483777045529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 203485427252746320576971285 9538379402472483777045529)
        ·
          refine ⟨7153784551854362832784147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9538379402472483777045529 7153784551854362832784147)
          ·
            refine ⟨10730676827781544249176221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7153784551854362832784147 10730676827781544249176221)
            ·
              refine ⟨4024003810418079093441083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10730676827781544249176221 4024003810418079093441083)
              ·
                refine ⟨6036005715627118640161625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4024003810418079093441083 6036005715627118640161625)
                ·
                  refine ⟨4527004286720338980121219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6036005715627118640161625 4527004286720338980121219)
                  ·
                    refine ⟨6790506430080508470181829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4527004286720338980121219 6790506430080508470181829)
                    ·
                      refine ⟨1273219955640095338159093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6790506430080508470181829 1273219955640095338159093)
                      ·
                        rfl

theorem cell23_2479587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_2479587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479587 prefixEnd_2479587 := by exact prefixLift 2479587
  have htrace : WordTrace (prefixWord ++ tailWord_2479587) baseStart_2479587 baseEnd_2479587 := by
    simpa [prefixWord, tailWord_2479587, baseEnd_2479587] using wordTrace_append hprefix tailTrace_2479587
  have hstable : (prefixWord ++ tailWord_2479587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479587).length < 2 ^ (prefixWord ++ tailWord_2479587).sum := by decide
  have hdescent : baseEnd_2479587 < baseStart_2479587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479647 : List Nat := [1, 1, 2, 4, 1, 1, 4, 1, 1, 5, 2]
def baseStart_2479647 : Nat := 118140960795 + 2479647 * 2 ^ 59
def prefixEnd_2479647 : Nat := 4983230072969 + 3 ^ 40 * 2479647 * 2
def baseEnd_2479647 : Nat := 1273250764479365103408817

theorem tailTrace_2479647 : CollatzResearch.WordTrace tailWord_2479647 prefixEnd_2479647 1273250764479365103408817 := by
  unfold tailWord_2479647
  simp only [CollatzResearch.WordTrace]
  refine ⟨90440156047669883836949195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60293437365113255891299463 90440156047669883836949195)
  ·
    refine ⟨135660234071504825755423793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90440156047669883836949195 135660234071504825755423793)
    ·
      refine ⟨101745175553628619316567845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135660234071504825755423793 101745175553628619316567845)
      ·
        refine ⟨19077220416305366121856471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101745175553628619316567845 19077220416305366121856471)
        ·
          refine ⟨28615830624458049182784707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19077220416305366121856471 28615830624458049182784707)
          ·
            refine ⟨42923745936687073774177061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28615830624458049182784707 42923745936687073774177061)
            ·
              refine ⟨8048202363128826332658199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42923745936687073774177061 8048202363128826332658199)
              ·
                refine ⟨12072303544693239498987299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8048202363128826332658199 12072303544693239498987299)
                ·
                  refine ⟨18108455317039859248480949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12072303544693239498987299 18108455317039859248480949)
                  ·
                    refine ⟨1697667685972486804545089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18108455317039859248480949 1697667685972486804545089)
                    ·
                      refine ⟨1273250764479365103408817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1697667685972486804545089 1273250764479365103408817)
                      ·
                        rfl

theorem cell23_2479647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_2479647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479647 prefixEnd_2479647 := by exact prefixLift 2479647
  have htrace : WordTrace (prefixWord ++ tailWord_2479647) baseStart_2479647 baseEnd_2479647 := by
    simpa [prefixWord, tailWord_2479647, baseEnd_2479647] using wordTrace_append hprefix tailTrace_2479647
  have hstable : (prefixWord ++ tailWord_2479647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479647).length < 2 ^ (prefixWord ++ tailWord_2479647).sum := by decide
  have hdescent : baseEnd_2479647 < baseStart_2479647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479660 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 4]
def baseStart_2479660 : Nat := 118140960795 + 2479660 * 2 ^ 59
def prefixEnd_2479660 : Nat := 4983230072969 + 3 ^ 40 * 2479660 * 2
def baseEnd_2479660 : Nat := 1273257439727873552546257

theorem tailTrace_2479660 : CollatzResearch.WordTrace tailWord_2479660 prefixEnd_2479660 1273257439727873552546257 := by
  unfold tailWord_2479660
  simp only [CollatzResearch.WordTrace]
  refine ⟨45220315098311393528586217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60293753464415191371448289 45220315098311393528586217)
  ·
    refine ⟨33915236323733545146439663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45220315098311393528586217 33915236323733545146439663)
    ·
      refine ⟨50872854485600317719659495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33915236323733545146439663 50872854485600317719659495)
      ·
        refine ⟨76309281728400476579489243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50872854485600317719659495 76309281728400476579489243)
        ·
          refine ⟨114463922592600714869233865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76309281728400476579489243 114463922592600714869233865)
          ·
            refine ⟨85847941944450536151925399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114463922592600714869233865 85847941944450536151925399)
            ·
              refine ⟨128771912916675804227888099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85847941944450536151925399 128771912916675804227888099)
              ·
                refine ⟨193157869375013706341832149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128771912916675804227888099 193157869375013706341832149)
                ·
                  refine ⟨4527137563476883742386691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 193157869375013706341832149 4527137563476883742386691)
                  ·
                    refine ⟨6790706345215325613580037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4527137563476883742386691 6790706345215325613580037)
                    ·
                      refine ⟨1273257439727873552546257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6790706345215325613580037 1273257439727873552546257)
                      ·
                        rfl

theorem cell23_2479660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_2479660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479660 prefixEnd_2479660 := by exact prefixLift 2479660
  have htrace : WordTrace (prefixWord ++ tailWord_2479660) baseStart_2479660 baseEnd_2479660 := by
    simpa [prefixWord, tailWord_2479660, baseEnd_2479660] using wordTrace_append hprefix tailTrace_2479660
  have hstable : (prefixWord ++ tailWord_2479660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479660).length < 2 ^ (prefixWord ++ tailWord_2479660).sum := by decide
  have hdescent : baseEnd_2479660 < baseStart_2479660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479680 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 3]
def baseStart_2479680 : Nat := 118140960795 + 2479680 * 2 ^ 59
def prefixEnd_2479680 : Nat := 4983230072969 + 3 ^ 40 * 2479680 * 2
def baseEnd_2479680 : Nat := 1273267709340963474296165

theorem tailTrace_2479680 : CollatzResearch.WordTrace tailWord_2479680 prefixEnd_2479680 1273267709340963474296165 := by
  unfold tailWord_2479680
  simp only [CollatzResearch.WordTrace]
  refine ⟨45220679828275165236450247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60294239771033553648600329 45220679828275165236450247)
  ·
    refine ⟨67831019742412747854675371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45220679828275165236450247 67831019742412747854675371)
    ·
      refine ⟨101746529613619121782013057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67831019742412747854675371 101746529613619121782013057)
      ·
        refine ⟨76309897210214341336509793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101746529613619121782013057 76309897210214341336509793)
        ·
          refine ⟨57232422907660756002382345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76309897210214341336509793 57232422907660756002382345)
          ·
            refine ⟨42924317180745567001786759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57232422907660756002382345 42924317180745567001786759)
            ·
              refine ⟨64386475771118350502680139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42924317180745567001786759 64386475771118350502680139)
              ·
                refine ⟨96579713656677525754020209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64386475771118350502680139 96579713656677525754020209)
                ·
                  refine ⟨72434785242508144315515157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96579713656677525754020209 72434785242508144315515157)
                  ·
                    refine ⟨3395380558242569264789773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 72434785242508144315515157 3395380558242569264789773)
                    ·
                      refine ⟨1273267709340963474296165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3395380558242569264789773 1273267709340963474296165)
                      ·
                        rfl

theorem cell23_2479680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 3].length) (baseStart_2479680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479680 prefixEnd_2479680 := by exact prefixLift 2479680
  have htrace : WordTrace (prefixWord ++ tailWord_2479680) baseStart_2479680 baseEnd_2479680 := by
    simpa [prefixWord, tailWord_2479680, baseEnd_2479680] using wordTrace_append hprefix tailTrace_2479680
  have hstable : (prefixWord ++ tailWord_2479680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479680).length < 2 ^ (prefixWord ++ tailWord_2479680).sum := by decide
  have hdescent : baseEnd_2479680 < baseStart_2479680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479690 : List Nat := [3, 1, 2, 1, 1, 3, 1, 3, 1, 1, 6]
def baseStart_2479690 : Nat := 118140960795 + 2479690 * 2 ^ 59
def prefixEnd_2479690 : Nat := 4983230072969 + 3 ^ 40 * 2479690 * 2
def baseEnd_2479690 : Nat := 1273272844147508435171119

theorem tailTrace_2479690 : CollatzResearch.WordTrace tailWord_2479690 prefixEnd_2479690 1273272844147508435171119 := by
  unfold tailWord_2479690
  simp only [CollatzResearch.WordTrace]
  refine ⟨22610431096628525545191131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60294482924342734787176349 22610431096628525545191131)
  ·
    refine ⟨33915646644942788317786697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22610431096628525545191131 33915646644942788317786697)
    ·
      refine ⟨25436734983707091238340023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33915646644942788317786697 25436734983707091238340023)
      ·
        refine ⟨38155102475560636857510035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25436734983707091238340023 38155102475560636857510035)
        ·
          refine ⟨57232653713340955286265053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38155102475560636857510035 57232653713340955286265053)
          ·
            refine ⟨21462245142502858232349395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57232653713340955286265053 21462245142502858232349395)
            ·
              refine ⟨32193367713754287348524093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21462245142502858232349395 32193367713754287348524093)
              ·
                refine ⟨12072512892657857755696535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32193367713754287348524093 12072512892657857755696535)
                ·
                  refine ⟨18108769338986786633544803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12072512892657857755696535 18108769338986786633544803)
                  ·
                    refine ⟨27163154008480179950317205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18108769338986786633544803 27163154008480179950317205)
                    ·
                      refine ⟨1273272844147508435171119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27163154008480179950317205 1273272844147508435171119)
                      ·
                        rfl

theorem cell23_2479690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_2479690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479690 prefixEnd_2479690 := by exact prefixLift 2479690
  have htrace : WordTrace (prefixWord ++ tailWord_2479690) baseStart_2479690 baseEnd_2479690 := by
    simpa [prefixWord, tailWord_2479690, baseEnd_2479690] using wordTrace_append hprefix tailTrace_2479690
  have hstable : (prefixWord ++ tailWord_2479690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479690).length < 2 ^ (prefixWord ++ tailWord_2479690).sum := by decide
  have hdescent : baseEnd_2479690 < baseStart_2479690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479694 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2]
def baseStart_2479694 : Nat := 118140960795 + 2479694 * 2 ^ 59
def prefixEnd_2479694 : Nat := 4983230072969 + 3 ^ 40 * 2479694 * 2
def baseEnd_2479694 : Nat := 1273274898070126419521101

theorem tailTrace_2479694 : CollatzResearch.WordTrace tailWord_2479694 prefixEnd_2479694 1273274898070126419521101 := by
  unfold tailWord_2479694
  simp only [CollatzResearch.WordTrace]
  refine ⟨11305233784812451357988767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60294580185666407242606757 11305233784812451357988767)
  ·
    refine ⟨16957850677218677036983151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11305233784812451357988767 16957850677218677036983151)
    ·
      refine ⟨25436776015828015555474727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16957850677218677036983151 25436776015828015555474727)
      ·
        refine ⟨38155164023742023333212091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25436776015828015555474727 38155164023742023333212091)
        ·
          refine ⟨57232746035613034999818137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38155164023742023333212091 57232746035613034999818137)
          ·
            refine ⟨42924559526709776249863603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57232746035613034999818137 42924559526709776249863603)
            ·
              refine ⟨64386839290064664374795405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42924559526709776249863603 64386839290064664374795405)
              ·
                refine ⟨24145064733774249140548277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64386839290064664374795405 24145064733774249140548277)
                ·
                  refine ⟨2263599818791335856926401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24145064733774249140548277 2263599818791335856926401)
                  ·
                    refine ⟨1697699864093501892694801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2263599818791335856926401 1697699864093501892694801)
                    ·
                      refine ⟨1273274898070126419521101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1697699864093501892694801 1273274898070126419521101)
                      ·
                        rfl

theorem cell23_2479694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2].length) (baseStart_2479694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479694 prefixEnd_2479694 := by exact prefixLift 2479694
  have htrace : WordTrace (prefixWord ++ tailWord_2479694) baseStart_2479694 baseEnd_2479694 := by
    simpa [prefixWord, tailWord_2479694, baseEnd_2479694] using wordTrace_append hprefix tailTrace_2479694
  have hstable : (prefixWord ++ tailWord_2479694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479694).length < 2 ^ (prefixWord ++ tailWord_2479694).sum := by decide
  have hdescent : baseEnd_2479694 < baseStart_2479694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479697 : List Nat := [1, 2, 2, 1, 3, 2, 3, 1, 3, 2, 3]
def baseStart_2479697 : Nat := 118140960795 + 2479697 * 2 ^ 59
def prefixEnd_2479697 : Nat := 4983230072969 + 3 ^ 40 * 2479697 * 2
def baseEnd_2479697 : Nat := 1273276438512089907783587

theorem tailTrace_2479697 : CollatzResearch.WordTrace tailWord_2479697 prefixEnd_2479697 1273276438512089907783587 := by
  unfold tailWord_2479697
  simp only [CollatzResearch.WordTrace]
  refine ⟨90441979697488742376269345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60294653131659161584179563 90441979697488742376269345)
  ·
    refine ⟨67831484773116556782202009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90441979697488742376269345 67831484773116556782202009)
    ·
      refine ⟨50873613579837417586651507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67831484773116556782202009 50873613579837417586651507)
      ·
        refine ⟨76310420369756126379977261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50873613579837417586651507 76310420369756126379977261)
        ·
          refine ⟨28616407638658547392491473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76310420369756126379977261 28616407638658547392491473)
          ·
            refine ⟨21462305728993910544368605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28616407638658547392491473 21462305728993910544368605)
            ·
              refine ⟨8048364648372716454138227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21462305728993910544368605 8048364648372716454138227)
              ·
                refine ⟨12072546972559074681207341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8048364648372716454138227 12072546972559074681207341)
                ·
                  refine ⟨4527205114709653005452753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12072546972559074681207341 4527205114709653005452753)
                  ·
                    refine ⟨3395403836032239754089565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4527205114709653005452753 3395403836032239754089565)
                    ·
                      refine ⟨1273276438512089907783587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3395403836032239754089565 1273276438512089907783587)
                      ·
                        rfl

theorem cell23_2479697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 2, 3].length) (baseStart_2479697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479697 prefixEnd_2479697 := by exact prefixLift 2479697
  have htrace : WordTrace (prefixWord ++ tailWord_2479697) baseStart_2479697 baseEnd_2479697 := by
    simpa [prefixWord, tailWord_2479697, baseEnd_2479697] using wordTrace_append hprefix tailTrace_2479697
  have hstable : (prefixWord ++ tailWord_2479697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479697).length < 2 ^ (prefixWord ++ tailWord_2479697).sum := by decide
  have hdescent : baseEnd_2479697 < baseStart_2479697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479700 : List Nat := [2, 4, 1, 1, 1, 2, 1, 11]
def baseStart_2479700 : Nat := 118140960795 + 2479700 * 2 ^ 59
def prefixEnd_2479700 : Nat := 4983230072969 + 3 ^ 40 * 2479700 * 2
def baseEnd_2479700 : Nat := 47158443664964940594299

theorem tailTrace_2479700 : CollatzResearch.WordTrace tailWord_2479700 prefixEnd_2479700 47158443664964940594299 := by
  unfold tailWord_2479700
  simp only [CollatzResearch.WordTrace]
  refine ⟨45221044558238936944314277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60294726077651915925752369 45221044558238936944314277)
  ·
    refine ⟨8478945854669800677058927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45221044558238936944314277 8478945854669800677058927)
    ·
      refine ⟨12718418782004701015588391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8478945854669800677058927 12718418782004701015588391)
      ·
        refine ⟨19077628173007051523382587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12718418782004701015588391 19077628173007051523382587)
        ·
          refine ⟨28616442259510577285073881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19077628173007051523382587 28616442259510577285073881)
          ·
            refine ⟨21462331694632932963805411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28616442259510577285073881 21462331694632932963805411)
            ·
              refine ⟨32193497541949399445708117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21462331694632932963805411 32193497541949399445708117)
              ·
                refine ⟨47158443664964940594299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 32193497541949399445708117 47158443664964940594299)
                ·
                  rfl

theorem cell23_2479700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 11].length) (baseStart_2479700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479700 prefixEnd_2479700 := by exact prefixLift 2479700
  have htrace : WordTrace (prefixWord ++ tailWord_2479700) baseStart_2479700 baseEnd_2479700 := by
    simpa [prefixWord, tailWord_2479700, baseEnd_2479700] using wordTrace_append hprefix tailTrace_2479700
  have hstable : (prefixWord ++ tailWord_2479700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479700).length < 2 ^ (prefixWord ++ tailWord_2479700).sum := by decide
  have hdescent : baseEnd_2479700 < baseStart_2479700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479728 : List Nat := [2, 1, 1, 1, 6, 2, 1, 4, 1, 2, 2]
def baseStart_2479728 : Nat := 118140960795 + 2479728 * 2 ^ 59
def prefixEnd_2479728 : Nat := 4983230072969 + 3 ^ 40 * 2479728 * 2
def baseEnd_2479728 : Nat := 1273292356412379286495945

theorem tailTrace_2479728 : CollatzResearch.WordTrace tailWord_2479728 prefixEnd_2479728 1273292356412379286495945 := by
  unfold tailWord_2479728
  simp only [CollatzResearch.WordTrace]
  refine ⟨45221555180188217335323919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60295406906917623113765225 45221555180188217335323919)
  ·
    refine ⟨67832332770282326002985879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45221555180188217335323919 67832332770282326002985879)
    ·
      refine ⟨101748499155423489004478819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67832332770282326002985879 101748499155423489004478819)
      ·
        refine ⟨152622748733135233506718229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101748499155423489004478819 152622748733135233506718229)
        ·
          refine ⟨7154191346865714070627417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 152622748733135233506718229 7154191346865714070627417)
          ·
            refine ⟨5365643510149285552970563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7154191346865714070627417 5365643510149285552970563)
            ·
              refine ⟨8048465265223928329455845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5365643510149285552970563 8048465265223928329455845)
              ·
                refine ⟨1509087237229486561772971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8048465265223928329455845 1509087237229486561772971)
                ·
                  refine ⟨2263630855844229842659457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1509087237229486561772971 2263630855844229842659457)
                  ·
                    refine ⟨1697723141883172381994593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2263630855844229842659457 1697723141883172381994593)
                    ·
                      refine ⟨1273292356412379286495945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1697723141883172381994593 1273292356412379286495945)
                      ·
                        rfl

theorem cell23_2479728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4, 1, 2, 2].length) (baseStart_2479728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479728 prefixEnd_2479728 := by exact prefixLift 2479728
  have htrace : WordTrace (prefixWord ++ tailWord_2479728) baseStart_2479728 baseEnd_2479728 := by
    simpa [prefixWord, tailWord_2479728, baseEnd_2479728] using wordTrace_append hprefix tailTrace_2479728
  have hstable : (prefixWord ++ tailWord_2479728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479728).length < 2 ^ (prefixWord ++ tailWord_2479728).sum := by decide
  have hdescent : baseEnd_2479728 < baseStart_2479728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479734 : List Nat := [5, 1, 1, 2, 2, 3, 1, 8]
def baseStart_2479734 : Nat := 118140960795 + 2479734 * 2 ^ 59
def prefixEnd_2479734 : Nat := 4983230072969 + 3 ^ 40 * 2479734 * 2
def baseEnd_2479734 : Nat := 47159090270233565297071

theorem tailTrace_2479734 : CollatzResearch.WordTrace tailWord_2479734 prefixEnd_2479734 47159090270233565297071 := by
  unfold tailWord_2479734
  simp only [CollatzResearch.WordTrace]
  refine ⟨5652708074897168605960391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60295552798903131796910837 5652708074897168605960391)
  ·
    refine ⟨8479062112345752908940587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5652708074897168605960391 8479062112345752908940587)
    ·
      refine ⟨12718593168518629363410881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8479062112345752908940587 12718593168518629363410881)
      ·
        refine ⟨9538944876388972022558161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12718593168518629363410881 9538944876388972022558161)
        ·
          refine ⟨7154208657291729016918621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9538944876388972022558161 7154208657291729016918621)
          ·
            refine ⟨2682828246484398381344483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7154208657291729016918621 2682828246484398381344483)
            ·
              refine ⟨4024242369726597572016725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2682828246484398381344483 4024242369726597572016725)
              ·
                refine ⟨47159090270233565297071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4024242369726597572016725 47159090270233565297071)
                ·
                  rfl

theorem cell23_2479734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_2479734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479734 prefixEnd_2479734 := by exact prefixLift 2479734
  have htrace : WordTrace (prefixWord ++ tailWord_2479734) baseStart_2479734 baseEnd_2479734 := by
    simpa [prefixWord, tailWord_2479734, baseEnd_2479734] using wordTrace_append hprefix tailTrace_2479734
  have hstable : (prefixWord ++ tailWord_2479734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479734).length < 2 ^ (prefixWord ++ tailWord_2479734).sum := by decide
  have hdescent : baseEnd_2479734 < baseStart_2479734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479740 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 1, 4, 5]
def baseStart_2479740 : Nat := 118140960795 + 2479740 * 2 ^ 59
def prefixEnd_2479740 : Nat := 4983230072969 + 3 ^ 40 * 2479740 * 2
def baseEnd_2479740 : Nat := 1273298518180233239545889

theorem tailTrace_2479740 : CollatzResearch.WordTrace tailWord_2479740 prefixEnd_2479740 1273298518180233239545889 := by
  unfold tailWord_2479740
  simp only [CollatzResearch.WordTrace]
  refine ⟨45221774018166480360042337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60295698690888640480056449 45221774018166480360042337)
  ·
    refine ⟨33916330513624860270031753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45221774018166480360042337 33916330513624860270031753)
    ·
      refine ⟨25437247885218645202523815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33916330513624860270031753 25437247885218645202523815)
      ·
        refine ⟨38155871827827967803785723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25437247885218645202523815 38155871827827967803785723)
        ·
          refine ⟨57233807741741951705678585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38155871827827967803785723 57233807741741951705678585)
          ·
            refine ⟨42925355806306463779258939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57233807741741951705678585 42925355806306463779258939)
            ·
              refine ⟨64388033709459695668888409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42925355806306463779258939 64388033709459695668888409)
              ·
                refine ⟨48291025282094771751666307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64388033709459695668888409 48291025282094771751666307)
                ·
                  refine ⟨72436537923142157627499461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48291025282094771751666307 72436537923142157627499461)
                  ·
                    refine ⟨13581850860589154555156149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72436537923142157627499461 13581850860589154555156149)
                    ·
                      refine ⟨1273298518180233239545889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13581850860589154555156149 1273298518180233239545889)
                      ·
                        rfl

theorem cell23_2479740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_2479740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479740 prefixEnd_2479740 := by exact prefixLift 2479740
  have htrace : WordTrace (prefixWord ++ tailWord_2479740) baseStart_2479740 baseEnd_2479740 := by
    simpa [prefixWord, tailWord_2479740, baseEnd_2479740] using wordTrace_append hprefix tailTrace_2479740
  have hstable : (prefixWord ++ tailWord_2479740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479740).length < 2 ^ (prefixWord ++ tailWord_2479740).sum := by decide
  have hdescent : baseEnd_2479740 < baseStart_2479740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479744 : List Nat := [2, 1, 1, 2, 1, 4, 1, 5, 2, 1, 3]
def baseStart_2479744 : Nat := 118140960795 + 2479744 * 2 ^ 59
def prefixEnd_2479744 : Nat := 4983230072969 + 3 ^ 40 * 2479744 * 2
def baseEnd_2479744 : Nat := 1273300572102851223895871

theorem tailTrace_2479744 : CollatzResearch.WordTrace tailWord_2479744 prefixEnd_2479744 1273300572102851223895871 := by
  unfold tailWord_2479744
  simp only [CollatzResearch.WordTrace]
  refine ⟨45221846964159234701615143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60295795952212312935486857 45221846964159234701615143)
  ·
    refine ⟨67832770446238852052422715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45221846964159234701615143 67832770446238852052422715)
    ·
      refine ⟨101749155669358278078634073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67832770446238852052422715 101749155669358278078634073)
      ·
        refine ⟨76311866752018708558975555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101749155669358278078634073 76311866752018708558975555)
        ·
          refine ⟨114467800128028062838463333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76311866752018708558975555 114467800128028062838463333)
          ·
            refine ⟨21462712524005261782211875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114467800128028062838463333 21462712524005261782211875)
            ·
              refine ⟨32194068786007892673317813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21462712524005261782211875 32194068786007892673317813)
              ·
                refine ⟨3018193948688239938123545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32194068786007892673317813 3018193948688239938123545)
                ·
                  refine ⟨2263645461516179953592659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3018193948688239938123545 2263645461516179953592659)
                  ·
                    refine ⟨3395468192274269930388989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2263645461516179953592659 3395468192274269930388989)
                    ·
                      refine ⟨1273300572102851223895871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3395468192274269930388989 1273300572102851223895871)
                      ·
                        rfl

theorem cell23_2479744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 2, 1, 3].length) (baseStart_2479744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479744 prefixEnd_2479744 := by exact prefixLift 2479744
  have htrace : WordTrace (prefixWord ++ tailWord_2479744) baseStart_2479744 baseEnd_2479744 := by
    simpa [prefixWord, tailWord_2479744, baseEnd_2479744] using wordTrace_append hprefix tailTrace_2479744
  have hstable : (prefixWord ++ tailWord_2479744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479744).length < 2 ^ (prefixWord ++ tailWord_2479744).sum := by decide
  have hdescent : baseEnd_2479744 < baseStart_2479744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479777 : List Nat := [1, 2, 3, 3, 2, 1, 1, 2, 2, 6]
def baseStart_2479777 : Nat := 118140960795 + 2479777 * 2 ^ 59
def prefixEnd_2479777 : Nat := 4983230072969 + 3 ^ 40 * 2479777 * 2
def baseEnd_2479777 : Nat := 424439172321483198261073

theorem tailTrace_2479777 : CollatzResearch.WordTrace tailWord_2479777 prefixEnd_2479777 424439172321483198261073 := by
  unfold tailWord_2479777
  simp only [CollatzResearch.WordTrace]
  refine ⟨90444897537198916039181585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60296598358132610692787723 90444897537198916039181585)
  ·
    refine ⟨67833673152899187029386189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90444897537198916039181585 67833673152899187029386189)
    ·
      refine ⟨25437627432337195136019821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67833673152899187029386189 25437627432337195136019821)
      ·
        refine ⟨9539110287126448176007433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25437627432337195136019821 9539110287126448176007433)
        ·
          refine ⟨7154332715344836132005575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9539110287126448176007433 7154332715344836132005575)
          ·
            refine ⟨10731499073017254198008363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7154332715344836132005575 10731499073017254198008363)
            ·
              refine ⟨16097248609525881297012545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10731499073017254198008363 16097248609525881297012545)
              ·
                refine ⟨12072936457144410972759409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16097248609525881297012545 12072936457144410972759409)
                ·
                  refine ⟨9054702342858308229569557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12072936457144410972759409 9054702342858308229569557)
                  ·
                    refine ⟨424439172321483198261073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9054702342858308229569557 424439172321483198261073)
                    ·
                      rfl

theorem cell23_2479777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_2479777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479777 prefixEnd_2479777 := by exact prefixLift 2479777
  have htrace : WordTrace (prefixWord ++ tailWord_2479777) baseStart_2479777 baseEnd_2479777 := by
    simpa [prefixWord, tailWord_2479777, baseEnd_2479777] using wordTrace_append hprefix tailTrace_2479777
  have hstable : (prefixWord ++ tailWord_2479777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479777).length < 2 ^ (prefixWord ++ tailWord_2479777).sum := by decide
  have hdescent : baseEnd_2479777 < baseStart_2479777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479778 : List Nat := [3, 3, 1, 4, 1, 1, 1, 1, 4, 1, 3]
def baseStart_2479778 : Nat := 118140960795 + 2479778 * 2 ^ 59
def prefixEnd_2479778 : Nat := 4983230072969 + 3 ^ 40 * 2479778 * 2
def baseEnd_2479778 : Nat := 1273318030445104090870715

theorem tailTrace_2479778 : CollatzResearch.WordTrace tailWord_2479778 prefixEnd_2479778 1273318030445104090870715 := by
  unfold tailWord_2479778
  simp only [CollatzResearch.WordTrace]
  refine ⟨22611233502548823302491997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60296622673463528806645325 22611233502548823302491997)
  ·
    refine ⟨8479212563455808738434499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22611233502548823302491997 8479212563455808738434499)
    ·
      refine ⟨12718818845183713107651749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8479212563455808738434499 12718818845183713107651749)
      ·
        refine ⟨2384778533471946207684703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12718818845183713107651749 2384778533471946207684703)
        ·
          refine ⟨3577167800207919311527055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2384778533471946207684703 3577167800207919311527055)
          ·
            refine ⟨5365751700311878967290583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3577167800207919311527055 5365751700311878967290583)
            ·
              refine ⟨8048627550467818450935875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5365751700311878967290583 8048627550467818450935875)
              ·
                refine ⟨12072941325701727676403813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8048627550467818450935875 12072941325701727676403813)
                ·
                  refine ⟨2263676498569073939325715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12072941325701727676403813 2263676498569073939325715)
                  ·
                    refine ⟨3395514747853610908988573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2263676498569073939325715 3395514747853610908988573)
                    ·
                      refine ⟨1273318030445104090870715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3395514747853610908988573 1273318030445104090870715)
                      ·
                        rfl

theorem cell23_2479778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_2479778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479778 prefixEnd_2479778 := by exact prefixLift 2479778
  have htrace : WordTrace (prefixWord ++ tailWord_2479778) baseStart_2479778 baseEnd_2479778 := by
    simpa [prefixWord, tailWord_2479778, baseEnd_2479778] using wordTrace_append hprefix tailTrace_2479778
  have hstable : (prefixWord ++ tailWord_2479778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479778).length < 2 ^ (prefixWord ++ tailWord_2479778).sum := by decide
  have hdescent : baseEnd_2479778 < baseStart_2479778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479800 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 1, 1, 9]
def baseStart_2479800 : Nat := 118140960795 + 2479800 * 2 ^ 59
def prefixEnd_2479800 : Nat := 4983230072969 + 3 ^ 40 * 2479800 * 2
def baseEnd_2479800 : Nat := 1273329327019503004795613

theorem tailTrace_2479800 : CollatzResearch.WordTrace tailWord_2479800 prefixEnd_2479800 1273329327019503004795613 := by
  unfold tailWord_2479800
  simp only [CollatzResearch.WordTrace]
  refine ⟨45222868208057795483634427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60297157610743727311512569 45222868208057795483634427)
  ·
    refine ⟨67834302312086693225451641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45222868208057795483634427 67834302312086693225451641)
    ·
      refine ⟨50875726734065019919088731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67834302312086693225451641 50875726734065019919088731)
      ·
        refine ⟨76313590101097529878633097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50875726734065019919088731 76313590101097529878633097)
        ·
          refine ⟨57235192575823147408974823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76313590101097529878633097 57235192575823147408974823)
          ·
            refine ⟨85852788863734721113462235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57235192575823147408974823 85852788863734721113462235)
            ·
              refine ⟨128779183295602081670193353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85852788863734721113462235 128779183295602081670193353)
              ·
                refine ⟨96584387471701561252645015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128779183295602081670193353 96584387471701561252645015)
                ·
                  refine ⟨144876581207552341878967523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96584387471701561252645015 144876581207552341878967523)
                  ·
                    refine ⟨217314871811328512818451285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 144876581207552341878967523 217314871811328512818451285)
                    ·
                      refine ⟨1273329327019503004795613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 217314871811328512818451285 1273329327019503004795613)
                      ·
                        rfl

theorem cell23_2479800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_2479800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479800 prefixEnd_2479800 := by exact prefixLift 2479800
  have htrace : WordTrace (prefixWord ++ tailWord_2479800) baseStart_2479800 baseEnd_2479800 := by
    simpa [prefixWord, tailWord_2479800, baseEnd_2479800] using wordTrace_append hprefix tailTrace_2479800
  have hstable : (prefixWord ++ tailWord_2479800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479800).length < 2 ^ (prefixWord ++ tailWord_2479800).sum := by decide
  have hdescent : baseEnd_2479800 < baseStart_2479800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479801 : List Nat := [1, 2, 1, 4, 1, 1, 2, 5, 2, 2, 2]
def baseStart_2479801 : Nat := 118140960795 + 2479801 * 2 ^ 59
def prefixEnd_2479801 : Nat := 4983230072969 + 3 ^ 40 * 2479801 * 2
def baseEnd_2479801 : Nat := 1273329840500157500883109

theorem tailTrace_2479801 : CollatzResearch.WordTrace tailWord_2479801 prefixEnd_2479801 1273329840500157500883109 := by
  unfold tailWord_2479801
  simp only [CollatzResearch.WordTrace]
  refine ⟨90445772889111968138055257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60297181926074645425370171 90445772889111968138055257)
  ·
    refine ⟨67834329666833976103541443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90445772889111968138055257 67834329666833976103541443)
    ·
      refine ⟨101751494500250964155312165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67834329666833976103541443 101751494500250964155312165)
      ·
        refine ⟨19078405218797055779121031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101751494500250964155312165 19078405218797055779121031)
        ·
          refine ⟨28617607828195583668681547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19078405218797055779121031 28617607828195583668681547)
          ·
            refine ⟨42926411742293375503022321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28617607828195583668681547 42926411742293375503022321)
            ·
              refine ⟨32194808806720031627266741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42926411742293375503022321 32194808806720031627266741)
              ·
                refine ⟨3018263325630002965056257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32194808806720031627266741 3018263325630002965056257)
                ·
                  refine ⟨2263697494222502223792193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3018263325630002965056257 2263697494222502223792193)
                  ·
                    refine ⟨1697773120666876667844145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2263697494222502223792193 1697773120666876667844145)
                    ·
                      refine ⟨1273329840500157500883109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1697773120666876667844145 1273329840500157500883109)
                      ·
                        rfl

theorem cell23_2479801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_2479801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479801 prefixEnd_2479801 := by exact prefixLift 2479801
  have htrace : WordTrace (prefixWord ++ tailWord_2479801) baseStart_2479801 baseEnd_2479801 := by
    simpa [prefixWord, tailWord_2479801, baseEnd_2479801] using wordTrace_append hprefix tailTrace_2479801
  have hstable : (prefixWord ++ tailWord_2479801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479801).length < 2 ^ (prefixWord ++ tailWord_2479801).sum := by decide
  have hdescent : baseEnd_2479801 < baseStart_2479801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479821 : List Nat := [1, 6, 2, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_2479821 : Nat := 118140960795 + 2479821 * 2 ^ 59
def prefixEnd_2479821 : Nat := 4983230072969 + 3 ^ 40 * 2479821 * 2
def baseEnd_2479821 : Nat := 1273340110113247422633017

theorem tailTrace_2479821 : CollatzResearch.WordTrace tailWord_2479821 prefixEnd_2479821 1273340110113247422633017 := by
  unfold tailWord_2479821
  simp only [CollatzResearch.WordTrace]
  refine ⟨90446502349039511553783317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60297668232693007702522211 90446502349039511553783317)
  ·
    refine ⟨4239679797611227104083593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 90446502349039511553783317 4239679797611227104083593)
    ·
      refine ⟨3179759848208420328062695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4239679797611227104083593 3179759848208420328062695)
      ·
        refine ⟨4769639772312630492094043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3179759848208420328062695 4769639772312630492094043)
        ·
          refine ⟨7154459658468945738141065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4769639772312630492094043 7154459658468945738141065)
          ·
            refine ⟨5365844743851709303605799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7154459658468945738141065 5365844743851709303605799)
            ·
              refine ⟨8048767115777563955408699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5365844743851709303605799 8048767115777563955408699)
              ·
                refine ⟨12073150673666345933113049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8048767115777563955408699 12073150673666345933113049)
                ·
                  refine ⟨9054863005249759449834787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12073150673666345933113049 9054863005249759449834787)
                  ·
                    refine ⟨13582294507874639174752181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9054863005249759449834787 13582294507874639174752181)
                    ·
                      refine ⟨1273340110113247422633017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13582294507874639174752181 1273340110113247422633017)
                      ·
                        rfl

theorem cell23_2479821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_2479821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479821 prefixEnd_2479821 := by exact prefixLift 2479821
  have htrace : WordTrace (prefixWord ++ tailWord_2479821) baseStart_2479821 baseEnd_2479821 := by
    simpa [prefixWord, tailWord_2479821, baseEnd_2479821] using wordTrace_append hprefix tailTrace_2479821
  have hstable : (prefixWord ++ tailWord_2479821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479821).length < 2 ^ (prefixWord ++ tailWord_2479821).sum := by decide
  have hdescent : baseEnd_2479821 < baseStart_2479821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479841 : List Nat := [1, 2, 3, 1, 6, 1, 1, 1, 7]
def baseStart_2479841 : Nat := 118140960795 + 2479841 * 2 ^ 59
def prefixEnd_2479841 : Nat := 4983230072969 + 3 ^ 40 * 2479841 * 2
def baseEnd_2479841 : Nat := 141483375525148593820325

theorem tailTrace_2479841 : CollatzResearch.WordTrace tailWord_2479841 prefixEnd_2479841 141483375525148593820325 := by
  unfold tailWord_2479841
  simp only [CollatzResearch.WordTrace]
  refine ⟨90447231808967054969511377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60298154539311369979674251 90447231808967054969511377)
  ·
    refine ⟨67835423856725291227133533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90447231808967054969511377 67835423856725291227133533)
    ·
      refine ⟨25438283946271984210175075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67835423856725291227133533 25438283946271984210175075)
      ·
        refine ⟨38157425919407976315262613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25438283946271984210175075 38157425919407976315262613)
        ·
          refine ⟨1788629339972248889777935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38157425919407976315262613 1788629339972248889777935)
          ·
            refine ⟨2682944009958373334666903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1788629339972248889777935 2682944009958373334666903)
            ·
              refine ⟨4024416014937560002000355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2682944009958373334666903 4024416014937560002000355)
              ·
                refine ⟨6036624022406340003000533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4024416014937560002000355 6036624022406340003000533)
                ·
                  refine ⟨141483375525148593820325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6036624022406340003000533 141483375525148593820325)
                  ·
                    rfl

theorem cell23_2479841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 7].length) (baseStart_2479841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479841 prefixEnd_2479841 := by exact prefixLift 2479841
  have htrace : WordTrace (prefixWord ++ tailWord_2479841) baseStart_2479841 baseEnd_2479841 := by
    simpa [prefixWord, tailWord_2479841, baseEnd_2479841] using wordTrace_append hprefix tailTrace_2479841
  have hstable : (prefixWord ++ tailWord_2479841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479841).length < 2 ^ (prefixWord ++ tailWord_2479841).sum := by decide
  have hdescent : baseEnd_2479841 < baseStart_2479841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479844 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 2, 5, 2]
def baseStart_2479844 : Nat := 118140960795 + 2479844 * 2 ^ 59
def prefixEnd_2479844 : Nat := 4983230072969 + 3 ^ 40 * 2479844 * 2
def baseEnd_2479844 : Nat := 1273351920168300832645411

theorem tailTrace_2479844 : CollatzResearch.WordTrace tailWord_2479844 prefixEnd_2479844 1273351920168300832645411 := by
  unfold tailWord_2479844
  simp only [CollatzResearch.WordTrace]
  refine ⟨45223670613978093240935293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60298227485304124321247057 45223670613978093240935293)
  ·
    refine ⟨16958876480241784965350735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45223670613978093240935293 16958876480241784965350735)
    ·
      refine ⟨25438314720362677448026103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16958876480241784965350735 25438314720362677448026103)
      ·
        refine ⟨38157472080544016172039155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25438314720362677448026103 38157472080544016172039155)
        ·
          refine ⟨57236208120816024258058733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38157472080544016172039155 57236208120816024258058733)
          ·
            refine ⟨21463578045306009096772025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57236208120816024258058733 21463578045306009096772025)
            ·
              refine ⟨16097683533979506822579019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21463578045306009096772025 16097683533979506822579019)
              ·
                refine ⟨24146525300969260233868529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16097683533979506822579019 24146525300969260233868529)
                ·
                  refine ⟨18109893975726945175401397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24146525300969260233868529 18109893975726945175401397)
                  ·
                    refine ⟨1697802560224401110193881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18109893975726945175401397 1697802560224401110193881)
                    ·
                      refine ⟨1273351920168300832645411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1697802560224401110193881 1273351920168300832645411)
                      ·
                        rfl

theorem cell23_2479844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 2, 5, 2].length) (baseStart_2479844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479844 prefixEnd_2479844 := by exact prefixLift 2479844
  have htrace : WordTrace (prefixWord ++ tailWord_2479844) baseStart_2479844 baseEnd_2479844 := by
    simpa [prefixWord, tailWord_2479844, baseEnd_2479844] using wordTrace_append hprefix tailTrace_2479844
  have hstable : (prefixWord ++ tailWord_2479844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479844).length < 2 ^ (prefixWord ++ tailWord_2479844).sum := by decide
  have hdescent : baseEnd_2479844 < baseStart_2479844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479918 : List Nat := [4, 1, 3, 2, 2, 1, 1, 2, 3, 4]
def baseStart_2479918 : Nat := 118140960795 + 2479918 * 2 ^ 59
def prefixEnd_2479918 : Nat := 4983230072969 + 3 ^ 40 * 2479918 * 2
def baseEnd_2479918 : Nat := 424463305912244514373357

theorem tailTrace_2479918 : CollatzResearch.WordTrace tailWord_2479918 prefixEnd_2479918 424463305912244514373357 := by
  unfold tailWord_2479918
  simp only [CollatzResearch.WordTrace]
  refine ⟨11306255028711012140008051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60300026819792064746709605 11306255028711012140008051)
  ·
    refine ⟨16959382543066518210012077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11306255028711012140008051 16959382543066518210012077)
    ·
      refine ⟨6359768453649944328754529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16959382543066518210012077 6359768453649944328754529)
      ·
        refine ⟨4769826340237458246565897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6359768453649944328754529 4769826340237458246565897)
        ·
          refine ⟨3577369755178093684924423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4769826340237458246565897 3577369755178093684924423)
          ·
            refine ⟨5366054632767140527386635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3577369755178093684924423 5366054632767140527386635)
            ·
              refine ⟨8049081949150710791079953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5366054632767140527386635 8049081949150710791079953)
              ·
                refine ⟨6036811461863033093309965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8049081949150710791079953 6036811461863033093309965)
                ·
                  refine ⟨2263804298198637409991237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6036811461863033093309965 2263804298198637409991237)
                  ·
                    refine ⟨424463305912244514373357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2263804298198637409991237 424463305912244514373357)
                    ·
                      rfl

theorem cell23_2479918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_2479918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479918 prefixEnd_2479918 := by exact prefixLift 2479918
  have htrace : WordTrace (prefixWord ++ tailWord_2479918) baseStart_2479918 baseEnd_2479918 := by
    simpa [prefixWord, tailWord_2479918, baseEnd_2479918] using wordTrace_append hprefix tailTrace_2479918
  have hstable : (prefixWord ++ tailWord_2479918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479918).length < 2 ^ (prefixWord ++ tailWord_2479918).sum := by decide
  have hdescent : baseEnd_2479918 < baseStart_2479918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479948 : List Nat := [2, 2, 1, 3, 5, 1, 1, 2, 6]
def baseStart_2479948 : Nat := 118140960795 + 2479948 * 2 ^ 59
def prefixEnd_2479948 : Nat := 4983230072969 + 3 ^ 40 * 2479948 * 2
def baseEnd_2479948 : Nat := 141489480239596491749437

theorem tailTrace_2479948 : CollatzResearch.WordTrace tailWord_2479948 prefixEnd_2479948 141489480239596491749437 := by
  unfold tailWord_2479948
  simp only [CollatzResearch.WordTrace]
  refine ⟨45225567209789706121828249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60300756279719608162437665 45225567209789706121828249)
  ·
    refine ⟨33919175407342279591371187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45225567209789706121828249 33919175407342279591371187)
    ·
      refine ⟨50878763111013419387056781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33919175407342279591371187 50878763111013419387056781)
      ·
        refine ⟨19079536166630032270146293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50878763111013419387056781 19079536166630032270146293)
        ·
          refine ⟨1788706515621565525326215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19079536166630032270146293 1788706515621565525326215)
          ·
            refine ⟨2683059773432348287989323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1788706515621565525326215 2683059773432348287989323)
            ·
              refine ⟨4024589660148522431983985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2683059773432348287989323 4024589660148522431983985)
              ·
                refine ⟨3018442245111391823987989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4024589660148522431983985 3018442245111391823987989)
                ·
                  refine ⟨141489480239596491749437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3018442245111391823987989 141489480239596491749437)
                  ·
                    rfl

theorem cell23_2479948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 6].length) (baseStart_2479948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479948 prefixEnd_2479948 := by exact prefixLift 2479948
  have htrace : WordTrace (prefixWord ++ tailWord_2479948) baseStart_2479948 baseEnd_2479948 := by
    simpa [prefixWord, tailWord_2479948, baseEnd_2479948] using wordTrace_append hprefix tailTrace_2479948
  have hstable : (prefixWord ++ tailWord_2479948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479948).length < 2 ^ (prefixWord ++ tailWord_2479948).sum := by decide
  have hdescent : baseEnd_2479948 < baseStart_2479948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479981 : List Nat := [1, 5, 1, 1, 1, 1, 3, 4, 1, 1, 4]
def baseStart_2479981 : Nat := 118140960795 + 2479981 * 2 ^ 59
def prefixEnd_2479981 : Nat := 4983230072969 + 3 ^ 40 * 2479981 * 2
def baseEnd_2479981 : Nat := 1273422267017966796632281

theorem tailTrace_2479981 : CollatzResearch.WordTrace tailWord_2479981 prefixEnd_2479981 1273422267017966796632281 := by
  unfold tailWord_2479981
  simp only [CollatzResearch.WordTrace]
  refine ⟨90452338028459858879607797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60301558685639905919738531 90452338028459858879607797)
  ·
    refine ⟨8479906690168111769963231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90452338028459858879607797 8479906690168111769963231)
    ·
      refine ⟨12719860035252167654944847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8479906690168111769963231 12719860035252167654944847)
      ·
        refine ⟨19079790052878251482417271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12719860035252167654944847 19079790052878251482417271)
        ·
          refine ⟨28619685079317377223625907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19079790052878251482417271 28619685079317377223625907)
          ·
            refine ⟨42929527618976065835438861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28619685079317377223625907 42929527618976065835438861)
            ·
              refine ⟨16098572857116024688289573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42929527618976065835438861 16098572857116024688289573)
              ·
                refine ⟨3018482410709254629054295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16098572857116024688289573 3018482410709254629054295)
                ·
                  refine ⟨4527723616063881943581443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3018482410709254629054295 4527723616063881943581443)
                  ·
                    refine ⟨6791585424095822915372165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4527723616063881943581443 6791585424095822915372165)
                    ·
                      refine ⟨1273422267017966796632281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6791585424095822915372165 1273422267017966796632281)
                      ·
                        rfl

theorem cell23_2479981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_2479981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479981 prefixEnd_2479981 := by exact prefixLift 2479981
  have htrace : WordTrace (prefixWord ++ tailWord_2479981) baseStart_2479981 baseEnd_2479981 := by
    simpa [prefixWord, tailWord_2479981, baseEnd_2479981] using wordTrace_append hprefix tailTrace_2479981
  have hstable : (prefixWord ++ tailWord_2479981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479981).length < 2 ^ (prefixWord ++ tailWord_2479981).sum := by decide
  have hdescent : baseEnd_2479981 < baseStart_2479981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479994 : List Nat := [3, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4]
def baseStart_2479994 : Nat := 118140960795 + 2479994 * 2 ^ 59
def prefixEnd_2479994 : Nat := 4983230072969 + 3 ^ 40 * 2479994 * 2
def baseEnd_2479994 : Nat := 1273428942266475245769721

theorem tailTrace_2479994 : CollatzResearch.WordTrace tailWord_2479994 prefixEnd_2479994 1273428942266475245769721 := by
  unfold tailWord_2479994
  simp only [CollatzResearch.WordTrace]
  refine ⟨22613203044353190524957759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60301874784941841399887357 22613203044353190524957759)
  ·
    refine ⟨33919804566529785787436639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22613203044353190524957759 33919804566529785787436639)
    ·
      refine ⟨50879706849794678681154959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33919804566529785787436639 50879706849794678681154959)
      ·
        refine ⟨76319560274692018021732439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50879706849794678681154959 76319560274692018021732439)
        ·
          refine ⟨114479340412038027032598659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76319560274692018021732439 114479340412038027032598659)
          ·
            refine ⟨171719010618057040548897989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114479340412038027032598659 171719010618057040548897989)
            ·
              refine ⟨32197314490885695102918373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 171719010618057040548897989 32197314490885695102918373)
              ·
                refine ⟨6036996467041067831797195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32197314490885695102918373 6036996467041067831797195)
                ·
                  refine ⟨9055494700561601747695793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6036996467041067831797195 9055494700561601747695793)
                  ·
                    refine ⟨6791621025421201310771845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9055494700561601747695793 6791621025421201310771845)
                    ·
                      refine ⟨1273428942266475245769721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6791621025421201310771845 1273428942266475245769721)
                      ·
                        rfl

theorem cell23_2479994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_2479994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2479994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2479994 prefixEnd_2479994 := by exact prefixLift 2479994
  have htrace : WordTrace (prefixWord ++ tailWord_2479994) baseStart_2479994 baseEnd_2479994 := by
    simpa [prefixWord, tailWord_2479994, baseEnd_2479994] using wordTrace_append hprefix tailTrace_2479994
  have hstable : (prefixWord ++ tailWord_2479994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479994).length < 2 ^ (prefixWord ++ tailWord_2479994).sum := by decide
  have hdescent : baseEnd_2479994 < baseStart_2479994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480052 : List Nat := [2, 5, 2, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_2480052 : Nat := 118140960795 + 2480052 * 2 ^ 59
def prefixEnd_2480052 : Nat := 4983230072969 + 3 ^ 40 * 2480052 * 2
def baseEnd_2480052 : Nat := 1273458724144436018844455

theorem tailTrace_2480052 : CollatzResearch.WordTrace tailWord_2480052 prefixEnd_2480052 1273458724144436018844455 := by
  unfold tailWord_2480052
  simp only [CollatzResearch.WordTrace]
  refine ⟨45227463805601319002721205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60303285074135092003628273 45227463805601319002721205)
  ·
    refine ⟨4240074731775123656505113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45227463805601319002721205 4240074731775123656505113)
    ·
      refine ⟨3180056048831342742378835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4240074731775123656505113 3180056048831342742378835)
      ·
        refine ⟨4770084073247014113568253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3180056048831342742378835 4770084073247014113568253)
        ·
          refine ⟨1788781527467630292588095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4770084073247014113568253 1788781527467630292588095)
          ·
            refine ⟨2683172291201445438882143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1788781527467630292588095 2683172291201445438882143)
            ·
              refine ⟨4024758436802168158323215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2683172291201445438882143 4024758436802168158323215)
              ·
                refine ⟨6037137655203252237484823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4024758436802168158323215 6037137655203252237484823)
                ·
                  refine ⟨9055706482804878356227235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6037137655203252237484823 9055706482804878356227235)
                  ·
                    refine ⟨13583559724207317534340853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9055706482804878356227235 13583559724207317534340853)
                    ·
                      refine ⟨1273458724144436018844455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13583559724207317534340853 1273458724144436018844455)
                      ·
                        rfl

theorem cell23_2480052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_2480052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480052 prefixEnd_2480052 := by exact prefixLift 2480052
  have htrace : WordTrace (prefixWord ++ tailWord_2480052) baseStart_2480052 baseEnd_2480052 := by
    simpa [prefixWord, tailWord_2480052, baseEnd_2480052] using wordTrace_append hprefix tailTrace_2480052
  have hstable : (prefixWord ++ tailWord_2480052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480052).length < 2 ^ (prefixWord ++ tailWord_2480052).sum := by decide
  have hdescent : baseEnd_2480052 < baseStart_2480052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480064 : List Nat := [2, 1, 1, 2, 3, 2, 2, 2, 2, 6]
def baseStart_2480064 : Nat := 118140960795 + 2480064 * 2 ^ 59
def prefixEnd_2480064 : Nat := 4983230072969 + 3 ^ 40 * 2480064 * 2
def baseEnd_2480064 : Nat := 424488295304096657298133

theorem tailTrace_2480064 : CollatzResearch.WordTrace tailWord_2480064 prefixEnd_2480064 424488295304096657298133 := by
  unfold tailWord_2480064
  simp only [CollatzResearch.WordTrace]
  refine ⟨45227682643579582027439623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60303576858106109369919497 45227682643579582027439623)
  ·
    refine ⟨67841523965369373041159435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45227682643579582027439623 67841523965369373041159435)
    ·
      refine ⟨101762285948054059561739153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67841523965369373041159435 101762285948054059561739153)
      ·
        refine ⟨76321714461040544671304365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101762285948054059561739153 76321714461040544671304365)
        ·
          refine ⟨28620642922890204251739137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76321714461040544671304365 28620642922890204251739137)
          ·
            refine ⟨21465482192167653188804353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28620642922890204251739137 21465482192167653188804353)
            ·
              refine ⟨16099111644125739891603265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21465482192167653188804353 16099111644125739891603265)
              ·
                refine ⟨12074333733094304918702449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16099111644125739891603265 12074333733094304918702449)
                ·
                  refine ⟨9055750299820728689026837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12074333733094304918702449 9055750299820728689026837)
                  ·
                    refine ⟨424488295304096657298133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9055750299820728689026837 424488295304096657298133)
                    ·
                      rfl

theorem cell23_2480064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 2, 6].length) (baseStart_2480064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480064 prefixEnd_2480064 := by exact prefixLift 2480064
  have htrace : WordTrace (prefixWord ++ tailWord_2480064) baseStart_2480064 baseEnd_2480064 := by
    simpa [prefixWord, tailWord_2480064, baseEnd_2480064] using wordTrace_append hprefix tailTrace_2480064
  have hstable : (prefixWord ++ tailWord_2480064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480064).length < 2 ^ (prefixWord ++ tailWord_2480064).sum := by decide
  have hdescent : baseEnd_2480064 < baseStart_2480064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480071 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 5, 4, 2]
def baseStart_2480071 : Nat := 118140960795 + 2480071 * 2 ^ 59
def prefixEnd_2480071 : Nat := 4983230072969 + 3 ^ 40 * 2480071 * 2
def baseEnd_2480071 : Nat := 1273468480276871444506867

theorem tailTrace_2480071 : CollatzResearch.WordTrace tailWord_2480071 prefixEnd_2480071 1273468480276871444506867 := by
  unfold tailWord_2480071
  simp only [CollatzResearch.WordTrace]
  refine ⟨90455620598133804250384067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60303747065422536166922711 90455620598133804250384067)
  ·
    refine ⟨135683430897200706375576101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90455620598133804250384067 135683430897200706375576101)
    ·
      refine ⟨25440643293225132445420519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135683430897200706375576101 25440643293225132445420519)
      ·
        refine ⟨38160964939837698668130779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25440643293225132445420519 38160964939837698668130779)
        ·
          refine ⟨57241447409756548002196169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38160964939837698668130779 57241447409756548002196169)
          ·
            refine ⟨42931085557317411001647127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57241447409756548002196169 42931085557317411001647127)
            ·
              refine ⟨64396628335976116502470691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42931085557317411001647127 64396628335976116502470691)
              ·
                refine ⟨96594942503964174753706037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64396628335976116502470691 96594942503964174753706037)
                ·
                  refine ⟨9055775859746641383159941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 96594942503964174753706037 9055775859746641383159941)
                  ·
                    refine ⟨1697957973702495259342489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9055775859746641383159941 1697957973702495259342489)
                    ·
                      refine ⟨1273468480276871444506867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1697957973702495259342489 1273468480276871444506867)
                      ·
                        rfl

theorem cell23_2480071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 4, 2].length) (baseStart_2480071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480071 prefixEnd_2480071 := by exact prefixLift 2480071
  have htrace : WordTrace (prefixWord ++ tailWord_2480071) baseStart_2480071 baseEnd_2480071 := by
    simpa [prefixWord, tailWord_2480071, baseEnd_2480071] using wordTrace_append hprefix tailTrace_2480071
  have hstable : (prefixWord ++ tailWord_2480071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480071).length < 2 ^ (prefixWord ++ tailWord_2480071).sum := by decide
  have hdescent : baseEnd_2480071 < baseStart_2480071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480074 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 1, 3, 5]
def baseStart_2480074 : Nat := 118140960795 + 2480074 * 2 ^ 59
def prefixEnd_2480074 : Nat := 4983230072969 + 3 ^ 40 * 2480074 * 2
def baseEnd_2480074 : Nat := 1273470020718834932769353

theorem tailTrace_2480074 : CollatzResearch.WordTrace tailWord_2480074 prefixEnd_2480074 1273470020718834932769353 := by
  unfold tailWord_2480074
  simp only [CollatzResearch.WordTrace]
  refine ⟨22613932504280733940685819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60303820011415290508495517 22613932504280733940685819)
  ·
    refine ⟨33920898756421100911028729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22613932504280733940685819 33920898756421100911028729)
    ·
      refine ⟨25440674067315825683271547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33920898756421100911028729 25440674067315825683271547)
      ·
        refine ⟨38161011100973738524907321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25440674067315825683271547 38161011100973738524907321)
        ·
          refine ⟨28620758325730303893680491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38161011100973738524907321 28620758325730303893680491)
          ·
            refine ⟨42931137488595455840520737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28620758325730303893680491 42931137488595455840520737)
            ·
              refine ⟨32198353116446591880390553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42931137488595455840520737 32198353116446591880390553)
              ·
                refine ⟨24148764837334943910292915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32198353116446591880390553 24148764837334943910292915)
                ·
                  refine ⟨36223147256002415865439373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24148764837334943910292915 36223147256002415865439373)
                  ·
                    refine ⟨13583680221000905949539765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36223147256002415865439373 13583680221000905949539765)
                    ·
                      refine ⟨1273470020718834932769353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13583680221000905949539765 1273470020718834932769353)
                      ·
                        rfl

theorem cell23_2480074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_2480074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480074 prefixEnd_2480074 := by exact prefixLift 2480074
  have htrace : WordTrace (prefixWord ++ tailWord_2480074) baseStart_2480074 baseEnd_2480074 := by
    simpa [prefixWord, tailWord_2480074, baseEnd_2480074] using wordTrace_append hprefix tailTrace_2480074
  have hstable : (prefixWord ++ tailWord_2480074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480074).length < 2 ^ (prefixWord ++ tailWord_2480074).sum := by decide
  have hdescent : baseEnd_2480074 < baseStart_2480074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480088 : List Nat := [2, 1, 2, 2, 2, 2, 4, 1, 1, 4, 2]
def baseStart_2480088 : Nat := 118140960795 + 2480088 * 2 ^ 59
def prefixEnd_2480088 : Nat := 4983230072969 + 3 ^ 40 * 2480088 * 2
def baseEnd_2480088 : Nat := 1273477209447997877994289

theorem tailTrace_2480088 : CollatzResearch.WordTrace tailWord_2480088 prefixEnd_2480088 1273477209447997877994289 := by
  unfold tailWord_2480088
  simp only [CollatzResearch.WordTrace]
  refine ⟨45228120319536108076876459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60304160426048144102501945 45228120319536108076876459)
  ·
    refine ⟨67842180479304162115314689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45228120319536108076876459 67842180479304162115314689)
    ·
      refine ⟨50881635359478121586486017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67842180479304162115314689 50881635359478121586486017)
      ·
        refine ⟨38161226519608591189864513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50881635359478121586486017 38161226519608591189864513)
        ·
          refine ⟨28620919889706443392398385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38161226519608591189864513 28620919889706443392398385)
          ·
            refine ⟨21465689917279832544298789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28620919889706443392398385 21465689917279832544298789)
            ·
              refine ⟨4024816859489968602056023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21465689917279832544298789 4024816859489968602056023)
              ·
                refine ⟨6037225289234952903084035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4024816859489968602056023 6037225289234952903084035)
                ·
                  refine ⟨9055837933852429354626053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6037225289234952903084035 9055837933852429354626053)
                  ·
                    refine ⟨1697969612597330503992385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9055837933852429354626053 1697969612597330503992385)
                    ·
                      refine ⟨1273477209447997877994289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1697969612597330503992385 1273477209447997877994289)
                      ·
                        rfl

theorem cell23_2480088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 1, 4, 2].length) (baseStart_2480088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480088 prefixEnd_2480088 := by exact prefixLift 2480088
  have htrace : WordTrace (prefixWord ++ tailWord_2480088) baseStart_2480088 baseEnd_2480088 := by
    simpa [prefixWord, tailWord_2480088, baseEnd_2480088] using wordTrace_append hprefix tailTrace_2480088
  have hstable : (prefixWord ++ tailWord_2480088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480088).length < 2 ^ (prefixWord ++ tailWord_2480088).sum := by decide
  have hdescent : baseEnd_2480088 < baseStart_2480088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480104 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_2480104 : Nat := 118140960795 + 2480104 * 2 ^ 59
def prefixEnd_2480104 : Nat := 4983230072969 + 3 ^ 40 * 2480104 * 2
def baseEnd_2480104 : Nat := 1273485425138469815394215

theorem tailTrace_2480104 : CollatzResearch.WordTrace tailWord_2480104 prefixEnd_2480104 1273485425138469815394215 := by
  unfold tailWord_2480104
  simp only [CollatzResearch.WordTrace]
  refine ⟨45228412103507125443167683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60304549471342833924223577 45228412103507125443167683)
  ·
    refine ⟨67842618155260688164751525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45228412103507125443167683 67842618155260688164751525)
    ·
      refine ⟨12720490904111379030890911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67842618155260688164751525 12720490904111379030890911)
      ·
        refine ⟨19080736356167068546336367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12720490904111379030890911 19080736356167068546336367)
        ·
          refine ⟨28621104534250602819504551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19080736356167068546336367 28621104534250602819504551)
          ·
            refine ⟨42931656801375904229256827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28621104534250602819504551 42931656801375904229256827)
            ·
              refine ⟨64397485202063856343885241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42931656801375904229256827 64397485202063856343885241)
              ·
                refine ⟨48298113901547892257913931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64397485202063856343885241 48298113901547892257913931)
                ·
                  refine ⟨72447170852321838386870897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48298113901547892257913931 72447170852321838386870897)
                  ·
                    refine ⟨54335378139241378790153173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72447170852321838386870897 54335378139241378790153173)
                    ·
                      refine ⟨1273485425138469815394215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54335378139241378790153173 1273485425138469815394215)
                      ·
                        rfl

theorem cell23_2480104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_2480104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480104 prefixEnd_2480104 := by exact prefixLift 2480104
  have htrace : WordTrace (prefixWord ++ tailWord_2480104) baseStart_2480104 baseEnd_2480104 := by
    simpa [prefixWord, tailWord_2480104, baseEnd_2480104] using wordTrace_append hprefix tailTrace_2480104
  have hstable : (prefixWord ++ tailWord_2480104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480104).length < 2 ^ (prefixWord ++ tailWord_2480104).sum := by decide
  have hdescent : baseEnd_2480104 < baseStart_2480104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480121 : List Nat := [1, 2, 1, 3, 1, 4, 1, 2, 2, 3, 3]
def baseStart_2480121 : Nat := 118140960795 + 2480121 * 2 ^ 59
def prefixEnd_2480121 : Nat := 4983230072969 + 3 ^ 40 * 2480121 * 2
def baseEnd_2480121 : Nat := 1273494154309596248881637

theorem tailTrace_2480121 : CollatzResearch.WordTrace tailWord_2480121 prefixEnd_2480121 1273494154309596248881637 := by
  unfold tailWord_2480121
  simp only [CollatzResearch.WordTrace]
  refine ⟨90457444247952662789704217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60304962831968441859802811 90457444247952662789704217)
  ·
    refine ⟨67843083185964497092278163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90457444247952662789704217 67843083185964497092278163)
    ·
      refine ⟨101764624778946745638417245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67843083185964497092278163 101764624778946745638417245)
      ·
        refine ⟨38161734292105029614406467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101764624778946745638417245 38161734292105029614406467)
        ·
          refine ⟨57242601438157544421609701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38161734292105029614406467 57242601438157544421609701)
          ·
            refine ⟨10732987769654539579051819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57242601438157544421609701 10732987769654539579051819)
            ·
              refine ⟨16099481654481809368577729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10732987769654539579051819 16099481654481809368577729)
              ·
                refine ⟨12074611240861357026433297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16099481654481809368577729 12074611240861357026433297)
                ·
                  refine ⟨9055958430646017769824973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12074611240861357026433297 9055958430646017769824973)
                  ·
                    refine ⟨3395984411492256663684365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9055958430646017769824973 3395984411492256663684365)
                    ·
                      refine ⟨1273494154309596248881637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3395984411492256663684365 1273494154309596248881637)
                      ·
                        rfl

theorem cell23_2480121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_2480121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480121 prefixEnd_2480121 := by exact prefixLift 2480121
  have htrace : WordTrace (prefixWord ++ tailWord_2480121) baseStart_2480121 baseEnd_2480121 := by
    simpa [prefixWord, tailWord_2480121, baseEnd_2480121] using wordTrace_append hprefix tailTrace_2480121
  have hstable : (prefixWord ++ tailWord_2480121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480121).length < 2 ^ (prefixWord ++ tailWord_2480121).sum := by decide
  have hdescent : baseEnd_2480121 < baseStart_2480121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480131 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 1, 7, 2]
def baseStart_2480131 : Nat := 118140960795 + 2480131 * 2 ^ 59
def prefixEnd_2480131 : Nat := 4983230072969 + 3 ^ 40 * 2480131 * 2
def baseEnd_2480131 : Nat := 1273499289116141209756591

theorem tailTrace_2480131 : CollatzResearch.WordTrace tailWord_2480131 prefixEnd_2480131 1273499289116141209756591 := by
  unfold tailWord_2480131
  simp only [CollatzResearch.WordTrace]
  refine ⟨90457808977916434497568247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60305205985277622998378831 90457808977916434497568247)
  ·
    refine ⟨135686713466874651746352371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90457808977916434497568247 135686713466874651746352371)
    ·
      refine ⟨203530070200311977619528557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135686713466874651746352371 203530070200311977619528557)
      ·
        refine ⟨76323776325116991607323209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203530070200311977619528557 76323776325116991607323209)
        ·
          refine ⟨57242832243837743705492407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76323776325116991607323209 57242832243837743705492407)
          ·
            refine ⟨85864248365756615558238611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57242832243837743705492407 85864248365756615558238611)
            ·
              refine ⟨128796372548634923337357917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85864248365756615558238611 128796372548634923337357917)
              ·
                refine ⟨48298639705738096251509219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128796372548634923337357917 48298639705738096251509219)
                ·
                  refine ⟨72447959558607144377263829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48298639705738096251509219 72447959558607144377263829)
                  ·
                    refine ⟨1697999052154854946342121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 72447959558607144377263829 1697999052154854946342121)
                    ·
                      refine ⟨1273499289116141209756591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1697999052154854946342121 1273499289116141209756591)
                      ·
                        rfl

theorem cell23_2480131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 7, 2].length) (baseStart_2480131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480131 prefixEnd_2480131 := by exact prefixLift 2480131
  have htrace : WordTrace (prefixWord ++ tailWord_2480131) baseStart_2480131 baseEnd_2480131 := by
    simpa [prefixWord, tailWord_2480131, baseEnd_2480131] using wordTrace_append hprefix tailTrace_2480131
  have hstable : (prefixWord ++ tailWord_2480131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480131).length < 2 ^ (prefixWord ++ tailWord_2480131).sum := by decide
  have hdescent : baseEnd_2480131 < baseStart_2480131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480178 : List Nat := [3, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4]
def baseStart_2480178 : Nat := 118140960795 + 2480178 * 2 ^ 59
def prefixEnd_2480178 : Nat := 4983230072969 + 3 ^ 40 * 2480178 * 2
def baseEnd_2480178 : Nat := 1273523422706902525868875

theorem tailTrace_2480178 : CollatzResearch.WordTrace tailWord_2480178 prefixEnd_2480178 1273523422706902525868875 := by
  unfold tailWord_2480178
  simp only [CollatzResearch.WordTrace]
  refine ⟨22614880802186540381132297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60306348805830774349686125 22614880802186540381132297)
  ·
    refine ⟨16961160601639905285849223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22614880802186540381132297 16961160601639905285849223)
    ·
      refine ⟨25441740902459857928773835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16961160601639905285849223 25441740902459857928773835)
      ·
        refine ⟨38162611353689786893160753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25441740902459857928773835 38162611353689786893160753)
        ·
          refine ⟨28621958515267340169870565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38162611353689786893160753 28621958515267340169870565)
          ·
            refine ⟨5366617221612626281850731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28621958515267340169870565 5366617221612626281850731)
            ·
              refine ⟨8049925832418939422776097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5366617221612626281850731 8049925832418939422776097)
              ·
                refine ⟨6037444374314204567082073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8049925832418939422776097 6037444374314204567082073)
                ·
                  refine ⟨4528083280735653425311555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6037444374314204567082073 4528083280735653425311555)
                  ·
                    refine ⟨6792124921103480137967333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4528083280735653425311555 6792124921103480137967333)
                    ·
                      refine ⟨1273523422706902525868875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6792124921103480137967333 1273523422706902525868875)
                      ·
                        rfl

theorem cell23_2480178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_2480178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480178 prefixEnd_2480178 := by exact prefixLift 2480178
  have htrace : WordTrace (prefixWord ++ tailWord_2480178) baseStart_2480178 baseEnd_2480178 := by
    simpa [prefixWord, tailWord_2480178, baseEnd_2480178] using wordTrace_append hprefix tailTrace_2480178
  have hstable : (prefixWord ++ tailWord_2480178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480178).length < 2 ^ (prefixWord ++ tailWord_2480178).sum := by decide
  have hdescent : baseEnd_2480178 < baseStart_2480178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480201 : List Nat := [1, 2, 1, 1, 2, 2, 5, 3, 6]
def baseStart_2480201 : Nat := 118140960795 + 2480201 * 2 ^ 59
def prefixEnd_2480201 : Nat := 4983230072969 + 3 ^ 40 * 2480201 * 2
def baseEnd_2480201 : Nat := 141503914751328437320141

theorem tailTrace_2480201 : CollatzResearch.WordTrace tailWord_2480201 prefixEnd_2480201 141503914751328437320141 := by
  unfold tailWord_2480201
  simp only [CollatzResearch.WordTrace]
  refine ⟨90460362087662836452616457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60306908058441890968410971 90460362087662836452616457)
  ·
    refine ⟨67845271565747127339462343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90460362087662836452616457 67845271565747127339462343)
    ·
      refine ⟨101767907348620691009193515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67845271565747127339462343 101767907348620691009193515)
      ·
        refine ⟨152651861022931036513790273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101767907348620691009193515 152651861022931036513790273)
        ·
          refine ⟨114488895767198277385342705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152651861022931036513790273 114488895767198277385342705)
          ·
            refine ⟨85866671825398708039007029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114488895767198277385342705 85866671825398708039007029)
            ·
              refine ⟨8050000483631128878656909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85866671825398708039007029 8050000483631128878656909)
              ·
                refine ⟨3018750181361673329496341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8050000483631128878656909 3018750181361673329496341)
                ·
                  refine ⟨141503914751328437320141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3018750181361673329496341 141503914751328437320141)
                  ·
                    rfl

theorem cell23_2480201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 6].length) (baseStart_2480201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480201 prefixEnd_2480201 := by exact prefixLift 2480201
  have htrace : WordTrace (prefixWord ++ tailWord_2480201) baseStart_2480201 baseEnd_2480201 := by
    simpa [prefixWord, tailWord_2480201, baseEnd_2480201] using wordTrace_append hprefix tailTrace_2480201
  have hstable : (prefixWord ++ tailWord_2480201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480201).length < 2 ^ (prefixWord ++ tailWord_2480201).sum := by decide
  have hdescent : baseEnd_2480201 < baseStart_2480201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480279 : List Nat := [1, 1, 3, 3, 4, 1, 2, 3, 1, 1, 3]
def baseStart_2480279 : Nat := 118140960795 + 2480279 * 2 ^ 59
def prefixEnd_2480279 : Nat := 4983230072969 + 3 ^ 40 * 2480279 * 2
def baseEnd_2480279 : Nat := 1273575284253006630705911

theorem tailTrace_2480279 : CollatzResearch.WordTrace tailWord_2480279 prefixEnd_2480279 1273575284253006630705911 := by
  unfold tailWord_2480279
  simp only [CollatzResearch.WordTrace]
  refine ⟨90463206981380255773955891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60308804654253503849303927 90463206981380255773955891)
  ·
    refine ⟨135694810472070383660933837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90463206981380255773955891 135694810472070383660933837)
    ·
      refine ⟨50885553927026393872850189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135694810472070383660933837 50885553927026393872850189)
      ·
        refine ⟨19082082722634897702318821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50885553927026393872850189 19082082722634897702318821)
        ·
          refine ⟨3577890510494043319184779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19082082722634897702318821 3577890510494043319184779)
          ·
            refine ⟨5366835765741064978777169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3577890510494043319184779 5366835765741064978777169)
            ·
              refine ⟨4025126824305798734082877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5366835765741064978777169 4025126824305798734082877)
              ·
                refine ⟨1509422559114674525281079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4025126824305798734082877 1509422559114674525281079)
                ·
                  refine ⟨2264133838672011787921619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1509422559114674525281079 2264133838672011787921619)
                  ·
                    refine ⟨3396200758008017681882429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2264133838672011787921619 3396200758008017681882429)
                    ·
                      refine ⟨1273575284253006630705911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3396200758008017681882429 1273575284253006630705911)
                      ·
                        rfl

theorem cell23_2480279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_2480279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480279 prefixEnd_2480279 := by exact prefixLift 2480279
  have htrace : WordTrace (prefixWord ++ tailWord_2480279) baseStart_2480279 baseEnd_2480279 := by
    simpa [prefixWord, tailWord_2480279, baseEnd_2480279] using wordTrace_append hprefix tailTrace_2480279
  have hstable : (prefixWord ++ tailWord_2480279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480279).length < 2 ^ (prefixWord ++ tailWord_2480279).sum := by decide
  have hdescent : baseEnd_2480279 < baseStart_2480279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480285 : List Nat := [1, 4, 2, 1, 1, 4, 1, 3, 1, 1, 4]
def baseStart_2480285 : Nat := 118140960795 + 2480285 * 2 ^ 59
def prefixEnd_2480285 : Nat := 4983230072969 + 3 ^ 40 * 2480285 * 2
def baseEnd_2480285 : Nat := 1273578365136933607230883

theorem tailTrace_2480285 : CollatzResearch.WordTrace tailWord_2480285 prefixEnd_2480285 1273578365136933607230883 := by
  unfold tailWord_2480285
  simp only [CollatzResearch.WordTrace]
  refine ⟨90463425819358518798674309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60308950546239012532449539 90463425819358518798674309)
  ·
    refine ⟨16961892341129722274751433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90463425819358518798674309 16961892341129722274751433)
    ·
      refine ⟨12721419255847291706063575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16961892341129722274751433 12721419255847291706063575)
      ·
        refine ⟨19082128883770937559095363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12721419255847291706063575 19082128883770937559095363)
        ·
          refine ⟨28623193325656406338643045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19082128883770937559095363 28623193325656406338643045)
          ·
            refine ⟨5366848748560576188495571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28623193325656406338643045 5366848748560576188495571)
            ·
              refine ⟨8050273122840864282743357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5366848748560576188495571 8050273122840864282743357)
              ·
                refine ⟨3018852421065324106028759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8050273122840864282743357 3018852421065324106028759)
                ·
                  refine ⟨4528278631597986159043139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3018852421065324106028759 4528278631597986159043139)
                  ·
                    refine ⟨6792417947396979238564709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4528278631597986159043139 6792417947396979238564709)
                    ·
                      refine ⟨1273578365136933607230883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6792417947396979238564709 1273578365136933607230883)
                      ·
                        rfl

theorem cell23_2480285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_2480285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480285 prefixEnd_2480285 := by exact prefixLift 2480285
  have htrace : WordTrace (prefixWord ++ tailWord_2480285) baseStart_2480285 baseEnd_2480285 := by
    simpa [prefixWord, tailWord_2480285, baseEnd_2480285] using wordTrace_append hprefix tailTrace_2480285
  have hstable : (prefixWord ++ tailWord_2480285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480285).length < 2 ^ (prefixWord ++ tailWord_2480285).sum := by decide
  have hdescent : baseEnd_2480285 < baseStart_2480285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480305 : List Nat := [1, 2, 2, 5, 2, 1, 1, 2, 1, 1, 5]
def baseStart_2480305 : Nat := 118140960795 + 2480305 * 2 ^ 59
def prefixEnd_2480305 : Nat := 4983230072969 + 3 ^ 40 * 2480305 * 2
def baseEnd_2480305 : Nat := 1273588634750023528980791

theorem tailTrace_2480305 : CollatzResearch.WordTrace tailWord_2480305 prefixEnd_2480305 1273588634750023528980791 := by
  unfold tailWord_2480305
  simp only [CollatzResearch.WordTrace]
  refine ⟨90464155279286062214402369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60309436852857374809601579 90464155279286062214402369)
  ·
    refine ⟨67848116459464546660801777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90464155279286062214402369 67848116459464546660801777)
    ·
      refine ⟨50886087344598409995601333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67848116459464546660801777 50886087344598409995601333)
      ·
        refine ⟨4770570688556100937087625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50886087344598409995601333 4770570688556100937087625)
        ·
          refine ⟨3577928016417075702815719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4770570688556100937087625 3577928016417075702815719)
          ·
            refine ⟨5366892024625613554223579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3577928016417075702815719 5366892024625613554223579)
            ·
              refine ⟨8050338036938420331335369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5366892024625613554223579 8050338036938420331335369)
              ·
                refine ⟨6037753527703815248501527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8050338036938420331335369 6037753527703815248501527)
                ·
                  refine ⟨9056630291555722872752291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6037753527703815248501527 9056630291555722872752291)
                  ·
                    refine ⟨13584945437333584309128437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9056630291555722872752291 13584945437333584309128437)
                    ·
                      refine ⟨1273588634750023528980791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13584945437333584309128437 1273588634750023528980791)
                      ·
                        rfl

theorem cell23_2480305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_2480305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480305 prefixEnd_2480305 := by exact prefixLift 2480305
  have htrace : WordTrace (prefixWord ++ tailWord_2480305) baseStart_2480305 baseEnd_2480305 := by
    simpa [prefixWord, tailWord_2480305, baseEnd_2480305] using wordTrace_append hprefix tailTrace_2480305
  have hstable : (prefixWord ++ tailWord_2480305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480305).length < 2 ^ (prefixWord ++ tailWord_2480305).sum := by decide
  have hdescent : baseEnd_2480305 < baseStart_2480305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480331 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 5]
def baseStart_2480331 : Nat := 118140960795 + 2480331 * 2 ^ 59
def prefixEnd_2480331 : Nat := 4983230072969 + 3 ^ 40 * 2480331 * 2
def baseEnd_2480331 : Nat := 1273601985247040427255671

theorem tailTrace_2480331 : CollatzResearch.WordTrace tailWord_2480331 prefixEnd_2480331 1273601985247040427255671 := by
  unfold tailWord_2480331
  simp only [CollatzResearch.WordTrace]
  refine ⟨90465103577191868654848847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60310069051461245769899231 90465103577191868654848847)
  ·
    refine ⟨135697655365787802982273271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90465103577191868654848847 135697655365787802982273271)
    ·
      refine ⟨203546483048681704473409907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135697655365787802982273271 203546483048681704473409907)
      ·
        refine ⟨305319724573022556710114861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203546483048681704473409907 305319724573022556710114861)
        ·
          refine ⟨114494896714883458766293073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 305319724573022556710114861 114494896714883458766293073)
          ·
            refine ⟨85871172536162594074719805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114494896714883458766293073 85871172536162594074719805)
            ·
              refine ⟨32201689701060972778019927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85871172536162594074719805 32201689701060972778019927)
              ·
                refine ⟨48302534551591459167029891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32201689701060972778019927 48302534551591459167029891)
                ·
                  refine ⟨72453801827387188750544837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48302534551591459167029891 72453801827387188750544837)
                  ·
                    refine ⟨13585087842635097890727157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72453801827387188750544837 13585087842635097890727157)
                    ·
                      refine ⟨1273601985247040427255671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13585087842635097890727157 1273601985247040427255671)
                      ·
                        rfl

theorem cell23_2480331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 5].length) (baseStart_2480331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480331 prefixEnd_2480331 := by exact prefixLift 2480331
  have htrace : WordTrace (prefixWord ++ tailWord_2480331) baseStart_2480331 baseEnd_2480331 := by
    simpa [prefixWord, tailWord_2480331, baseEnd_2480331] using wordTrace_append hprefix tailTrace_2480331
  have hstable : (prefixWord ++ tailWord_2480331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480331).length < 2 ^ (prefixWord ++ tailWord_2480331).sum := by decide
  have hdescent : baseEnd_2480331 < baseStart_2480331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480378 : List Nat := [3, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5]
def baseStart_2480378 : Nat := 118140960795 + 2480378 * 2 ^ 59
def prefixEnd_2480378 : Nat := 4983230072969 + 3 ^ 40 * 2480378 * 2
def baseEnd_2480378 : Nat := 1273626118837801743367955

theorem tailTrace_2480378 : CollatzResearch.WordTrace tailWord_2480378 prefixEnd_2480378 1273626118837801743367955 := by
  unfold tailWord_2480378
  simp only [CollatzResearch.WordTrace]
  refine ⟨22616704452005398920452447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60311211872014397121206525 22616704452005398920452447)
  ·
    refine ⟨33925056678008098380678671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22616704452005398920452447 33925056678008098380678671)
    ·
      refine ⟨50887585017012147571018007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33925056678008098380678671 50887585017012147571018007)
      ·
        refine ⟨76331377525518221356527011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50887585017012147571018007 76331377525518221356527011)
        ·
          refine ⟨114497066288277332034790517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76331377525518221356527011 114497066288277332034790517)
          ·
            refine ⟨10734099964525999878261611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114497066288277332034790517 10734099964525999878261611)
            ·
              refine ⟨16101149946788999817392417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10734099964525999878261611 16101149946788999817392417)
              ·
                refine ⟨12075862460091749863044313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16101149946788999817392417 12075862460091749863044313)
                ·
                  refine ⟨9056896845068812397283235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12075862460091749863044313 9056896845068812397283235)
                  ·
                    refine ⟨13585345267603218595924853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9056896845068812397283235 13585345267603218595924853)
                    ·
                      refine ⟨1273626118837801743367955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13585345267603218595924853 1273626118837801743367955)
                      ·
                        rfl

theorem cell23_2480378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_2480378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480378 prefixEnd_2480378 := by exact prefixLift 2480378
  have htrace : WordTrace (prefixWord ++ tailWord_2480378) baseStart_2480378 baseEnd_2480378 := by
    simpa [prefixWord, tailWord_2480378, baseEnd_2480378] using wordTrace_append hprefix tailTrace_2480378
  have hstable : (prefixWord ++ tailWord_2480378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480378).length < 2 ^ (prefixWord ++ tailWord_2480378).sum := by decide
  have hdescent : baseEnd_2480378 < baseStart_2480378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480392 : List Nat := [2, 1, 3, 2, 3, 2, 1, 2, 1, 4, 2]
def baseStart_2480392 : Nat := 118140960795 + 2480392 * 2 ^ 59
def prefixEnd_2480392 : Nat := 4983230072969 + 3 ^ 40 * 2480392 * 2
def baseEnd_2480392 : Nat := 1273633307566964688592891

theorem tailTrace_2480392 : CollatzResearch.WordTrace tailWord_2480392 prefixEnd_2480392 1273633307566964688592891 := by
  unfold tailWord_2480392
  simp only [CollatzResearch.WordTrace]
  refine ⟨45233664214985438036409715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60311552286647250715212953 45233664214985438036409715)
  ·
    refine ⟨67850496322478157054614573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45233664214985438036409715 67850496322478157054614573)
    ·
      refine ⟨25443936120929308895480465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67850496322478157054614573 25443936120929308895480465)
      ·
        refine ⟨19082952090696981671610349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25443936120929308895480465 19082952090696981671610349)
        ·
          refine ⟨7156107034011368126853881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19082952090696981671610349 7156107034011368126853881)
          ·
            refine ⟨5367080275508526095140411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7156107034011368126853881 5367080275508526095140411)
            ·
              refine ⟨8050620413262789142710617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5367080275508526095140411 8050620413262789142710617)
              ·
                refine ⟨6037965309947091857032963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8050620413262789142710617 6037965309947091857032963)
                ·
                  refine ⟨9056947964920637785549445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6037965309947091857032963 9056947964920637785549445)
                  ·
                    refine ⟨1698177743422619584790521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9056947964920637785549445 1698177743422619584790521)
                    ·
                      refine ⟨1273633307566964688592891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1698177743422619584790521 1273633307566964688592891)
                      ·
                        rfl

theorem cell23_2480392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_2480392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480392 prefixEnd_2480392 := by exact prefixLift 2480392
  have htrace : WordTrace (prefixWord ++ tailWord_2480392) baseStart_2480392 baseEnd_2480392 := by
    simpa [prefixWord, tailWord_2480392, baseEnd_2480392] using wordTrace_append hprefix tailTrace_2480392
  have hstable : (prefixWord ++ tailWord_2480392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480392).length < 2 ^ (prefixWord ++ tailWord_2480392).sum := by decide
  have hdescent : baseEnd_2480392 < baseStart_2480392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480428 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 4, 5]
def baseStart_2480428 : Nat := 118140960795 + 2480428 * 2 ^ 59
def prefixEnd_2480428 : Nat := 4983230072969 + 3 ^ 40 * 2480428 * 2
def baseEnd_2480428 : Nat := 424550597623508849247575

theorem tailTrace_2480428 : CollatzResearch.WordTrace tailWord_2480428 prefixEnd_2480428 424550597623508849247575 := by
  unfold tailWord_2480428
  simp only [CollatzResearch.WordTrace]
  refine ⟨45234320728920227110564969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60312427638560302814086625 45234320728920227110564969)
  ·
    refine ⟨33925740546690170332923727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45234320728920227110564969 33925740546690170332923727)
    ·
      refine ⟨50888610820035255499385591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33925740546690170332923727 50888610820035255499385591)
      ·
        refine ⟨76332916230052883249078387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50888610820035255499385591 76332916230052883249078387)
        ·
          refine ⟨114499374345079324873617581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76332916230052883249078387 114499374345079324873617581)
          ·
            refine ⟨42937265379404746827606593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114499374345079324873617581 42937265379404746827606593)
            ·
              refine ⟨32202949034553560120704945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42937265379404746827606593 32202949034553560120704945)
              ·
                refine ⟨24152211775915170090528709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32202949034553560120704945 24152211775915170090528709)
                ·
                  refine ⟨4528539707984094391974133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24152211775915170090528709 4528539707984094391974133)
                  ·
                    refine ⟨424550597623508849247575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4528539707984094391974133 424550597623508849247575)
                    ·
                      rfl

theorem cell23_2480428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 5].length) (baseStart_2480428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480428 prefixEnd_2480428 := by exact prefixLift 2480428
  have htrace : WordTrace (prefixWord ++ tailWord_2480428) baseStart_2480428 baseEnd_2480428 := by
    simpa [prefixWord, tailWord_2480428, baseEnd_2480428] using wordTrace_append hprefix tailTrace_2480428
  have hstable : (prefixWord ++ tailWord_2480428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480428).length < 2 ^ (prefixWord ++ tailWord_2480428).sum := by decide
  have hdescent : baseEnd_2480428 < baseStart_2480428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480435 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 2, 5, 2]
def baseStart_2480435 : Nat := 118140960795 + 2480435 * 2 ^ 59
def prefixEnd_2480435 : Nat := 4983230072969 + 3 ^ 40 * 2480435 * 2
def baseEnd_2480435 : Nat := 1273655387235108020355193

theorem tailTrace_2480435 : CollatzResearch.WordTrace tailWord_2480435 prefixEnd_2480435 1273655387235108020355193 := by
  unfold tailWord_2480435
  simp only [CollatzResearch.WordTrace]
  refine ⟨90468896768815094416634759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60312597845876729611089839 90468896768815094416634759)
  ·
    refine ⟨135703345153222641624952139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90468896768815094416634759 135703345153222641624952139)
    ·
      refine ⟨203555017729833962437428209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135703345153222641624952139 203555017729833962437428209)
      ·
        refine ⟨152666263297375471828071157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203555017729833962437428209 152666263297375471828071157)
        ·
          refine ⟨14312462184128950483881671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152666263297375471828071157 14312462184128950483881671)
          ·
            refine ⟨21468693276193425725822507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14312462184128950483881671 21468693276193425725822507)
            ·
              refine ⟨32203039914290138588733761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21468693276193425725822507 32203039914290138588733761)
              ·
                refine ⟨24152279935717603941550321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32203039914290138588733761 24152279935717603941550321)
                ·
                  refine ⟨18114209951788202956162741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24152279935717603941550321 18114209951788202956162741)
                  ·
                    refine ⟨1698207182980144027140257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18114209951788202956162741 1698207182980144027140257)
                    ·
                      refine ⟨1273655387235108020355193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1698207182980144027140257 1273655387235108020355193)
                      ·
                        rfl

theorem cell23_2480435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 5, 2].length) (baseStart_2480435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480435 prefixEnd_2480435 := by exact prefixLift 2480435
  have htrace : WordTrace (prefixWord ++ tailWord_2480435) baseStart_2480435 baseEnd_2480435 := by
    simpa [prefixWord, tailWord_2480435, baseEnd_2480435] using wordTrace_append hprefix tailTrace_2480435
  have hstable : (prefixWord ++ tailWord_2480435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480435).length < 2 ^ (prefixWord ++ tailWord_2480435).sum := by decide
  have hdescent : baseEnd_2480435 < baseStart_2480435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480449 : List Nat := [1, 2, 5, 2, 2, 1, 2, 3, 5]
def baseStart_2480449 : Nat := 118140960795 + 2480449 * 2 ^ 59
def prefixEnd_2480449 : Nat := 4983230072969 + 3 ^ 40 * 2480449 * 2
def baseEnd_2480449 : Nat := 141518063996030107286681

theorem tailTrace_2480449 : CollatzResearch.WordTrace tailWord_2480449 prefixEnd_2480449 141518063996030107286681 := by
  unfold tailWord_2480449
  simp only [CollatzResearch.WordTrace]
  refine ⟨90469407390764374807644401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60312938260509583205096267 90469407390764374807644401)
  ·
    refine ⟨67852055543073281105733301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90469407390764374807644401 67852055543073281105733301)
    ·
      refine ⟨6361130207163120103662497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67852055543073281105733301 6361130207163120103662497)
      ·
        refine ⟨4770847655372340077746873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6361130207163120103662497 4770847655372340077746873)
        ·
          refine ⟨3578135741529255058310155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4770847655372340077746873 3578135741529255058310155)
          ·
            refine ⟨5367203612293882587465233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3578135741529255058310155 5367203612293882587465233)
            ·
              refine ⟨4025402709220411940598925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5367203612293882587465233 4025402709220411940598925)
              ·
                refine ⟨1509526015957654477724597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4025402709220411940598925 1509526015957654477724597)
                ·
                  refine ⟨141518063996030107286681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1509526015957654477724597 141518063996030107286681)
                  ·
                    rfl

theorem cell23_2480449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3, 5].length) (baseStart_2480449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480449 prefixEnd_2480449 := by exact prefixLift 2480449
  have htrace : WordTrace (prefixWord ++ tailWord_2480449) baseStart_2480449 baseEnd_2480449 := by
    simpa [prefixWord, tailWord_2480449, baseEnd_2480449] using wordTrace_append hprefix tailTrace_2480449
  have hstable : (prefixWord ++ tailWord_2480449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480449).length < 2 ^ (prefixWord ++ tailWord_2480449).sum := by decide
  have hdescent : baseEnd_2480449 < baseStart_2480449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480485 : List Nat := [1, 3, 1, 3, 1, 3, 1, 2, 1, 4, 3]
def baseStart_2480485 : Nat := 118140960795 + 2480485 * 2 ^ 59
def prefixEnd_2480485 : Nat := 4983230072969 + 3 ^ 40 * 2480485 * 2
def baseEnd_2480485 : Nat := 1273681061267832824729963

theorem tailTrace_2480485 : CollatzResearch.WordTrace tailWord_2480485 prefixEnd_2480485 1273681061267832824729963 := by
  unfold tailWord_2480485
  simp only [CollatzResearch.WordTrace]
  refine ⟨90470720418633952955954909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60313813612422635303969939 90470720418633952955954909)
  ·
    refine ⟨33926520156987732358483091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90470720418633952955954909 33926520156987732358483091)
    ·
      refine ⟨50889780235481598537724637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33926520156987732358483091 50889780235481598537724637)
      ·
        refine ⟨19083667588305599451646739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50889780235481598537724637 19083667588305599451646739)
        ·
          refine ⟨28625501382458399177470109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19083667588305599451646739 28625501382458399177470109)
          ·
            refine ⟨10734563018421899691551291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28625501382458399177470109 10734563018421899691551291)
            ·
              refine ⟨16101844527632849537326937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10734563018421899691551291 16101844527632849537326937)
              ·
                refine ⟨12076383395724637152995203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16101844527632849537326937 12076383395724637152995203)
                ·
                  refine ⟨18114575093586955729492805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12076383395724637152995203 18114575093586955729492805)
                  ·
                    refine ⟨3396482830047554199279901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18114575093586955729492805 3396482830047554199279901)
                    ·
                      refine ⟨1273681061267832824729963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3396482830047554199279901 1273681061267832824729963)
                      ·
                        rfl

theorem cell23_2480485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_2480485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480485 prefixEnd_2480485 := by exact prefixLift 2480485
  have htrace : WordTrace (prefixWord ++ tailWord_2480485) baseStart_2480485 baseEnd_2480485 := by
    simpa [prefixWord, tailWord_2480485, baseEnd_2480485] using wordTrace_append hprefix tailTrace_2480485
  have hstable : (prefixWord ++ tailWord_2480485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480485).length < 2 ^ (prefixWord ++ tailWord_2480485).sum := by decide
  have hdescent : baseEnd_2480485 < baseStart_2480485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480508 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 1, 1, 8]
def baseStart_2480508 : Nat := 118140960795 + 2480508 * 2 ^ 59
def prefixEnd_2480508 : Nat := 4983230072969 + 3 ^ 40 * 2480508 * 2
def baseEnd_2480508 : Nat := 1273692871322886234742357

theorem tailTrace_2480508 : CollatzResearch.WordTrace tailWord_2480508 prefixEnd_2480508 1273692871322886234742357 := by
  unfold tailWord_2480508
  simp only [CollatzResearch.WordTrace]
  refine ⟨45235779648775313942021089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60314372865033751922694785 45235779648775313942021089)
  ·
    refine ⟨33926834736581485456515817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45235779648775313942021089 33926834736581485456515817)
    ·
      refine ⟨25445126052436114092386863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33926834736581485456515817 25445126052436114092386863)
      ·
        refine ⟨38167689078654171138580295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25445126052436114092386863 38167689078654171138580295)
        ·
          refine ⟨57251533617981256707870443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38167689078654171138580295 57251533617981256707870443)
          ·
            refine ⟨85877300426971885061805665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57251533617981256707870443 85877300426971885061805665)
            ·
              refine ⟨64407975320228913796354249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85877300426971885061805665 64407975320228913796354249)
              ·
                refine ⟨48305981490171685347265687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64407975320228913796354249 48305981490171685347265687)
                ·
                  refine ⟨72458972235257528020898531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48305981490171685347265687 72458972235257528020898531)
                  ·
                    refine ⟨108688458352886292031347797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72458972235257528020898531 108688458352886292031347797)
                    ·
                      refine ⟨1273692871322886234742357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 108688458352886292031347797 1273692871322886234742357)
                      ·
                        rfl

theorem cell23_2480508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_2480508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480508 prefixEnd_2480508 := by exact prefixLift 2480508
  have htrace : WordTrace (prefixWord ++ tailWord_2480508) baseStart_2480508 baseEnd_2480508 := by
    simpa [prefixWord, tailWord_2480508, baseEnd_2480508] using wordTrace_append hprefix tailTrace_2480508
  have hstable : (prefixWord ++ tailWord_2480508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480508).length < 2 ^ (prefixWord ++ tailWord_2480508).sum := by decide
  have hdescent : baseEnd_2480508 < baseStart_2480508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480509 : List Nat := [1, 4, 1, 1, 2, 3, 3, 3, 1, 4]
def baseStart_2480509 : Nat := 118140960795 + 2480509 * 2 ^ 59
def prefixEnd_2480509 : Nat := 4983230072969 + 3 ^ 40 * 2480509 * 2
def baseEnd_2480509 : Nat := 424564461601180243609951

theorem tailTrace_2480509 : CollatzResearch.WordTrace tailWord_2480509 prefixEnd_2480509 424564461601180243609951 := by
  unfold tailWord_2480509
  simp only [CollatzResearch.WordTrace]
  refine ⟨90471595770547005054828581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60314397180364670036552387 90471595770547005054828581)
  ·
    refine ⟨16963424206977563447780359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90471595770547005054828581 16963424206977563447780359)
    ·
      refine ⟨25445136310466345171670539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16963424206977563447780359 25445136310466345171670539)
      ·
        refine ⟨38167704465699517757505809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25445136310466345171670539 38167704465699517757505809)
        ·
          refine ⟨28625778349274638318129357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38167704465699517757505809 28625778349274638318129357)
          ·
            refine ⟨10734666880977989369298509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28625778349274638318129357 10734666880977989369298509)
            ·
              refine ⟨4025500080366746013486941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10734666880977989369298509 4025500080366746013486941)
              ·
                refine ⟨1509562530137529755057603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4025500080366746013486941 1509562530137529755057603)
                ·
                  refine ⟨2264343795206294632586405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1509562530137529755057603 2264343795206294632586405)
                  ·
                    refine ⟨424564461601180243609951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2264343795206294632586405 424564461601180243609951)
                    ·
                      rfl

theorem cell23_2480509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_2480509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480509 prefixEnd_2480509 := by exact prefixLift 2480509
  have htrace : WordTrace (prefixWord ++ tailWord_2480509) baseStart_2480509 baseEnd_2480509 := by
    simpa [prefixWord, tailWord_2480509, baseEnd_2480509] using wordTrace_append hprefix tailTrace_2480509
  have hstable : (prefixWord ++ tailWord_2480509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480509).length < 2 ^ (prefixWord ++ tailWord_2480509).sum := by decide
  have hdescent : baseEnd_2480509 < baseStart_2480509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480528 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 5]
def baseStart_2480528 : Nat := 118140960795 + 2480528 * 2 ^ 59
def prefixEnd_2480528 : Nat := 4983230072969 + 3 ^ 40 * 2480528 * 2
def baseEnd_2480528 : Nat := 1273703140935976156492265

theorem tailTrace_2480528 : CollatzResearch.WordTrace tailWord_2480528 prefixEnd_2480528 1273703140935976156492265 := by
  unfold tailWord_2480528
  simp only [CollatzResearch.WordTrace]
  refine ⟨45236144378739085649885119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60314859171652114199846825 45236144378739085649885119)
  ·
    refine ⟨67854216568108628474827679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45236144378739085649885119 67854216568108628474827679)
    ·
      refine ⟨101781324852162942712241519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67854216568108628474827679 101781324852162942712241519)
      ·
        refine ⟨152671987278244414068362279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101781324852162942712241519 152671987278244414068362279)
        ·
          refine ⟨229007980917366621102543419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152671987278244414068362279 229007980917366621102543419)
          ·
            refine ⟨343511971376049931653815129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229007980917366621102543419 343511971376049931653815129)
            ·
              refine ⟨257633978532037448740361347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 343511971376049931653815129 257633978532037448740361347)
              ·
                refine ⟨386450967798056173110542021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257633978532037448740361347 386450967798056173110542021)
                ·
                  refine ⟨72459556462135532458226629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 386450967798056173110542021 72459556462135532458226629)
                  ·
                    refine ⟨13586166836650412335917493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72459556462135532458226629 13586166836650412335917493)
                    ·
                      refine ⟨1273703140935976156492265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13586166836650412335917493 1273703140935976156492265)
                      ·
                        rfl

theorem cell23_2480528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 5].length) (baseStart_2480528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480528 prefixEnd_2480528 := by exact prefixLift 2480528
  have htrace : WordTrace (prefixWord ++ tailWord_2480528) baseStart_2480528 baseEnd_2480528 := by
    simpa [prefixWord, tailWord_2480528, baseEnd_2480528] using wordTrace_append hprefix tailTrace_2480528
  have hstable : (prefixWord ++ tailWord_2480528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480528).length < 2 ^ (prefixWord ++ tailWord_2480528).sum := by decide
  have hdescent : baseEnd_2480528 < baseStart_2480528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480569 : List Nat := [1, 2, 1, 4, 3, 2, 3, 1, 1, 5]
def baseStart_2480569 : Nat := 118140960795 + 2480569 * 2 ^ 59
def prefixEnd_2480569 : Nat := 4983230072969 + 3 ^ 40 * 2480569 * 2
def baseEnd_2480569 : Nat := 424574731214270165359859

theorem tailTrace_2480569 : CollatzResearch.WordTrace tailWord_2480569 prefixEnd_2480569 424574731214270165359859 := by
  unfold tailWord_2480569
  simp only [CollatzResearch.WordTrace]
  refine ⟨90473784150329635302012761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60315856100219756868008507 90473784150329635302012761)
  ·
    refine ⟨67855338112747226476509571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90473784150329635302012761 67855338112747226476509571)
    ·
      refine ⟨101783007169120839714764357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67855338112747226476509571 101783007169120839714764357)
      ·
        refine ⟨19084313844210157446518317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101783007169120839714764357 19084313844210157446518317)
        ·
          refine ⟨7156617691578809042444369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19084313844210157446518317 7156617691578809042444369)
          ·
            refine ⟨5367463268684106781833277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7156617691578809042444369 5367463268684106781833277)
            ·
              refine ⟨2012798725756540043187479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5367463268684106781833277 2012798725756540043187479)
              ·
                refine ⟨3019198088634810064781219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2012798725756540043187479 3019198088634810064781219)
                ·
                  refine ⟨4528797132952215097171829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3019198088634810064781219 4528797132952215097171829)
                  ·
                    refine ⟨424574731214270165359859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4528797132952215097171829 424574731214270165359859)
                    ·
                      rfl

theorem cell23_2480569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 1, 5].length) (baseStart_2480569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480569 prefixEnd_2480569 := by exact prefixLift 2480569
  have htrace : WordTrace (prefixWord ++ tailWord_2480569) baseStart_2480569 baseEnd_2480569 := by
    simpa [prefixWord, tailWord_2480569, baseEnd_2480569] using wordTrace_append hprefix tailTrace_2480569
  have hstable : (prefixWord ++ tailWord_2480569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480569).length < 2 ^ (prefixWord ++ tailWord_2480569).sum := by decide
  have hdescent : baseEnd_2480569 < baseStart_2480569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480577 : List Nat := [1, 2, 7, 1, 1, 2, 2, 2, 1, 4]
def baseStart_2480577 : Nat := 118140960795 + 2480577 * 2 ^ 59
def prefixEnd_2480577 : Nat := 4983230072969 + 3 ^ 40 * 2480577 * 2
def baseEnd_2480577 : Nat := 424576100496015488259847

theorem tailTrace_2480577 : CollatzResearch.WordTrace tailWord_2480577 prefixEnd_2480577 424576100496015488259847 := by
  unfold tailWord_2480577
  simp only [CollatzResearch.WordTrace]
  refine ⟨90474075934300652668303985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60316050622867101778869323 90474075934300652668303985)
  ·
    refine ⟨67855556950725489501227989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90474075934300652668303985 67855556950725489501227989)
    ·
      refine ⟨1590364616032628660185031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 67855556950725489501227989 1590364616032628660185031)
      ·
        refine ⟨2385546924048942990277547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1590364616032628660185031 2385546924048942990277547)
        ·
          refine ⟨3578320386073414485416321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2385546924048942990277547 3578320386073414485416321)
          ·
            refine ⟨2683740289555060864062241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3578320386073414485416321 2683740289555060864062241)
            ·
              refine ⟨2012805217166295648046681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2683740289555060864062241 2012805217166295648046681)
              ·
                refine ⟨1509603912874721736035011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2012805217166295648046681 1509603912874721736035011)
                ·
                  refine ⟨2264405869312082604052517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1509603912874721736035011 2264405869312082604052517)
                  ·
                    refine ⟨424576100496015488259847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2264405869312082604052517 424576100496015488259847)
                    ·
                      rfl

theorem cell23_2480577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_2480577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480577 prefixEnd_2480577 := by exact prefixLift 2480577
  have htrace : WordTrace (prefixWord ++ tailWord_2480577) baseStart_2480577 baseEnd_2480577 := by
    simpa [prefixWord, tailWord_2480577, baseEnd_2480577] using wordTrace_append hprefix tailTrace_2480577
  have hstable : (prefixWord ++ tailWord_2480577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480577).length < 2 ^ (prefixWord ++ tailWord_2480577).sum := by decide
  have hdescent : baseEnd_2480577 < baseStart_2480577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480583 : List Nat := [1, 1, 4, 1, 1, 6, 2, 2, 1, 1, 3]
def baseStart_2480583 : Nat := 118140960795 + 2480583 * 2 ^ 59
def prefixEnd_2480583 : Nat := 4983230072969 + 3 ^ 40 * 2480583 * 2
def baseEnd_2480583 : Nat := 1273731382371973441304513

theorem tailTrace_2480583 : CollatzResearch.WordTrace tailWord_2480583 prefixEnd_2480583 1273731382371973441304513 := by
  unfold tailWord_2480583
  simp only [CollatzResearch.WordTrace]
  refine ⟨90474294772278915693022403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60316196514852610462014935 90474294772278915693022403)
  ·
    refine ⟨135711442158418373539533605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90474294772278915693022403 135711442158418373539533605)
    ·
      refine ⟨25445895404703445038662551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135711442158418373539533605 25445895404703445038662551)
      ·
        refine ⟨38168843107055167557993827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25445895404703445038662551 38168843107055167557993827)
        ·
          refine ⟨57253264660582751336990741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38168843107055167557993827 57253264660582751336990741)
          ·
            refine ⟨2683746780964816468921441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57253264660582751336990741 2683746780964816468921441)
            ·
              refine ⟨2012810085723612351691081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2683746780964816468921441 2012810085723612351691081)
              ·
                refine ⟨1509607564292709263768311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2012810085723612351691081 1509607564292709263768311)
                ·
                  refine ⟨2264411346439063895652467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1509607564292709263768311 2264411346439063895652467)
                  ·
                    refine ⟨3396617019658595843478701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2264411346439063895652467 3396617019658595843478701)
                    ·
                      refine ⟨1273731382371973441304513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3396617019658595843478701 1273731382371973441304513)
                      ·
                        rfl

theorem cell23_2480583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2, 1, 1, 3].length) (baseStart_2480583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480583 prefixEnd_2480583 := by exact prefixLift 2480583
  have htrace : WordTrace (prefixWord ++ tailWord_2480583) baseStart_2480583 baseEnd_2480583 := by
    simpa [prefixWord, tailWord_2480583, baseEnd_2480583] using wordTrace_append hprefix tailTrace_2480583
  have hstable : (prefixWord ++ tailWord_2480583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480583).length < 2 ^ (prefixWord ++ tailWord_2480583).sum := by decide
  have hdescent : baseEnd_2480583 < baseStart_2480583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480602 : List Nat := [3, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4]
def baseStart_2480602 : Nat := 118140960795 + 2480602 * 2 ^ 59
def prefixEnd_2480602 : Nat := 4983230072969 + 3 ^ 40 * 2480602 * 2
def baseEnd_2480602 : Nat := 1273741138504408866966925

theorem tailTrace_2480602 : CollatzResearch.WordTrace tailWord_2480602 prefixEnd_2480602 1273741138504408866966925 := by
  unfold tailWord_2480602
  simp only [CollatzResearch.WordTrace]
  refine ⟨22618746939802520484491015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60316658506140054625309373 22618746939802520484491015)
  ·
    refine ⟨33928120409703780726736523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22618746939802520484491015 33928120409703780726736523)
    ·
      refine ⟨50892180614555671090104785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33928120409703780726736523 50892180614555671090104785)
      ·
        refine ⟨38169135460916753317578589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50892180614555671090104785 38169135460916753317578589)
        ·
          refine ⟨14313425797843782494091971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38169135460916753317578589 14313425797843782494091971)
          ·
            refine ⟨21470138696765673741137957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14313425797843782494091971 21470138696765673741137957)
            ·
              refine ⟨4025651005643563826463367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21470138696765673741137957 4025651005643563826463367)
              ·
                refine ⟨6038476508465345739695051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4025651005643563826463367 6038476508465345739695051)
                ·
                  refine ⟨9057714762698018609542577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6038476508465345739695051 9057714762698018609542577)
                  ·
                    refine ⟨6793286072023513957156933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9057714762698018609542577 6793286072023513957156933)
                    ·
                      refine ⟨1273741138504408866966925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6793286072023513957156933 1273741138504408866966925)
                      ·
                        rfl

theorem cell23_2480602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_2480602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480602 prefixEnd_2480602 := by exact prefixLift 2480602
  have htrace : WordTrace (prefixWord ++ tailWord_2480602) baseStart_2480602 baseEnd_2480602 := by
    simpa [prefixWord, tailWord_2480602, baseEnd_2480602] using wordTrace_append hprefix tailTrace_2480602
  have hstable : (prefixWord ++ tailWord_2480602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480602).length < 2 ^ (prefixWord ++ tailWord_2480602).sum := by decide
  have hdescent : baseEnd_2480602 < baseStart_2480602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480610 : List Nat := [3, 3, 3, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_2480610 : Nat := 118140960795 + 2480610 * 2 ^ 59
def prefixEnd_2480610 : Nat := 4983230072969 + 3 ^ 40 * 2480610 * 2
def baseEnd_2480610 : Nat := 1273745246349644835666889

theorem tailTrace_2480610 : CollatzResearch.WordTrace tailWord_2480610 prefixEnd_2480610 1273745246349644835666889 := by
  unfold tailWord_2480610
  simp only [CollatzResearch.WordTrace]
  refine ⟨22618819885795274826063821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60316853028787399536170189 22618819885795274826063821)
  ·
    refine ⟨8482057457173228059773933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22618819885795274826063821 8482057457173228059773933)
    ·
      refine ⟨3180771546439960522415225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8482057457173228059773933 3180771546439960522415225)
      ·
        refine ⟨2385578659829970391811419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3180771546439960522415225 2385578659829970391811419)
        ·
          refine ⟨3578367989744955587717129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2385578659829970391811419 3578367989744955587717129)
          ·
            refine ⟨2683775992308716690787847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3578367989744955587717129 2683775992308716690787847)
            ·
              refine ⟨4025663988463075036181771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2683775992308716690787847 4025663988463075036181771)
              ·
                refine ⟨6038495982694612554272657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4025663988463075036181771 6038495982694612554272657)
                ·
                  refine ⟨4528871987020959415704493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6038495982694612554272657 4528871987020959415704493)
                  ·
                    refine ⟨1698326995132859780889185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4528871987020959415704493 1698326995132859780889185)
                    ·
                      refine ⟨1273745246349644835666889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1698326995132859780889185 1273745246349644835666889)
                      ·
                        rfl

theorem cell23_2480610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_2480610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480610 prefixEnd_2480610 := by exact prefixLift 2480610
  have htrace : WordTrace (prefixWord ++ tailWord_2480610) baseStart_2480610 baseEnd_2480610 := by
    simpa [prefixWord, tailWord_2480610, baseEnd_2480610] using wordTrace_append hprefix tailTrace_2480610
  have hstable : (prefixWord ++ tailWord_2480610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480610).length < 2 ^ (prefixWord ++ tailWord_2480610).sum := by decide
  have hdescent : baseEnd_2480610 < baseStart_2480610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480626 : List Nat := [3, 2, 1, 4, 2, 1, 1, 3, 1, 2, 3]
def baseStart_2480626 : Nat := 118140960795 + 2480626 * 2 ^ 59
def prefixEnd_2480626 : Nat := 4983230072969 + 3 ^ 40 * 2480626 * 2
def baseEnd_2480626 : Nat := 1273753462040116773066815

theorem tailTrace_2480626 : CollatzResearch.WordTrace tailWord_2480626 prefixEnd_2480626 1273753462040116773066815 := by
  unfold tailWord_2480626
  simp only [CollatzResearch.WordTrace]
  refine ⟨22618965777780783509209433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60317242074082089357891821 22618965777780783509209433)
  ·
    refine ⟨16964224333335587631907075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22618965777780783509209433 16964224333335587631907075)
    ·
      refine ⟨25446336500003381447860613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16964224333335587631907075 25446336500003381447860613)
      ·
        refine ⟨4771188093750634021473865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25446336500003381447860613 4771188093750634021473865)
        ·
          refine ⟨3578391070312975516105399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4771188093750634021473865 3578391070312975516105399)
          ·
            refine ⟨5367586605469463274158099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3578391070312975516105399 5367586605469463274158099)
            ·
              refine ⟨8051379908204194911237149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5367586605469463274158099 8051379908204194911237149)
              ·
                refine ⟨3019267465576573091713931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8051379908204194911237149 3019267465576573091713931)
                ·
                  refine ⟨4528901198364859637570897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3019267465576573091713931 4528901198364859637570897)
                  ·
                    refine ⟨3396675898773644728178173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4528901198364859637570897 3396675898773644728178173)
                    ·
                      refine ⟨1273753462040116773066815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3396675898773644728178173 1273753462040116773066815)
                      ·
                        rfl

theorem cell23_2480626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_2480626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480626 prefixEnd_2480626 := by exact prefixLift 2480626
  have htrace : WordTrace (prefixWord ++ tailWord_2480626) baseStart_2480626 baseEnd_2480626 := by
    simpa [prefixWord, tailWord_2480626, baseEnd_2480626] using wordTrace_append hprefix tailTrace_2480626
  have hstable : (prefixWord ++ tailWord_2480626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480626).length < 2 ^ (prefixWord ++ tailWord_2480626).sum := by decide
  have hdescent : baseEnd_2480626 < baseStart_2480626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480645 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 1, 5, 4]
def baseStart_2480645 : Nat := 118140960795 + 2480645 * 2 ^ 59
def prefixEnd_2480645 : Nat := 4983230072969 + 3 ^ 40 * 2480645 * 2
def baseEnd_2480645 : Nat := 1273763218172552198729227

theorem tailTrace_2480645 : CollatzResearch.WordTrace tailWord_2480645 prefixEnd_2480645 1273763218172552198729227 := by
  unfold tailWord_2480645
  simp only [CollatzResearch.WordTrace]
  refine ⟨90476556098054300281779389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60317704065369533521186259 90476556098054300281779389)
  ·
    refine ⟨33928708536770362605667271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90476556098054300281779389 33928708536770362605667271)
    ·
      refine ⟨50893062805155543908500907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33928708536770362605667271 50893062805155543908500907)
      ·
        refine ⟨76339594207733315862751361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50893062805155543908500907 76339594207733315862751361)
        ·
          refine ⟨57254695655799986897063521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76339594207733315862751361 57254695655799986897063521)
          ·
            refine ⟨42941021741849990172797641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57254695655799986897063521 42941021741849990172797641)
            ·
              refine ⟨32205766306387492629598231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42941021741849990172797641 32205766306387492629598231)
              ·
                refine ⟨48308649459581238944397347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32205766306387492629598231 48308649459581238944397347)
                ·
                  refine ⟨72462974189371858416596021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48308649459581238944397347 72462974189371858416596021)
                  ·
                    refine ⟨6793403830253611726555877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72462974189371858416596021 6793403830253611726555877)
                    ·
                      refine ⟨1273763218172552198729227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6793403830253611726555877 1273763218172552198729227)
                      ·
                        rfl

theorem cell23_2480645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_2480645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480645 prefixEnd_2480645 := by exact prefixLift 2480645
  have htrace : WordTrace (prefixWord ++ tailWord_2480645) baseStart_2480645 baseEnd_2480645 := by
    simpa [prefixWord, tailWord_2480645, baseEnd_2480645] using wordTrace_append hprefix tailTrace_2480645
  have hstable : (prefixWord ++ tailWord_2480645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480645).length < 2 ^ (prefixWord ++ tailWord_2480645).sum := by decide
  have hdescent : baseEnd_2480645 < baseStart_2480645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480653 : List Nat := [1, 7, 1, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_2480653 : Nat := 118140960795 + 2480653 * 2 ^ 59
def prefixEnd_2480653 : Nat := 4983230072969 + 3 ^ 40 * 2480653 * 2
def baseEnd_2480653 : Nat := 1273767326017788167429191

theorem tailTrace_2480653 : CollatzResearch.WordTrace tailWord_2480653 prefixEnd_2480653 1273767326017788167429191 := by
  unfold tailWord_2480653
  simp only [CollatzResearch.WordTrace]
  refine ⟨90476847882025317648070613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60317898588016878432047075 90476847882025317648070613)
  ·
    refine ⟨2120551122234968382376655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 90476847882025317648070613 2120551122234968382376655)
    ·
      refine ⟨3180826683352452573564983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2120551122234968382376655 3180826683352452573564983)
      ·
        refine ⟨4771240025028678860347475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3180826683352452573564983 4771240025028678860347475)
        ·
          refine ⟨7156860037543018290521213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4771240025028678860347475 7156860037543018290521213)
          ·
            refine ⟨2683822514078631858945455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7156860037543018290521213 2683822514078631858945455)
            ·
              refine ⟨4025733771117947788418183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2683822514078631858945455 4025733771117947788418183)
              ·
                refine ⟨6038600656676921682627275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4025733771117947788418183 6038600656676921682627275)
                ·
                  refine ⟨9057900985015382523940913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6038600656676921682627275 9057900985015382523940913)
                  ·
                    refine ⟨6793425738761536892955685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9057900985015382523940913 6793425738761536892955685)
                    ·
                      refine ⟨1273767326017788167429191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6793425738761536892955685 1273767326017788167429191)
                      ·
                        rfl

theorem cell23_2480653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_2480653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480653 prefixEnd_2480653 := by exact prefixLift 2480653
  have htrace : WordTrace (prefixWord ++ tailWord_2480653) baseStart_2480653 baseEnd_2480653 := by
    simpa [prefixWord, tailWord_2480653, baseEnd_2480653] using wordTrace_append hprefix tailTrace_2480653
  have hstable : (prefixWord ++ tailWord_2480653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480653).length < 2 ^ (prefixWord ++ tailWord_2480653).sum := by decide
  have hdescent : baseEnd_2480653 < baseStart_2480653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480665 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 4, 1, 5]
def baseStart_2480665 : Nat := 118140960795 + 2480665 * 2 ^ 59
def prefixEnd_2480665 : Nat := 4983230072969 + 3 ^ 40 * 2480665 * 2
def baseEnd_2480665 : Nat := 1273773487785642120479135

theorem tailTrace_2480665 : CollatzResearch.WordTrace tailWord_2480665 prefixEnd_2480665 1273773487785642120479135 := by
  unfold tailWord_2480665
  simp only [CollatzResearch.WordTrace]
  refine ⟨90477285557981843697507449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60318190371987895798338299 90477285557981843697507449)
  ·
    refine ⟨67857964168486382773130587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90477285557981843697507449 67857964168486382773130587)
    ·
      refine ⟨101786946252729574159695881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67857964168486382773130587 101786946252729574159695881)
      ·
        refine ⟨76340209689547180619771911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101786946252729574159695881 76340209689547180619771911)
        ·
          refine ⟨114510314534320770929657867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76340209689547180619771911 114510314534320770929657867)
          ·
            refine ⟨171765471801481156394486801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114510314534320770929657867 171765471801481156394486801)
            ·
              refine ⟨128824103851110867295865101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171765471801481156394486801 128824103851110867295865101)
              ·
                refine ⟨48309038944166575235949413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128824103851110867295865101 48309038944166575235949413)
                ·
                  refine ⟨9057944802031232856740515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48309038944166575235949413 9057944802031232856740515)
                  ·
                    refine ⟨13586917203046849285110773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9057944802031232856740515 13586917203046849285110773)
                    ·
                      refine ⟨1273773487785642120479135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13586917203046849285110773 1273773487785642120479135)
                      ·
                        rfl

theorem cell23_2480665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_2480665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480665 prefixEnd_2480665 := by exact prefixLift 2480665
  have htrace : WordTrace (prefixWord ++ tailWord_2480665) baseStart_2480665 baseEnd_2480665 := by
    simpa [prefixWord, tailWord_2480665, baseEnd_2480665] using wordTrace_append hprefix tailTrace_2480665
  have hstable : (prefixWord ++ tailWord_2480665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480665).length < 2 ^ (prefixWord ++ tailWord_2480665).sum := by decide
  have hdescent : baseEnd_2480665 < baseStart_2480665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480682 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_2480682 : Nat := 118140960795 + 2480682 * 2 ^ 59
def prefixEnd_2480682 : Nat := 4983230072969 + 3 ^ 40 * 2480682 * 2
def baseEnd_2480682 : Nat := 1273782216956768553966557

theorem tailTrace_2480682 : CollatzResearch.WordTrace tailWord_2480682 prefixEnd_2480682 1273782216956768553966557 := by
  unfold tailWord_2480682
  simp only [CollatzResearch.WordTrace]
  refine ⟨22619476399730063900219075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60318603732613503733917533 22619476399730063900219075)
  ·
    refine ⟨33929214599595095850328613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22619476399730063900219075 33929214599595095850328613)
    ·
      refine ⟨6361727737424080471936615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33929214599595095850328613 6361727737424080471936615)
      ·
        refine ⟨9542591606136120707904923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6361727737424080471936615 9542591606136120707904923)
        ·
          refine ⟨14313887409204181061857385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9542591606136120707904923 14313887409204181061857385)
          ·
            refine ⟨10735415556903135796393039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14313887409204181061857385 10735415556903135796393039)
            ·
              refine ⟨16103123335354703694589559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10735415556903135796393039 16103123335354703694589559)
              ·
                refine ⟨24154685003032055541884339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16103123335354703694589559 24154685003032055541884339)
                ·
                  refine ⟨36232027504548083312826509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24154685003032055541884339 36232027504548083312826509)
                  ·
                    refine ⟨13587010314205531242309941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36232027504548083312826509 13587010314205531242309941)
                    ·
                      refine ⟨1273782216956768553966557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13587010314205531242309941 1273782216956768553966557)
                      ·
                        rfl

theorem cell23_2480682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_2480682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480682 prefixEnd_2480682 := by exact prefixLift 2480682
  have htrace : WordTrace (prefixWord ++ tailWord_2480682) baseStart_2480682 baseEnd_2480682 := by
    simpa [prefixWord, tailWord_2480682, baseEnd_2480682] using wordTrace_append hprefix tailTrace_2480682
  have hstable : (prefixWord ++ tailWord_2480682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480682).length < 2 ^ (prefixWord ++ tailWord_2480682).sum := by decide
  have hdescent : baseEnd_2480682 < baseStart_2480682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480695 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 7]
def baseStart_2480695 : Nat := 118140960795 + 2480695 * 2 ^ 59
def prefixEnd_2480695 : Nat := 4983230072969 + 3 ^ 40 * 2480695 * 2
def baseEnd_2480695 : Nat := 1273788892205277003103997

theorem tailTrace_2480695 : CollatzResearch.WordTrace tailWord_2480695 prefixEnd_2480695 1273788892205277003103997 := by
  unfold tailWord_2480695
  simp only [CollatzResearch.WordTrace]
  refine ⟨90478379747873158821099539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60318919831915439214066359 90478379747873158821099539)
  ·
    refine ⟨135717569621809738231649309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90478379747873158821099539 135717569621809738231649309)
    ·
      refine ⟨50894088608178651836868491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135717569621809738231649309 50894088608178651836868491)
      ·
        refine ⟨76341132912267977755302737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50894088608178651836868491 76341132912267977755302737)
        ·
          refine ⟨57255849684200983316477053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76341132912267977755302737 57255849684200983316477053)
          ·
            refine ⟨21470943631575368743678895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57255849684200983316477053 21470943631575368743678895)
            ·
              refine ⟨32206415447363053115518343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21470943631575368743678895 32206415447363053115518343)
              ·
                refine ⟨48309623171044579673277515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32206415447363053115518343 48309623171044579673277515)
                ·
                  refine ⟨72464434756566869509916273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48309623171044579673277515 72464434756566869509916273)
                  ·
                    refine ⟨54348326067425152132437205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72464434756566869509916273 54348326067425152132437205)
                    ·
                      refine ⟨1273788892205277003103997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54348326067425152132437205 1273788892205277003103997)
                      ·
                        rfl

theorem cell23_2480695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_2480695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480695 prefixEnd_2480695 := by exact prefixLift 2480695
  have htrace : WordTrace (prefixWord ++ tailWord_2480695) baseStart_2480695 baseEnd_2480695 := by
    simpa [prefixWord, tailWord_2480695, baseEnd_2480695] using wordTrace_append hprefix tailTrace_2480695
  have hstable : (prefixWord ++ tailWord_2480695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480695).length < 2 ^ (prefixWord ++ tailWord_2480695).sum := by decide
  have hdescent : baseEnd_2480695 < baseStart_2480695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480696 : List Nat := [2, 1, 2, 1, 4, 1, 2, 4, 2, 2, 2]
def baseStart_2480696 : Nat := 118140960795 + 2480696 * 2 ^ 59
def prefixEnd_2480696 : Nat := 4983230072969 + 3 ^ 40 * 2480696 * 2
def baseEnd_2480696 : Nat := 1273789405685931499191493

theorem tailTrace_2480696 : CollatzResearch.WordTrace tailWord_2480696 prefixEnd_2480696 1273789405685931499191493 := by
  unfold tailWord_2480696
  simp only [CollatzResearch.WordTrace]
  refine ⟨45239208110434767995942971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60318944147246357327923961 45239208110434767995942971)
  ·
    refine ⟨67858812165652151993914457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45239208110434767995942971 67858812165652151993914457)
    ·
      refine ⟨50894109124239113995435843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67858812165652151993914457 50894109124239113995435843)
      ·
        refine ⟨76341163686358670993153765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50894109124239113995435843 76341163686358670993153765)
        ·
          refine ⟨14313968191192250811216331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76341163686358670993153765 14313968191192250811216331)
          ·
            refine ⟨21470952286788376216824497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14313968191192250811216331 21470952286788376216824497)
            ·
              refine ⟨16103214215091282162618373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21470952286788376216824497 16103214215091282162618373)
              ·
                refine ⟨3019352665329615405490945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16103214215091282162618373 3019352665329615405490945)
                ·
                  refine ⟨2264514498997211554118209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3019352665329615405490945 2264514498997211554118209)
                  ·
                    refine ⟨1698385874247908665588657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2264514498997211554118209 1698385874247908665588657)
                    ·
                      refine ⟨1273789405685931499191493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1698385874247908665588657 1273789405685931499191493)
                      ·
                        rfl

theorem cell23_2480696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 2, 2, 2].length) (baseStart_2480696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480696 prefixEnd_2480696 := by exact prefixLift 2480696
  have htrace : WordTrace (prefixWord ++ tailWord_2480696) baseStart_2480696 baseEnd_2480696 := by
    simpa [prefixWord, tailWord_2480696, baseEnd_2480696] using wordTrace_append hprefix tailTrace_2480696
  have hstable : (prefixWord ++ tailWord_2480696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480696).length < 2 ^ (prefixWord ++ tailWord_2480696).sum := by decide
  have hdescent : baseEnd_2480696 < baseStart_2480696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480712 : List Nat := [2, 1, 3, 1, 1, 1, 1, 5, 2, 3, 3]
def baseStart_2480712 : Nat := 118140960795 + 2480712 * 2 ^ 59
def prefixEnd_2480712 : Nat := 4983230072969 + 3 ^ 40 * 2480712 * 2
def baseEnd_2480712 : Nat := 1273797621376403436591419

theorem tailTrace_2480712 : CollatzResearch.WordTrace tailWord_2480712 prefixEnd_2480712 1273797621376403436591419 := by
  unfold tailWord_2480712
  simp only [CollatzResearch.WordTrace]
  refine ⟨45239499894405785362234195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60319333192541047149645593 45239499894405785362234195)
  ·
    refine ⟨67859249841608678043351293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45239499894405785362234195 67859249841608678043351293)
    ·
      refine ⟨25447218690603254266256735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67859249841608678043351293 25447218690603254266256735)
      ·
        refine ⟨38170828035904881399385103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25447218690603254266256735 38170828035904881399385103)
        ·
          refine ⟨57256242053857322099077655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38170828035904881399385103 57256242053857322099077655)
          ·
            refine ⟨85884363080785983148616483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57256242053857322099077655 85884363080785983148616483)
            ·
              refine ⟨128826544621178974722924725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85884363080785983148616483 128826544621178974722924725)
              ·
                refine ⟨12077488558235528880274193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 128826544621178974722924725 12077488558235528880274193)
                ·
                  refine ⟨9058116418676646660205645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12077488558235528880274193 9058116418676646660205645)
                  ·
                    refine ⟨3396793657003742497577117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9058116418676646660205645 3396793657003742497577117)
                    ·
                      refine ⟨1273797621376403436591419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3396793657003742497577117 1273797621376403436591419)
                      ·
                        rfl

theorem cell23_2480712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_2480712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480712 prefixEnd_2480712 := by exact prefixLift 2480712
  have htrace : WordTrace (prefixWord ++ tailWord_2480712) baseStart_2480712 baseEnd_2480712 := by
    simpa [prefixWord, tailWord_2480712, baseEnd_2480712] using wordTrace_append hprefix tailTrace_2480712
  have hstable : (prefixWord ++ tailWord_2480712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480712).length < 2 ^ (prefixWord ++ tailWord_2480712).sum := by decide
  have hdescent : baseEnd_2480712 < baseStart_2480712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480715 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 3, 7]
def baseStart_2480715 : Nat := 118140960795 + 2480715 * 2 ^ 59
def prefixEnd_2480715 : Nat := 4983230072969 + 3 ^ 40 * 2480715 * 2
def baseEnd_2480715 : Nat := 424599720606122308284635

theorem tailTrace_2480715 : CollatzResearch.WordTrace tailWord_2480715 prefixEnd_2480715 424599720606122308284635 := by
  unfold tailWord_2480715
  simp only [CollatzResearch.WordTrace]
  refine ⟨90479109207800702236827599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60319406138533801491218399 90479109207800702236827599)
  ·
    refine ⟨135718663811701053355241399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90479109207800702236827599 135718663811701053355241399)
    ·
      refine ⟨203577995717551580032862099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135718663811701053355241399 203577995717551580032862099)
      ·
        refine ⟨305366993576327370049293149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203577995717551580032862099 305366993576327370049293149)
        ·
          refine ⟨114512622591122763768484931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 305366993576327370049293149 114512622591122763768484931)
          ·
            refine ⟨171768933886684145652727397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114512622591122763768484931 171768933886684145652727397)
            ·
              refine ⟨32206675103753277309886387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 171768933886684145652727397 32206675103753277309886387)
              ·
                refine ⟨48310012655629915964829581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32206675103753277309886387 48310012655629915964829581)
                ·
                  refine ⟨18116254745861218486811093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48310012655629915964829581 18116254745861218486811093)
                  ·
                    refine ⟨424599720606122308284635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18116254745861218486811093 424599720606122308284635)
                    ·
                      rfl

theorem cell23_2480715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 7].length) (baseStart_2480715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480715 prefixEnd_2480715 := by exact prefixLift 2480715
  have htrace : WordTrace (prefixWord ++ tailWord_2480715) baseStart_2480715 baseEnd_2480715 := by
    simpa [prefixWord, tailWord_2480715, baseEnd_2480715] using wordTrace_append hprefix tailTrace_2480715
  have hstable : (prefixWord ++ tailWord_2480715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480715).length < 2 ^ (prefixWord ++ tailWord_2480715).sum := by decide
  have hdescent : baseEnd_2480715 < baseStart_2480715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480734 : List Nat := [4, 4, 1, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_2480734 : Nat := 118140960795 + 2480734 * 2 ^ 59
def prefixEnd_2480734 : Nat := 4983230072969 + 3 ^ 40 * 2480734 * 2
def baseEnd_2480734 : Nat := 1273808917950802350516319

theorem tailTrace_2480734 : CollatzResearch.WordTrace tailWord_2480734 prefixEnd_2480734 1273808917950802350516319 := by
  unfold tailWord_2480734
  simp only [CollatzResearch.WordTrace]
  refine ⟨11309975274341483560221157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60319868129821245654512837 11309975274341483560221157)
  ·
    refine ⟨2120620363939028167541467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11309975274341483560221157 2120620363939028167541467)
    ·
      refine ⟨3180930545908542251312201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2120620363939028167541467 3180930545908542251312201)
      ·
        refine ⟨2385697909431406688484151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3180930545908542251312201 2385697909431406688484151)
        ·
          refine ⟨3578546864147110032726227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2385697909431406688484151 3578546864147110032726227)
          ·
            refine ⟨5367820296220665049089341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3578546864147110032726227 5367820296220665049089341)
            ·
              refine ⟨2012932611082749393408503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5367820296220665049089341 2012932611082749393408503)
              ·
                refine ⟨3019398916624124090112755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2012932611082749393408503 3019398916624124090112755)
                ·
                  refine ⟨4529098374936186135169133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3019398916624124090112755 4529098374936186135169133)
                  ·
                    refine ⟨1698411890601069800688425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4529098374936186135169133 1698411890601069800688425)
                    ·
                      refine ⟨1273808917950802350516319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1698411890601069800688425 1273808917950802350516319)
                      ·
                        rfl

theorem cell23_2480734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_2480734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480734 prefixEnd_2480734 := by exact prefixLift 2480734
  have htrace : WordTrace (prefixWord ++ tailWord_2480734) baseStart_2480734 baseEnd_2480734 := by
    simpa [prefixWord, tailWord_2480734, baseEnd_2480734] using wordTrace_append hprefix tailTrace_2480734
  have hstable : (prefixWord ++ tailWord_2480734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480734).length < 2 ^ (prefixWord ++ tailWord_2480734).sum := by decide
  have hdescent : baseEnd_2480734 < baseStart_2480734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480749 : List Nat := [1, 5, 1, 1, 3, 1, 2, 2, 2, 5]
def baseStart_2480749 : Nat := 118140960795 + 2480749 * 2 ^ 59
def prefixEnd_2480749 : Nat := 4983230072969 + 3 ^ 40 * 2480749 * 2
def baseEnd_2480749 : Nat := 424605540053539930609583

theorem tailTrace_2480749 : CollatzResearch.WordTrace tailWord_2480749 prefixEnd_2480749 424605540053539930609583 := by
  unfold tailWord_2480749
  simp only [CollatzResearch.WordTrace]
  refine ⟨90480349289677526043565301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60320232859785017362376867 90480349289677526043565301)
  ·
    refine ⟨8482532745907268066584247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90480349289677526043565301 8482532745907268066584247)
    ·
      refine ⟨12723799118860902099876371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8482532745907268066584247 12723799118860902099876371)
      ·
        refine ⟨19085698678291353149814557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12723799118860902099876371 19085698678291353149814557)
        ·
          refine ⟨7157137004359257431180459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19085698678291353149814557 7157137004359257431180459)
          ·
            refine ⟨10735705506538886146770689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7157137004359257431180459 10735705506538886146770689)
            ·
              refine ⟨8051779129904164610078017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10735705506538886146770689 8051779129904164610078017)
              ·
                refine ⟨6038834347428123457558513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8051779129904164610078017 6038834347428123457558513)
                ·
                  refine ⟨4529125760571092593168885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6038834347428123457558513 4529125760571092593168885)
                  ·
                    refine ⟨424605540053539930609583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4529125760571092593168885 424605540053539930609583)
                    ·
                      rfl

theorem cell23_2480749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_2480749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480749 prefixEnd_2480749 := by exact prefixLift 2480749
  have htrace : WordTrace (prefixWord ++ tailWord_2480749) baseStart_2480749 baseEnd_2480749 := by
    simpa [prefixWord, tailWord_2480749, baseEnd_2480749] using wordTrace_append hprefix tailTrace_2480749
  have hstable : (prefixWord ++ tailWord_2480749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480749).length < 2 ^ (prefixWord ++ tailWord_2480749).sum := by decide
  have hdescent : baseEnd_2480749 < baseStart_2480749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480786 : List Nat := [3, 2, 3, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_2480786 : Nat := 118140960795 + 2480786 * 2 ^ 59
def prefixEnd_2480786 : Nat := 4983230072969 + 3 ^ 40 * 2480786 * 2
def baseEnd_2480786 : Nat := 1273835618944836147066079

theorem tailTrace_2480786 : CollatzResearch.WordTrace tailWord_2480786 prefixEnd_2480786 1273835618944836147066079 := by
  unfold tailWord_2480786
  simp only [CollatzResearch.WordTrace]
  refine ⟨22620424697635870340665553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60321132527028987575108141 22620424697635870340665553)
  ·
    refine ⟨16965318523226902755499165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22620424697635870340665553 16965318523226902755499165)
    ·
      refine ⟨6361994446210088533312187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16965318523226902755499165 6361994446210088533312187)
      ·
        refine ⟨9542991669315132799968281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6361994446210088533312187 9542991669315132799968281)
        ·
          refine ⟨7157243751986349599976211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9542991669315132799968281 7157243751986349599976211)
          ·
            refine ⟨10735865627979524399964317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7157243751986349599976211 10735865627979524399964317)
            ·
              refine ⟨4025949610492321649986619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10735865627979524399964317 4025949610492321649986619)
              ·
                refine ⟨6038924415738482474979929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4025949610492321649986619 6038924415738482474979929)
                ·
                  refine ⟨4529193311803861856234947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6038924415738482474979929 4529193311803861856234947)
                  ·
                    refine ⟨6793789967705792784352421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4529193311803861856234947 6793789967705792784352421)
                    ·
                      refine ⟨1273835618944836147066079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6793789967705792784352421 1273835618944836147066079)
                      ·
                        rfl

theorem cell23_2480786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_2480786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480786 prefixEnd_2480786 := by exact prefixLift 2480786
  have htrace : WordTrace (prefixWord ++ tailWord_2480786) baseStart_2480786 baseEnd_2480786 := by
    simpa [prefixWord, tailWord_2480786, baseEnd_2480786] using wordTrace_append hprefix tailTrace_2480786
  have hstable : (prefixWord ++ tailWord_2480786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480786).length < 2 ^ (prefixWord ++ tailWord_2480786).sum := by decide
  have hdescent : baseEnd_2480786 < baseStart_2480786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480792 : List Nat := [2, 1, 2, 4, 1, 1, 2, 2, 8]
def baseStart_2480792 : Nat := 118140960795 + 2480792 * 2 ^ 59
def prefixEnd_2480792 : Nat := 4983230072969 + 3 ^ 40 * 2480792 * 2
def baseEnd_2480792 : Nat := 141537633314307013732339

theorem tailTrace_2480792 : CollatzResearch.WordTrace tailWord_2480792 prefixEnd_2480792 141537633314307013732339 := by
  unfold tailWord_2480792
  simp only [CollatzResearch.WordTrace]
  refine ⟨45240958814260872193690315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60321278419014496258253753 45240958814260872193690315)
  ·
    refine ⟨67861438221391308290535473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45240958814260872193690315 67861438221391308290535473)
    ·
      refine ⟨50896078666043481217901605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67861438221391308290535473 50896078666043481217901605)
      ·
        refine ⟨9543014749883152728356551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50896078666043481217901605 9543014749883152728356551)
        ·
          refine ⟨14314522124824729092534827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9543014749883152728356551 14314522124824729092534827)
          ·
            refine ⟨21471783187237093638802241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14314522124824729092534827 21471783187237093638802241)
            ·
              refine ⟨16103837390427820229101681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21471783187237093638802241 16103837390427820229101681)
              ·
                refine ⟨12077878042820865171826261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16103837390427820229101681 12077878042820865171826261)
                ·
                  refine ⟨141537633314307013732339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12077878042820865171826261 141537633314307013732339)
                  ·
                    rfl

theorem cell23_2480792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 8].length) (baseStart_2480792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480792 prefixEnd_2480792 := by exact prefixLift 2480792
  have htrace : WordTrace (prefixWord ++ tailWord_2480792) baseStart_2480792 baseEnd_2480792 := by
    simpa [prefixWord, tailWord_2480792, baseEnd_2480792] using wordTrace_append hprefix tailTrace_2480792
  have hstable : (prefixWord ++ tailWord_2480792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480792).length < 2 ^ (prefixWord ++ tailWord_2480792).sum := by decide
  have hdescent : baseEnd_2480792 < baseStart_2480792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480813 : List Nat := [1, 5, 2, 1, 1, 2, 2, 4, 1, 4]
def baseStart_2480813 : Nat := 118140960795 + 2480813 * 2 ^ 59
def prefixEnd_2480813 : Nat := 4983230072969 + 3 ^ 40 * 2480813 * 2
def baseEnd_2480813 : Nat := 424616494307502513809485

theorem tailTrace_2480813 : CollatzResearch.WordTrace tailWord_2480813 prefixEnd_2480813 424616494307502513809485 := by
  unfold tailWord_2480813
  simp only [CollatzResearch.WordTrace]
  refine ⟨90482683561445664973895093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60321789040963776649263395 90482683561445664973895093)
  ·
    refine ⟨8482751583885531091302665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90482683561445664973895093 8482751583885531091302665)
    ·
      refine ⟨6362063687914148318476999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8482751583885531091302665 6362063687914148318476999)
      ·
        refine ⟨9543095531871222477715499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6362063687914148318476999 9543095531871222477715499)
        ·
          refine ⟨14314643297806833716573249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9543095531871222477715499 14314643297806833716573249)
          ·
            refine ⟨10735982473355125287429937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14314643297806833716573249 10735982473355125287429937)
            ·
              refine ⟨8051986855016343965572453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10735982473355125287429937 8051986855016343965572453)
              ·
                refine ⟨1509747535315564493544835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8051986855016343965572453 1509747535315564493544835)
                ·
                  refine ⟨2264621302973346740317253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1509747535315564493544835 2264621302973346740317253)
                  ·
                    refine ⟨424616494307502513809485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2264621302973346740317253 424616494307502513809485)
                    ·
                      rfl

theorem cell23_2480813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_2480813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480813 prefixEnd_2480813 := by exact prefixLift 2480813
  have htrace : WordTrace (prefixWord ++ tailWord_2480813) baseStart_2480813 baseEnd_2480813 := by
    simpa [prefixWord, tailWord_2480813, baseEnd_2480813] using wordTrace_append hprefix tailTrace_2480813
  have hstable : (prefixWord ++ tailWord_2480813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480813).length < 2 ^ (prefixWord ++ tailWord_2480813).sum := by decide
  have hdescent : baseEnd_2480813 < baseStart_2480813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480846 : List Nat := [4, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2]
def baseStart_2480846 : Nat := 118140960795 + 2480846 * 2 ^ 59
def prefixEnd_2480846 : Nat := 4983230072969 + 3 ^ 40 * 2480846 * 2
def baseEnd_2480846 : Nat := 1273866427784105912315803

theorem tailTrace_2480846 : CollatzResearch.WordTrace tailWord_2480846 prefixEnd_2480846 1273866427784105912315803 := by
  unfold tailWord_2480846
  simp only [CollatzResearch.WordTrace]
  refine ⟨11310485896290763951230799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60322591446884074406564261 11310485896290763951230799)
  ·
    refine ⟨16965728844436145926846199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11310485896290763951230799 16965728844436145926846199)
    ·
      refine ⟨25448593266654218890269299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16965728844436145926846199 25448593266654218890269299)
      ·
        refine ⟨38172889899981328335403949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25448593266654218890269299 38172889899981328335403949)
        ·
          refine ⟨14314833712492998125776481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38172889899981328335403949 14314833712492998125776481)
          ·
            refine ⟨10736125284369748594332361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14314833712492998125776481 10736125284369748594332361)
            ·
              refine ⟨8052093963277311445749271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10736125284369748594332361 8052093963277311445749271)
              ·
                refine ⟨12078140944915967168623907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8052093963277311445749271 12078140944915967168623907)
                ·
                  refine ⟨18117211417373950752935861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12078140944915967168623907 18117211417373950752935861)
                  ·
                    refine ⟨1698488570378807883087737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18117211417373950752935861 1698488570378807883087737)
                    ·
                      refine ⟨1273866427784105912315803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1698488570378807883087737 1273866427784105912315803)
                      ·
                        rfl

theorem cell23_2480846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2].length) (baseStart_2480846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480846 prefixEnd_2480846 := by exact prefixLift 2480846
  have htrace : WordTrace (prefixWord ++ tailWord_2480846) baseStart_2480846 baseEnd_2480846 := by
    simpa [prefixWord, tailWord_2480846, baseEnd_2480846] using wordTrace_append hprefix tailTrace_2480846
  have hstable : (prefixWord ++ tailWord_2480846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480846).length < 2 ^ (prefixWord ++ tailWord_2480846).sum := by decide
  have hdescent : baseEnd_2480846 < baseStart_2480846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480879 : List Nat := [1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 5]
def baseStart_2480879 : Nat := 118140960795 + 2480879 * 2 ^ 59
def prefixEnd_2480879 : Nat := 4983230072969 + 3 ^ 40 * 2480879 * 2
def baseEnd_2480879 : Nat := 1273883372645704283203151

theorem tailTrace_2480879 : CollatzResearch.WordTrace tailWord_2480879 prefixEnd_2480879 1273883372645704283203151 := by
  unfold tailWord_2480879
  simp only [CollatzResearch.WordTrace]
  refine ⟨90485090779206558245797691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60323393852804372163865127 90485090779206558245797691)
  ·
    refine ⟨135727636168809837368696537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90485090779206558245797691 135727636168809837368696537)
    ·
      refine ⟨101795727126607378026522403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135727636168809837368696537 101795727126607378026522403)
      ·
        refine ⟨152693590689911067039783605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101795727126607378026522403 152693590689911067039783605)
        ·
          refine ⟨14315024127179162534979713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152693590689911067039783605 14315024127179162534979713)
          ·
            refine ⟨10736268095384371901234785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14315024127179162534979713 10736268095384371901234785)
            ·
              refine ⟨8052201071538278925926089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10736268095384371901234785 8052201071538278925926089)
              ·
                refine ⟨6039150803653709194444567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8052201071538278925926089 6039150803653709194444567)
                ·
                  refine ⟨9058726205480563791666851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6039150803653709194444567 9058726205480563791666851)
                  ·
                    refine ⟨13588089308220845687500277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9058726205480563791666851 13588089308220845687500277)
                    ·
                      refine ⟨1273883372645704283203151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13588089308220845687500277 1273883372645704283203151)
                      ·
                        rfl

theorem cell23_2480879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 5].length) (baseStart_2480879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480879 prefixEnd_2480879 := by exact prefixLift 2480879
  have htrace : WordTrace (prefixWord ++ tailWord_2480879) baseStart_2480879 baseEnd_2480879 := by
    simpa [prefixWord, tailWord_2480879, baseEnd_2480879] using wordTrace_append hprefix tailTrace_2480879
  have hstable : (prefixWord ++ tailWord_2480879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480879).length < 2 ^ (prefixWord ++ tailWord_2480879).sum := by decide
  have hdescent : baseEnd_2480879 < baseStart_2480879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480910 : List Nat := [4, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2]
def baseStart_2480910 : Nat := 118140960795 + 2480910 * 2 ^ 59
def prefixEnd_2480910 : Nat := 4983230072969 + 3 ^ 40 * 2480910 * 2
def baseEnd_2480910 : Nat := 1273899290545993661915509

theorem tailTrace_2480910 : CollatzResearch.WordTrace tailWord_2480910 prefixEnd_2480910 1273899290545993661915509 := by
  unfold tailWord_2480910
  simp only [CollatzResearch.WordTrace]
  refine ⟨11310777680261781317522023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60324147628062833693450789 11310777680261781317522023)
  ·
    refine ⟨16966166520392671976283035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11310777680261781317522023 16966166520392671976283035)
    ·
      refine ⟨25449249780589007964424553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16966166520392671976283035 25449249780589007964424553)
      ·
        refine ⟨19086937335441755973318415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25449249780589007964424553 19086937335441755973318415)
        ·
          refine ⟨28630406003162633959977623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19086937335441755973318415 28630406003162633959977623)
          ·
            refine ⟨42945609004743950939966435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28630406003162633959977623 42945609004743950939966435)
            ·
              refine ⟨64418413507115926409949653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42945609004743950939966435 64418413507115926409949653)
              ·
                refine ⟨1509806566573029525233195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 64418413507115926409949653 1509806566573029525233195)
                ·
                  refine ⟨2264709849859544287849793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1509806566573029525233195 2264709849859544287849793)
                  ·
                    refine ⟨1698532387394658215887345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2264709849859544287849793 1698532387394658215887345)
                    ·
                      refine ⟨1273899290545993661915509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1698532387394658215887345 1273899290545993661915509)
                      ·
                        rfl

theorem cell23_2480910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_2480910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480910 prefixEnd_2480910 := by exact prefixLift 2480910
  have htrace : WordTrace (prefixWord ++ tailWord_2480910) baseStart_2480910 baseEnd_2480910 := by
    simpa [prefixWord, tailWord_2480910, baseEnd_2480910] using wordTrace_append hprefix tailTrace_2480910
  have hstable : (prefixWord ++ tailWord_2480910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480910).length < 2 ^ (prefixWord ++ tailWord_2480910).sum := by decide
  have hdescent : baseEnd_2480910 < baseStart_2480910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480927 : List Nat := [1, 1, 2, 4, 2, 2, 4, 2, 1, 2, 2]
def baseStart_2480927 : Nat := 118140960795 + 2480927 * 2 ^ 59
def prefixEnd_2480927 : Nat := 4983230072969 + 3 ^ 40 * 2480927 * 2
def baseEnd_2480927 : Nat := 1273908019717120095402931

theorem tailTrace_2480927 : CollatzResearch.WordTrace tailWord_2480927 prefixEnd_2480927 1273908019717120095402931 := by
  unfold tailWord_2480927
  simp only [CollatzResearch.WordTrace]
  refine ⟨90486841483032662443545035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60324560988688441629030023 90486841483032662443545035)
  ·
    refine ⟨135730262224548993665317553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90486841483032662443545035 135730262224548993665317553)
    ·
      refine ⟨101797696668411745248988165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135730262224548993665317553 101797696668411745248988165)
      ·
        refine ⟨19087068125327202234185281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101797696668411745248988165 19087068125327202234185281)
        ·
          refine ⟨14315301093995401675638961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19087068125327202234185281 14315301093995401675638961)
          ·
            refine ⟨10736475820496551256729221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14315301093995401675638961 10736475820496551256729221)
            ·
              refine ⟨2013089216343103360636729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10736475820496551256729221 2013089216343103360636729)
              ·
                refine ⟨1509816912257327520477547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2013089216343103360636729 1509816912257327520477547)
                ·
                  refine ⟨2264725368385991280716321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1509816912257327520477547 2264725368385991280716321)
                  ·
                    refine ⟨1698544026289493460537241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2264725368385991280716321 1698544026289493460537241)
                    ·
                      refine ⟨1273908019717120095402931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1698544026289493460537241 1273908019717120095402931)
                      ·
                        rfl

theorem cell23_2480927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_2480927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480927 prefixEnd_2480927 := by exact prefixLift 2480927
  have htrace : WordTrace (prefixWord ++ tailWord_2480927) baseStart_2480927 baseEnd_2480927 := by
    simpa [prefixWord, tailWord_2480927, baseEnd_2480927] using wordTrace_append hprefix tailTrace_2480927
  have hstable : (prefixWord ++ tailWord_2480927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480927).length < 2 ^ (prefixWord ++ tailWord_2480927).sum := by decide
  have hdescent : baseEnd_2480927 < baseStart_2480927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480964 : List Nat := [2, 3, 4, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_2480964 : Nat := 118140960795 + 2480964 * 2 ^ 59
def prefixEnd_2480964 : Nat := 4983230072969 + 3 ^ 40 * 2480964 * 2
def baseEnd_2480964 : Nat := 1273927018501336450640261

theorem tailTrace_2480964 : CollatzResearch.WordTrace tailWord_2480964 prefixEnd_2480964 1273927018501336450640261 := by
  unfold tailWord_2480964
  simp only [CollatzResearch.WordTrace]
  refine ⟨45244095491949308881320973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60325460655932411841761297 45244095491949308881320973)
  ·
    refine ⟨16966535809480990830495365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45244095491949308881320973 16966535809480990830495365)
    ·
      refine ⟨3181225464277685780717881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16966535809480990830495365 3181225464277685780717881)
      ·
        refine ⟨2385919098208264335538411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3181225464277685780717881 2385919098208264335538411)
        ·
          refine ⟨3578878647312396503307617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2385919098208264335538411 3578878647312396503307617)
          ·
            refine ⟨2684158985484297377480713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3578878647312396503307617 2684158985484297377480713)
            ·
              refine ⟨2013119239113223033110535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2684158985484297377480713 2013119239113223033110535)
              ·
                refine ⟨3019678858669834549665803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2013119239113223033110535 3019678858669834549665803)
                ·
                  refine ⟨4529518288004751824498705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3019678858669834549665803 4529518288004751824498705)
                  ·
                    refine ⟨3397138716003563868374029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4529518288004751824498705 3397138716003563868374029)
                    ·
                      refine ⟨1273927018501336450640261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3397138716003563868374029 1273927018501336450640261)
                      ·
                        rfl

theorem cell23_2480964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_2480964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480964 prefixEnd_2480964 := by exact prefixLift 2480964
  have htrace : WordTrace (prefixWord ++ tailWord_2480964) baseStart_2480964 baseEnd_2480964 := by
    simpa [prefixWord, tailWord_2480964, baseEnd_2480964] using wordTrace_append hprefix tailTrace_2480964
  have hstable : (prefixWord ++ tailWord_2480964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480964).length < 2 ^ (prefixWord ++ tailWord_2480964).sum := by decide
  have hdescent : baseEnd_2480964 < baseStart_2480964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480977 : List Nat := [1, 2, 2, 1, 7, 1, 1, 2, 2, 1, 3]
def baseStart_2480977 : Nat := 118140960795 + 2480977 * 2 ^ 59
def prefixEnd_2480977 : Nat := 4983230072969 + 3 ^ 40 * 2480977 * 2
def baseEnd_2480977 : Nat := 1273933693749844899777701

theorem tailTrace_2480977 : CollatzResearch.WordTrace tailWord_2480977 prefixEnd_2480977 1273933693749844899777701 := by
  unfold tailWord_2480977
  simp only [CollatzResearch.WordTrace]
  refine ⟨90488665132851520982865185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60325776755234347321910123 90488665132851520982865185)
  ·
    refine ⟨67866498849638640737148889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90488665132851520982865185 67866498849638640737148889)
    ·
      refine ⟨50899874137228980552861667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67866498849638640737148889 50899874137228980552861667)
      ·
        refine ⟨76349811205843470829292501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50899874137228980552861667 76349811205843470829292501)
        ·
          refine ⟨1789448700136956347561543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 76349811205843470829292501 1789448700136956347561543)
          ·
            refine ⟨2684173050205434521342315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1789448700136956347561543 2684173050205434521342315)
            ·
              refine ⟨4026259575308151782013473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2684173050205434521342315 4026259575308151782013473)
              ·
                refine ⟨3019694681481113836510105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4026259575308151782013473 3019694681481113836510105)
                ·
                  refine ⟨2264771011110835377382579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3019694681481113836510105 2264771011110835377382579)
                  ·
                    refine ⟨3397156516666253066073869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2264771011110835377382579 3397156516666253066073869)
                    ·
                      refine ⟨1273933693749844899777701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3397156516666253066073869 1273933693749844899777701)
                      ·
                        rfl

theorem cell23_2480977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 2, 1, 3].length) (baseStart_2480977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480977 prefixEnd_2480977 := by exact prefixLift 2480977
  have htrace : WordTrace (prefixWord ++ tailWord_2480977) baseStart_2480977 baseEnd_2480977 := by
    simpa [prefixWord, tailWord_2480977, baseEnd_2480977] using wordTrace_append hprefix tailTrace_2480977
  have hstable : (prefixWord ++ tailWord_2480977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480977).length < 2 ^ (prefixWord ++ tailWord_2480977).sum := by decide
  have hdescent : baseEnd_2480977 < baseStart_2480977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480996 : List Nat := [2, 3, 1, 1, 4, 1, 2, 1, 2, 2, 4]
def baseStart_2480996 : Nat := 118140960795 + 2480996 * 2 ^ 59
def prefixEnd_2480996 : Nat := 4983230072969 + 3 ^ 40 * 2480996 * 2
def baseEnd_2480996 : Nat := 1273943449882280325440113

theorem tailTrace_2480996 : CollatzResearch.WordTrace tailWord_2480996 prefixEnd_2480996 1273943449882280325440113 := by
  unfold tailWord_2480996
  simp only [CollatzResearch.WordTrace]
  refine ⟨45244679059891343613903421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60326238746521791485204561 45244679059891343613903421)
  ·
    refine ⟨16966754647459253855213783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45244679059891343613903421 16966754647459253855213783)
    ·
      refine ⟨25450131971188880782820675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16966754647459253855213783 25450131971188880782820675)
      ·
        refine ⟨38175197956783321174231013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25450131971188880782820675 38175197956783321174231013)
        ·
          refine ⟨7157849616896872720168315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38175197956783321174231013 7157849616896872720168315)
          ·
            refine ⟨10736774425345309080252473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7157849616896872720168315 10736774425345309080252473)
            ·
              refine ⟨8052580819008981810189355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10736774425345309080252473 8052580819008981810189355)
              ·
                refine ⟨12078871228513472715284033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8052580819008981810189355 12078871228513472715284033)
                ·
                  refine ⟨9059153421385104536463025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12078871228513472715284033 9059153421385104536463025)
                  ·
                    refine ⟨6794365066038828402347269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9059153421385104536463025 6794365066038828402347269)
                    ·
                      refine ⟨1273943449882280325440113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6794365066038828402347269 1273943449882280325440113)
                      ·
                        rfl

theorem cell23_2480996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_2480996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2480996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2480996 prefixEnd_2480996 := by exact prefixLift 2480996
  have htrace : WordTrace (prefixWord ++ tailWord_2480996) baseStart_2480996 baseEnd_2480996 := by
    simpa [prefixWord, tailWord_2480996, baseEnd_2480996] using wordTrace_append hprefix tailTrace_2480996
  have hstable : (prefixWord ++ tailWord_2480996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480996).length < 2 ^ (prefixWord ++ tailWord_2480996).sum := by decide
  have hdescent : baseEnd_2480996 < baseStart_2480996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481000 : List Nat := [2, 1, 4, 2, 1, 4, 1, 1, 1, 4, 2]
def baseStart_2481000 : Nat := 118140960795 + 2481000 * 2 ^ 59
def prefixEnd_2481000 : Nat := 4983230072969 + 3 ^ 40 * 2481000 * 2
def baseEnd_2481000 : Nat := 1273945503804898309790095

theorem tailTrace_2481000 : CollatzResearch.WordTrace tailWord_2481000 prefixEnd_2481000 1273945503804898309790095 := by
  unfold tailWord_2481000
  simp only [CollatzResearch.WordTrace]
  refine ⟨45244752005884097955476227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60326336007845463940634969 45244752005884097955476227)
  ·
    refine ⟨67867128008826146933214341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45244752005884097955476227 67867128008826146933214341)
    ·
      refine ⟨12725086501654902549977689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67867128008826146933214341 12725086501654902549977689)
      ·
        refine ⟨9543814876241176912483267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12725086501654902549977689 9543814876241176912483267)
        ·
          refine ⟨14315722314361765368724901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9543814876241176912483267 14315722314361765368724901)
          ·
            refine ⟨2684197933942831006635919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14315722314361765368724901 2684197933942831006635919)
            ·
              refine ⟨4026296900914246509953879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2684197933942831006635919 4026296900914246509953879)
              ·
                refine ⟨6039445351371369764930819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4026296900914246509953879 6039445351371369764930819)
                ·
                  refine ⟨9059168027057054647396229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6039445351371369764930819 9059168027057054647396229)
                  ·
                    refine ⟨1698594005073197746386793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9059168027057054647396229 1698594005073197746386793)
                    ·
                      refine ⟨1273945503804898309790095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1698594005073197746386793 1273945503804898309790095)
                      ·
                        rfl

theorem cell23_2481000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_2481000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481000 prefixEnd_2481000 := by exact prefixLift 2481000
  have htrace : WordTrace (prefixWord ++ tailWord_2481000) baseStart_2481000 baseEnd_2481000 := by
    simpa [prefixWord, tailWord_2481000, baseEnd_2481000] using wordTrace_append hprefix tailTrace_2481000
  have hstable : (prefixWord ++ tailWord_2481000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481000).length < 2 ^ (prefixWord ++ tailWord_2481000).sum := by decide
  have hdescent : baseEnd_2481000 < baseStart_2481000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481019 : List Nat := [1, 1, 1, 1, 1, 5, 4, 1, 1, 7]
def baseStart_2481019 : Nat := 118140960795 + 2481019 * 2 ^ 59
def prefixEnd_2481019 : Nat := 4983230072969 + 3 ^ 40 * 2481019 * 2
def baseEnd_2481019 : Nat := 424651753312444578484169

theorem tailTrace_2481019 : CollatzResearch.WordTrace tailWord_2481019 prefixEnd_2481019 424651753312444578484169 := by
  unfold tailWord_2481019
  simp only [CollatzResearch.WordTrace]
  refine ⟨90490196998699362155894111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60326797999132908103929407 90490196998699362155894111)
  ·
    refine ⟨135735295498049043233841167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90490196998699362155894111 135735295498049043233841167)
    ·
      refine ⟨203602943247073564850761751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135735295498049043233841167 203602943247073564850761751)
      ·
        refine ⟨305404414870610347276142627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203602943247073564850761751 305404414870610347276142627)
        ·
          refine ⟨458106622305915520914213941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305404414870610347276142627 458106622305915520914213941)
          ·
            refine ⟨42947495841179580085707557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 458106622305915520914213941 42947495841179580085707557)
            ·
              refine ⟨8052655470221171266070167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42947495841179580085707557 8052655470221171266070167)
              ·
                refine ⟨12078983205331756899105251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8052655470221171266070167 12078983205331756899105251)
                ·
                  refine ⟨18118474807997635348657877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12078983205331756899105251 18118474807997635348657877)
                  ·
                    refine ⟨424651753312444578484169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18118474807997635348657877 424651753312444578484169)
                    ·
                      rfl

theorem cell23_2481019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 7].length) (baseStart_2481019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481019 prefixEnd_2481019 := by exact prefixLift 2481019
  have htrace : WordTrace (prefixWord ++ tailWord_2481019) baseStart_2481019 baseEnd_2481019 := by
    simpa [prefixWord, tailWord_2481019, baseEnd_2481019] using wordTrace_append hprefix tailTrace_2481019
  have hstable : (prefixWord ++ tailWord_2481019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481019).length < 2 ^ (prefixWord ++ tailWord_2481019).sum := by decide
  have hdescent : baseEnd_2481019 < baseStart_2481019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481079 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 10]
def baseStart_2481079 : Nat := 118140960795 + 2481079 * 2 ^ 59
def prefixEnd_2481079 : Nat := 4983230072969 + 3 ^ 40 * 2481079 * 2
def baseEnd_2481079 : Nat := 141554007641844833411359

theorem tailTrace_2481079 : CollatzResearch.WordTrace tailWord_2481079 prefixEnd_2481079 141554007641844833411359 := by
  unfold tailWord_2481079
  simp only [CollatzResearch.WordTrace]
  refine ⟨90492385378481992403078291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60328256918987994935385527 90492385378481992403078291)
  ·
    refine ⟨135738578067722988604617437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90492385378481992403078291 135738578067722988604617437)
    ·
      refine ⟨50901966775396120726731539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135738578067722988604617437 50901966775396120726731539)
      ·
        refine ⟨76352950163094181090097309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50901966775396120726731539 76352950163094181090097309)
        ·
          refine ⟨28632356311160317908786491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76352950163094181090097309 28632356311160317908786491)
          ·
            refine ⟨42948534466740476863179737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28632356311160317908786491 42948534466740476863179737)
            ·
              refine ⟨32211400850055357647384803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42948534466740476863179737 32211400850055357647384803)
              ·
                refine ⟨48317101275083036471077205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32211400850055357647384803 48317101275083036471077205)
                ·
                  refine ⟨141554007641844833411359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 48317101275083036471077205 141554007641844833411359)
                  ·
                    rfl

theorem cell23_2481079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 10].length) (baseStart_2481079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481079 prefixEnd_2481079 := by exact prefixLift 2481079
  have htrace : WordTrace (prefixWord ++ tailWord_2481079) baseStart_2481079 baseEnd_2481079 := by
    simpa [prefixWord, tailWord_2481079, baseEnd_2481079] using wordTrace_append hprefix tailTrace_2481079
  have hstable : (prefixWord ++ tailWord_2481079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481079).length < 2 ^ (prefixWord ++ tailWord_2481079).sum := by decide
  have hdescent : baseEnd_2481079 < baseStart_2481079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481086 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_2481086 : Nat := 118140960795 + 2481086 * 2 ^ 59
def prefixEnd_2481086 : Nat := 4983230072969 + 3 ^ 40 * 2481086 * 2
def baseEnd_2481086 : Nat := 1273989663141184973314699

theorem tailTrace_2481086 : CollatzResearch.WordTrace tailWord_2481086 prefixEnd_2481086 1273989663141184973314699 := by
  unfold tailWord_2481086
  simp only [CollatzResearch.WordTrace]
  refine ⟨11311580086182079074822889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60328427126304421732388741 11311580086182079074822889)
  ·
    refine ⟨8483685064636559306117167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11311580086182079074822889 8483685064636559306117167)
    ·
      refine ⟨12725527596954838959175751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8483685064636559306117167 12725527596954838959175751)
      ·
        refine ⟨19088291395432258438763627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12725527596954838959175751 19088291395432258438763627)
        ·
          refine ⟨28632437093148387658145441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19088291395432258438763627 28632437093148387658145441)
          ·
            refine ⟨21474327819861290743609081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28632437093148387658145441 21474327819861290743609081)
            ·
              refine ⟨16105745864895968057706811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21474327819861290743609081 16105745864895968057706811)
              ·
                refine ⟨24158618797343952086560217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16105745864895968057706811 24158618797343952086560217)
                ·
                  refine ⟨18118964098007964064920163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24158618797343952086560217 18118964098007964064920163)
                  ·
                    refine ⟨27178446147011946097380245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18118964098007964064920163 27178446147011946097380245)
                    ·
                      refine ⟨1273989663141184973314699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27178446147011946097380245 1273989663141184973314699)
                      ·
                        rfl

theorem cell23_2481086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_2481086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481086 prefixEnd_2481086 := by exact prefixLift 2481086
  have htrace : WordTrace (prefixWord ++ tailWord_2481086) baseStart_2481086 baseEnd_2481086 := by
    simpa [prefixWord, tailWord_2481086, baseEnd_2481086] using wordTrace_append hprefix tailTrace_2481086
  have hstable : (prefixWord ++ tailWord_2481086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481086).length < 2 ^ (prefixWord ++ tailWord_2481086).sum := by decide
  have hdescent : baseEnd_2481086 < baseStart_2481086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481100 : List Nat := [2, 2, 1, 4, 1, 1, 3, 4, 1, 4]
def baseStart_2481100 : Nat := 118140960795 + 2481100 * 2 ^ 59
def prefixEnd_2481100 : Nat := 4983230072969 + 3 ^ 40 * 2481100 * 2
def baseEnd_2481100 : Nat := 424665617290115972846545

theorem tailTrace_2481100 : CollatzResearch.WordTrace tailWord_2481100 prefixEnd_2481100 424665617290115972846545 := by
  unfold tailWord_2481100
  simp only [CollatzResearch.WordTrace]
  refine ⟨45246575655702956494796377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60328767540937275326395169 45246575655702956494796377)
  ·
    refine ⟨33934931741777217371097283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45246575655702956494796377 33934931741777217371097283)
    ·
      refine ⟨50902397612665826056645925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33934931741777217371097283 50902397612665826056645925)
      ·
        refine ⟨9544199552374842385621111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50902397612665826056645925 9544199552374842385621111)
        ·
          refine ⟨14316299328562263578431667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9544199552374842385621111 14316299328562263578431667)
          ·
            refine ⟨21474448992843395367647501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14316299328562263578431667 21474448992843395367647501)
            ·
              refine ⟨8052918372316273262867813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21474448992843395367647501 8052918372316273262867813)
              ·
                refine ⟨1509922194809301236787715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8052918372316273262867813 1509922194809301236787715)
                ·
                  refine ⟨2264883292213951855181573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1509922194809301236787715 2264883292213951855181573)
                  ·
                    refine ⟨424665617290115972846545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2264883292213951855181573 424665617290115972846545)
                    ·
                      rfl

theorem cell23_2481100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4, 1, 4].length) (baseStart_2481100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481100 prefixEnd_2481100 := by exact prefixLift 2481100
  have htrace : WordTrace (prefixWord ++ tailWord_2481100) baseStart_2481100 baseEnd_2481100 := by
    simpa [prefixWord, tailWord_2481100, baseEnd_2481100] using wordTrace_append hprefix tailTrace_2481100
  have hstable : (prefixWord ++ tailWord_2481100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481100).length < 2 ^ (prefixWord ++ tailWord_2481100).sum := by decide
  have hdescent : baseEnd_2481100 < baseStart_2481100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481173 : List Nat := [1, 3, 2, 1, 4, 1, 3, 1, 1, 6]
def baseStart_2481173 : Nat := 118140960795 + 2481173 * 2 ^ 59
def prefixEnd_2481173 : Nat := 4983230072969 + 3 ^ 40 * 2481173 * 2
def baseEnd_2481173 : Nat := 424678111986042044308933

theorem tailTrace_2481173 : CollatzResearch.WordTrace tailWord_2481173 prefixEnd_2481173 424678111986042044308933 := by
  unfold tailWord_2481173
  simp only [CollatzResearch.WordTrace]
  refine ⟨90495813840141446457000173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60330542560094297638000115 90495813840141446457000173)
  ·
    refine ⟨33935930190053042421375065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90495813840141446457000173 33935930190053042421375065)
    ·
      refine ⟨25451947642539781816031299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33935930190053042421375065 25451947642539781816031299)
      ·
        refine ⟨38177921463809672724046949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25451947642539781816031299 38177921463809672724046949)
        ·
          refine ⟨7158360274464313635758803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38177921463809672724046949 7158360274464313635758803)
          ·
            refine ⟨10737540411696470453638205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7158360274464313635758803 10737540411696470453638205)
            ·
              refine ⟨4026577654386176420114327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10737540411696470453638205 4026577654386176420114327)
              ·
                refine ⟨6039866481579264630171491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4026577654386176420114327 6039866481579264630171491)
                ·
                  refine ⟨9059799722368896945257237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6039866481579264630171491 9059799722368896945257237)
                  ·
                    refine ⟨424678111986042044308933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9059799722368896945257237 424678111986042044308933)
                    ·
                      rfl

theorem cell23_2481173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_2481173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481173 prefixEnd_2481173 := by exact prefixLift 2481173
  have htrace : WordTrace (prefixWord ++ tailWord_2481173) baseStart_2481173 baseEnd_2481173 := by
    simpa [prefixWord, tailWord_2481173, baseEnd_2481173] using wordTrace_append hprefix tailTrace_2481173
  have hstable : (prefixWord ++ tailWord_2481173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481173).length < 2 ^ (prefixWord ++ tailWord_2481173).sum := by decide
  have hdescent : baseEnd_2481173 < baseStart_2481173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481191 : List Nat := [1, 1, 7, 1, 1, 3, 1, 3, 1, 1, 3]
def baseStart_2481191 : Nat := 118140960795 + 2481191 * 2 ^ 59
def prefixEnd_2481191 : Nat := 4983230072969 + 3 ^ 40 * 2481191 * 2
def baseEnd_2481191 : Nat := 1274043578609907062501717

theorem tailTrace_2481191 : CollatzResearch.WordTrace tailWord_2481191 prefixEnd_2481191 1274043578609907062501717 := by
  unfold tailWord_2481191
  simp only [CollatzResearch.WordTrace]
  refine ⟨90496470354076235531155427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60330980236050823687436951 90496470354076235531155427)
  ·
    refine ⟨135744705531114353296733141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90496470354076235531155427 135744705531114353296733141)
    ·
      refine ⟨3181516535885492655392183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 135744705531114353296733141 3181516535885492655392183)
      ·
        refine ⟨4772274803828238983088275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3181516535885492655392183 4772274803828238983088275)
        ·
          refine ⟨7158412205742358474632413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4772274803828238983088275 7158412205742358474632413)
          ·
            refine ⟨2684404577153384427987155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7158412205742358474632413 2684404577153384427987155)
            ·
              refine ⟨4026606865730076641980733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2684404577153384427987155 4026606865730076641980733)
              ·
                refine ⟨1509977574648778740742775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4026606865730076641980733 1509977574648778740742775)
                ·
                  refine ⟨2264966361973168111114163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1509977574648778740742775 2264966361973168111114163)
                  ·
                    refine ⟨3397449542959752166671245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2264966361973168111114163 3397449542959752166671245)
                    ·
                      refine ⟨1274043578609907062501717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3397449542959752166671245 1274043578609907062501717)
                      ·
                        rfl

theorem cell23_2481191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_2481191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481191 prefixEnd_2481191 := by exact prefixLift 2481191
  have htrace : WordTrace (prefixWord ++ tailWord_2481191) baseStart_2481191 baseEnd_2481191 := by
    simpa [prefixWord, tailWord_2481191, baseEnd_2481191] using wordTrace_append hprefix tailTrace_2481191
  have hstable : (prefixWord ++ tailWord_2481191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481191).length < 2 ^ (prefixWord ++ tailWord_2481191).sum := by decide
  have hdescent : baseEnd_2481191 < baseStart_2481191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481214 : List Nat := [4, 2, 1, 3, 1, 1, 3, 1, 3, 2, 2]
def baseStart_2481214 : Nat := 118140960795 + 2481214 * 2 ^ 59
def prefixEnd_2481214 : Nat := 4983230072969 + 3 ^ 40 * 2481214 * 2
def baseEnd_2481214 : Nat := 1274055388664960472514111

theorem tailTrace_2481214 : CollatzResearch.WordTrace tailWord_2481214 prefixEnd_2481214 1274055388664960472514111 := by
  unfold tailWord_2481214
  simp only [CollatzResearch.WordTrace]
  refine ⟨11312163654124113807405337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60331539488661940306161797 11312163654124113807405337)
  ·
    refine ⟨8484122740593085355554003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11312163654124113807405337 8484122740593085355554003)
    ·
      refine ⟨12726184110889628033331005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8484122740593085355554003 12726184110889628033331005)
      ·
        refine ⟨4772319041583610512499127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12726184110889628033331005 4772319041583610512499127)
        ·
          refine ⟨7158478562375415768748691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4772319041583610512499127 7158478562375415768748691)
          ·
            refine ⟨10737717843563123653123037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7158478562375415768748691 10737717843563123653123037)
            ·
              refine ⟨4026644191336171369921139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10737717843563123653123037 4026644191336171369921139)
              ·
                refine ⟨6039966287004257054881709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4026644191336171369921139 6039966287004257054881709)
                ·
                  refine ⟨2264987357626596395580641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6039966287004257054881709 2264987357626596395580641)
                  ·
                    refine ⟨1698740518219947296685481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2264987357626596395580641 1698740518219947296685481)
                    ·
                      refine ⟨1274055388664960472514111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1698740518219947296685481 1274055388664960472514111)
                      ·
                        rfl

theorem cell23_2481214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_2481214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481214 prefixEnd_2481214 := by exact prefixLift 2481214
  have htrace : WordTrace (prefixWord ++ tailWord_2481214) baseStart_2481214 baseEnd_2481214 := by
    simpa [prefixWord, tailWord_2481214, baseEnd_2481214] using wordTrace_append hprefix tailTrace_2481214
  have hstable : (prefixWord ++ tailWord_2481214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481214).length < 2 ^ (prefixWord ++ tailWord_2481214).sum := by decide
  have hdescent : baseEnd_2481214 < baseStart_2481214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481216 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 2, 7]
def baseStart_2481216 : Nat := 118140960795 + 2481216 * 2 ^ 59
def prefixEnd_2481216 : Nat := 4983230072969 + 3 ^ 40 * 2481216 * 2
def baseEnd_2481216 : Nat := 424685471875423154896367

theorem tailTrace_2481216 : CollatzResearch.WordTrace tailWord_2481216 prefixEnd_2481216 424685471875423154896367 := by
  unfold tailWord_2481216
  simp only [CollatzResearch.WordTrace]
  refine ⟨45248691089492832400407751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60331588119323776533877001 45248691089492832400407751)
  ·
    refine ⟨67873036634239248600611627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45248691089492832400407751 67873036634239248600611627)
    ·
      refine ⟨101809554951358872900917441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67873036634239248600611627 101809554951358872900917441)
      ·
        refine ⟨76357166213519154675688081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101809554951358872900917441 76357166213519154675688081)
        ·
          refine ⟨57267874660139366006766061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76357166213519154675688081 57267874660139366006766061)
          ·
            refine ⟨21475452997552262252537273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57267874660139366006766061 21475452997552262252537273)
            ·
              refine ⟨16106589748164196689402955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21475452997552262252537273 16106589748164196689402955)
              ·
                refine ⟨24159884622246295034104433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16106589748164196689402955 24159884622246295034104433)
                ·
                  refine ⟨18119913466684721275578325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24159884622246295034104433 18119913466684721275578325)
                  ·
                    refine ⟨424685471875423154896367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18119913466684721275578325 424685471875423154896367)
                    ·
                      rfl

theorem cell23_2481216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 2, 7].length) (baseStart_2481216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481216 prefixEnd_2481216 := by exact prefixLift 2481216
  have htrace : WordTrace (prefixWord ++ tailWord_2481216) baseStart_2481216 baseEnd_2481216 := by
    simpa [prefixWord, tailWord_2481216, baseEnd_2481216] using wordTrace_append hprefix tailTrace_2481216
  have hstable : (prefixWord ++ tailWord_2481216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481216).length < 2 ^ (prefixWord ++ tailWord_2481216).sum := by decide
  have hdescent : baseEnd_2481216 < baseStart_2481216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481240 : List Nat := [2, 1, 2, 2, 1, 3, 3, 1, 3, 3, 2]
def baseStart_2481240 : Nat := 118140960795 + 2481240 * 2 ^ 59
def prefixEnd_2481240 : Nat := 4983230072969 + 3 ^ 40 * 2481240 * 2
def baseEnd_2481240 : Nat := 1274068739161977370788991

theorem tailTrace_2481240 : CollatzResearch.WordTrace tailWord_2481240 prefixEnd_2481240 1274068739161977370788991 := by
  unfold tailWord_2481240
  simp only [CollatzResearch.WordTrace]
  refine ⟨45249128765449358449844587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60332171687265811266459449 45249128765449358449844587)
  ·
    refine ⟨67873693148174037674766881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45249128765449358449844587 67873693148174037674766881)
    ·
      refine ⟨50905269861130528256075161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67873693148174037674766881 50905269861130528256075161)
      ·
        refine ⟨38178952395847896192056371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50905269861130528256075161 38178952395847896192056371)
        ·
          refine ⟨57268428593771844288084557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38178952395847896192056371 57268428593771844288084557)
          ·
            refine ⟨21475660722664441608031709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57268428593771844288084557 21475660722664441608031709)
            ·
              refine ⟨8053372770999165603011891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21475660722664441608031709 8053372770999165603011891)
              ·
                refine ⟨12080059156498748404517837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8053372770999165603011891 12080059156498748404517837)
                ·
                  refine ⟨4530022183687030651694189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12080059156498748404517837 4530022183687030651694189)
                  ·
                    refine ⟨1698758318882636494385321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4530022183687030651694189 1698758318882636494385321)
                    ·
                      refine ⟨1274068739161977370788991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1698758318882636494385321 1274068739161977370788991)
                      ·
                        rfl

theorem cell23_2481240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 3, 3, 2].length) (baseStart_2481240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481240 prefixEnd_2481240 := by exact prefixLift 2481240
  have htrace : WordTrace (prefixWord ++ tailWord_2481240) baseStart_2481240 baseEnd_2481240 := by
    simpa [prefixWord, tailWord_2481240, baseEnd_2481240] using wordTrace_append hprefix tailTrace_2481240
  have hstable : (prefixWord ++ tailWord_2481240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481240).length < 2 ^ (prefixWord ++ tailWord_2481240).sum := by decide
  have hdescent : baseEnd_2481240 < baseStart_2481240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481283 : List Nat := [1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 4]
def baseStart_2481283 : Nat := 118140960795 + 2481283 * 2 ^ 59
def prefixEnd_2481283 : Nat := 4983230072969 + 3 ^ 40 * 2481283 * 2
def baseEnd_2481283 : Nat := 1274090818830120702551293

theorem tailTrace_2481283 : CollatzResearch.WordTrace tailWord_2481283 prefixEnd_2481283 1274090818830120702551293 := by
  unfold tailWord_2481283
  simp only [CollatzResearch.WordTrace]
  refine ⟨90499825869742935243504503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60333217246495290162336335 90499825869742935243504503)
  ·
    refine ⟨135749738804614402865256755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90499825869742935243504503 135749738804614402865256755)
    ·
      refine ⟨203624608206921604297885133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135749738804614402865256755 203624608206921604297885133)
      ·
        refine ⟨76359228077595601611706925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203624608206921604297885133 76359228077595601611706925)
        ·
          refine ⟨28634710529098350604390097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76359228077595601611706925 28634710529098350604390097)
          ·
            refine ⟨21476032896823762953292573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28634710529098350604390097 21476032896823762953292573)
            ·
              refine ⟨8053512336308911107484715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21476032896823762953292573 8053512336308911107484715)
              ·
                refine ⟨12080268504463366661227073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8053512336308911107484715 12080268504463366661227073)
                ·
                  refine ⟨9060201378347524995920305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12080268504463366661227073 9060201378347524995920305)
                  ·
                    refine ⟨6795151033760643746940229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9060201378347524995920305 6795151033760643746940229)
                    ·
                      refine ⟨1274090818830120702551293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6795151033760643746940229 1274090818830120702551293)
                      ·
                        rfl

theorem cell23_2481283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_2481283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481283 prefixEnd_2481283 := by exact prefixLift 2481283
  have htrace : WordTrace (prefixWord ++ tailWord_2481283) baseStart_2481283 baseEnd_2481283 := by
    simpa [prefixWord, tailWord_2481283, baseEnd_2481283] using wordTrace_append hprefix tailTrace_2481283
  have hstable : (prefixWord ++ tailWord_2481283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481283).length < 2 ^ (prefixWord ++ tailWord_2481283).sum := by decide
  have hdescent : baseEnd_2481283 < baseStart_2481283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481343 : List Nat := [1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 4]
def baseStart_2481343 : Nat := 118140960795 + 2481343 * 2 ^ 59
def prefixEnd_2481343 : Nat := 4983230072969 + 3 ^ 40 * 2481343 * 2
def baseEnd_2481343 : Nat := 1274121627669390467801017

theorem tailTrace_2481343 : CollatzResearch.WordTrace tailWord_2481343 prefixEnd_2481343 1274121627669390467801017 := by
  unfold tailWord_2481343
  simp only [CollatzResearch.WordTrace]
  refine ⟨90502014249525565490688683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60334676166350376993792455 90502014249525565490688683)
  ·
    refine ⟨135753021374288348236033025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90502014249525565490688683 135753021374288348236033025)
    ·
      refine ⟨101814766030716261177024769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135753021374288348236033025 101814766030716261177024769)
      ·
        refine ⟨76361074523037195882768577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101814766030716261177024769 76361074523037195882768577)
        ·
          refine ⟨57270805892277896912076433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76361074523037195882768577 57270805892277896912076433)
          ·
            refine ⟨42953104419208422684057325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57270805892277896912076433 42953104419208422684057325)
            ·
              refine ⟨16107414157203158506521497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42953104419208422684057325 16107414157203158506521497)
              ·
                refine ⟨12080560617902368879891123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16107414157203158506521497 12080560617902368879891123)
                ·
                  refine ⟨18120840926853553319836685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12080560617902368879891123 18120840926853553319836685)
                  ·
                    refine ⟨6795315347570082494938757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18120840926853553319836685 6795315347570082494938757)
                    ·
                      refine ⟨1274121627669390467801017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6795315347570082494938757 1274121627669390467801017)
                      ·
                        rfl

theorem cell23_2481343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_2481343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481343 prefixEnd_2481343 := by exact prefixLift 2481343
  have htrace : WordTrace (prefixWord ++ tailWord_2481343) baseStart_2481343 baseEnd_2481343 := by
    simpa [prefixWord, tailWord_2481343, baseEnd_2481343] using wordTrace_append hprefix tailTrace_2481343
  have hstable : (prefixWord ++ tailWord_2481343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481343).length < 2 ^ (prefixWord ++ tailWord_2481343).sum := by decide
  have hdescent : baseEnd_2481343 < baseStart_2481343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481380 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 4, 2, 3]
def baseStart_2481380 : Nat := 118140960795 + 2481380 * 2 ^ 59
def prefixEnd_2481380 : Nat := 4983230072969 + 3 ^ 40 * 2481380 * 2
def baseEnd_2481380 : Nat := 1274140626453606823038347

theorem tailTrace_2481380 : CollatzResearch.WordTrace tailWord_2481380 prefixEnd_2481380 1274140626453606823038347 := by
  unfold tailWord_2481380
  simp only [CollatzResearch.WordTrace]
  refine ⟨45251681875195760404892797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60335575833594347206523729 45251681875195760404892797)
  ·
    refine ⟨16969380703198410151834799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45251681875195760404892797 16969380703198410151834799)
    ·
      refine ⟨25454071054797615227752199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16969380703198410151834799 25454071054797615227752199)
      ·
        refine ⟨38181106582196422841628299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25454071054797615227752199 38181106582196422841628299)
        ·
          refine ⟨57271659873294634262442449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38181106582196422841628299 57271659873294634262442449)
          ·
            refine ⟨42953744904970975696831837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57271659873294634262442449 42953744904970975696831837)
            ·
              refine ⟨16107654339364115886311939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42953744904970975696831837 16107654339364115886311939)
              ·
                refine ⟨24161481509046173829467909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16107654339364115886311939 24161481509046173829467909)
                ·
                  refine ⟨4530277782946157593025233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24161481509046173829467909 4530277782946157593025233)
                  ·
                    refine ⟨3397708337209618194768925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4530277782946157593025233 3397708337209618194768925)
                    ·
                      refine ⟨1274140626453606823038347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3397708337209618194768925 1274140626453606823038347)
                      ·
                        rfl

theorem cell23_2481380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_2481380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481380 prefixEnd_2481380 := by exact prefixLift 2481380
  have htrace : WordTrace (prefixWord ++ tailWord_2481380) baseStart_2481380 baseEnd_2481380 := by
    simpa [prefixWord, tailWord_2481380, baseEnd_2481380] using wordTrace_append hprefix tailTrace_2481380
  have hstable : (prefixWord ++ tailWord_2481380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481380).length < 2 ^ (prefixWord ++ tailWord_2481380).sum := by decide
  have hdescent : baseEnd_2481380 < baseStart_2481380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481387 : List Nat := [1, 1, 1, 1, 2, 8, 1, 1, 3, 4]
def baseStart_2481387 : Nat := 118140960795 + 2481387 * 2 ^ 59
def prefixEnd_2481387 : Nat := 4983230072969 + 3 ^ 40 * 2481387 * 2
def baseEnd_2481387 : Nat := 424714740272729431883605

theorem tailTrace_2481387 : CollatzResearch.WordTrace tailWord_2481387 prefixEnd_2481387 424714740272729431883605 := by
  unfold tailWord_2481387
  simp only [CollatzResearch.WordTrace]
  refine ⟨90503619061366161005290415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60335746040910774003526943 90503619061366161005290415)
  ·
    refine ⟨135755428592049241507935623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90503619061366161005290415 135755428592049241507935623)
    ·
      refine ⟨203633142888073862261903435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135755428592049241507935623 203633142888073862261903435)
      ·
        refine ⟨305449714332110793392855153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203633142888073862261903435 305449714332110793392855153)
        ·
          refine ⟨229087285749083095044641365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305449714332110793392855153 229087285749083095044641365)
          ·
            refine ⟨2684616629872067520054391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 229087285749083095044641365 2684616629872067520054391)
            ·
              refine ⟨4026924944808101280081587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2684616629872067520054391 4026924944808101280081587)
              ·
                refine ⟨6040387417212151920122381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4026924944808101280081587 6040387417212151920122381)
                ·
                  refine ⟨2265145281454556970045893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6040387417212151920122381 2265145281454556970045893)
                  ·
                    refine ⟨424714740272729431883605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2265145281454556970045893 424714740272729431883605)
                    ·
                      rfl

theorem cell23_2481387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3, 4].length) (baseStart_2481387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481387 prefixEnd_2481387 := by exact prefixLift 2481387
  have htrace : WordTrace (prefixWord ++ tailWord_2481387) baseStart_2481387 baseEnd_2481387 := by
    simpa [prefixWord, tailWord_2481387, baseEnd_2481387] using wordTrace_append hprefix tailTrace_2481387
  have hstable : (prefixWord ++ tailWord_2481387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481387).length < 2 ^ (prefixWord ++ tailWord_2481387).sum := by decide
  have hdescent : baseEnd_2481387 < baseStart_2481387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481438 : List Nat := [4, 3, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_2481438 : Nat := 118140960795 + 2481438 * 2 ^ 59
def prefixEnd_2481438 : Nat := 4983230072969 + 3 ^ 40 * 2481438 * 2
def baseEnd_2481438 : Nat := 424723469443855865371027

theorem tailTrace_2481438 : CollatzResearch.WordTrace tailWord_2481438 prefixEnd_2481438 424723469443855865371027 := by
  unfold tailWord_2481438
  simp only [CollatzResearch.WordTrace]
  refine ⟨11313184898022674589424621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60336986122787597810264645 11313184898022674589424621)
  ·
    refine ⟨4242444336758502971034233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11313184898022674589424621 4242444336758502971034233)
    ·
      refine ⟨3181833252568877228275675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4242444336758502971034233 3181833252568877228275675)
      ·
        refine ⟨4772749878853315842413513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3181833252568877228275675 4772749878853315842413513)
        ·
          refine ⟨3579562409139986881810135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4772749878853315842413513 3579562409139986881810135)
          ·
            refine ⟨5369343613709980322715203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3579562409139986881810135 5369343613709980322715203)
            ·
              refine ⟨8054015420564970484072805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5369343613709980322715203 8054015420564970484072805)
              ·
                refine ⟨1510127891355931965763651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8054015420564970484072805 1510127891355931965763651)
                ·
                  refine ⟨2265191837033897948645477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1510127891355931965763651 2265191837033897948645477)
                  ·
                    refine ⟨424723469443855865371027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2265191837033897948645477 424723469443855865371027)
                    ·
                      rfl

theorem cell23_2481438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_2481438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481438 prefixEnd_2481438 := by exact prefixLift 2481438
  have htrace : WordTrace (prefixWord ++ tailWord_2481438) baseStart_2481438 baseEnd_2481438 := by
    simpa [prefixWord, tailWord_2481438, baseEnd_2481438] using wordTrace_append hprefix tailTrace_2481438
  have hstable : (prefixWord ++ tailWord_2481438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481438).length < 2 ^ (prefixWord ++ tailWord_2481438).sum := by decide
  have hdescent : baseEnd_2481438 < baseStart_2481438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481483 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 7]
def baseStart_2481483 : Nat := 118140960795 + 2481483 * 2 ^ 59
def prefixEnd_2481483 : Nat := 4983230072969 + 3 ^ 40 * 2481483 * 2
def baseEnd_2481483 : Nat := 1274193514961019920050373

theorem tailTrace_2481483 : CollatzResearch.WordTrace tailWord_2481483 prefixEnd_2481483 1274193514961019920050373 := by
  unfold tailWord_2481483
  simp only [CollatzResearch.WordTrace]
  refine ⟨90507120469018369400785103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60338080312678912933856735 90507120469018369400785103)
  ·
    refine ⟨135760680703527554101177655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90507120469018369400785103 135760680703527554101177655)
    ·
      refine ⟨203641021055291331151766483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135760680703527554101177655 203641021055291331151766483)
      ·
        refine ⟨305461531582936996727649725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203641021055291331151766483 305461531582936996727649725)
        ·
          refine ⟨114548074343601373772868647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 305461531582936996727649725 114548074343601373772868647)
          ·
            refine ⟨171822111515402060659302971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114548074343601373772868647 171822111515402060659302971)
            ·
              refine ⟨257733167273103090988954457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171822111515402060659302971 257733167273103090988954457)
              ·
                refine ⟨193299875454827318241715843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 257733167273103090988954457 193299875454827318241715843)
                ·
                  refine ⟨289949813182240977362573765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 193299875454827318241715843 289949813182240977362573765)
                  ·
                    refine ⟨54365589971670183255482581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 289949813182240977362573765 54365589971670183255482581)
                    ·
                      refine ⟨1274193514961019920050373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54365589971670183255482581 1274193514961019920050373)
                      ·
                        rfl

theorem cell23_2481483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 7].length) (baseStart_2481483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481483 prefixEnd_2481483 := by exact prefixLift 2481483
  have htrace : WordTrace (prefixWord ++ tailWord_2481483) baseStart_2481483 baseEnd_2481483 := by
    simpa [prefixWord, tailWord_2481483, baseEnd_2481483] using wordTrace_append hprefix tailTrace_2481483
  have hstable : (prefixWord ++ tailWord_2481483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481483).length < 2 ^ (prefixWord ++ tailWord_2481483).sum := by decide
  have hdescent : baseEnd_2481483 < baseStart_2481483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481484 : List Nat := [2, 2, 1, 3, 2, 2, 4, 1, 1, 1, 4]
def baseStart_2481484 : Nat := 118140960795 + 2481484 * 2 ^ 59
def prefixEnd_2481484 : Nat := 4983230072969 + 3 ^ 40 * 2481484 * 2
def baseEnd_2481484 : Nat := 1274194028441674416137869

theorem tailTrace_2481484 : CollatzResearch.WordTrace tailWord_2481484 prefixEnd_2481484 1274194028441674416137869 := by
  unfold tailWord_2481484
  simp only [CollatzResearch.WordTrace]
  refine ⟨45253578471007373285785753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60338104628009831047714337 45253578471007373285785753)
  ·
    refine ⟨33940183853255529964339315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45253578471007373285785753 33940183853255529964339315)
    ·
      refine ⟨50910275779883294946508973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33940183853255529964339315 50910275779883294946508973)
      ·
        refine ⟨19091353417456235604940865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50910275779883294946508973 19091353417456235604940865)
        ·
          refine ⟨14318515063092176703705649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19091353417456235604940865 14318515063092176703705649)
          ·
            refine ⟨10738886297319132527779237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14318515063092176703705649 10738886297319132527779237)
            ·
              refine ⟨2013541180747337348958607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10738886297319132527779237 2013541180747337348958607)
              ·
                refine ⟨3020311771121006023437911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2013541180747337348958607 3020311771121006023437911)
                ·
                  refine ⟨4530467656681509035156867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3020311771121006023437911 4530467656681509035156867)
                  ·
                    refine ⟨6795701485022263552735301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4530467656681509035156867 6795701485022263552735301)
                    ·
                      refine ⟨1274194028441674416137869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6795701485022263552735301 1274194028441674416137869)
                      ·
                        rfl

theorem cell23_2481484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_2481484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481484 prefixEnd_2481484 := by exact prefixLift 2481484
  have htrace : WordTrace (prefixWord ++ tailWord_2481484) baseStart_2481484 baseEnd_2481484 := by
    simpa [prefixWord, tailWord_2481484, baseEnd_2481484] using wordTrace_append hprefix tailTrace_2481484
  have hstable : (prefixWord ++ tailWord_2481484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481484).length < 2 ^ (prefixWord ++ tailWord_2481484).sum := by decide
  have hdescent : baseEnd_2481484 < baseStart_2481484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481511 : List Nat := [1, 1, 5, 1, 4, 1, 3, 1, 2, 4]
def baseStart_2481511 : Nat := 118140960795 + 2481511 * 2 ^ 59
def prefixEnd_2481511 : Nat := 4983230072969 + 3 ^ 40 * 2481511 * 2
def baseEnd_2481511 : Nat := 424735964139781936833415

theorem tailTrace_2481511 : CollatzResearch.WordTrace tailWord_2481511 prefixEnd_2481511 424735964139781936833415 := by
  unfold tailWord_2481511
  simp only [CollatzResearch.WordTrace]
  refine ⟨90508141712916930182804387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60338761141944620121869591 90508141712916930182804387)
  ·
    refine ⟨135762212569375395274206581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90508141712916930182804387 135762212569375395274206581)
    ·
      refine ⟨12727707428378943306956867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135762212569375395274206581 12727707428378943306956867)
      ·
        refine ⟨19091561142568414960435301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12727707428378943306956867 19091561142568414960435301)
        ·
          refine ⟨3579667714231577805081619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19091561142568414960435301 3579667714231577805081619)
          ·
            refine ⟨5369501571347366707622429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3579667714231577805081619 5369501571347366707622429)
            ·
              refine ⟨2013563089255262515358411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5369501571347366707622429 2013563089255262515358411)
              ·
                refine ⟨3020344633882893773037617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2013563089255262515358411 3020344633882893773037617)
                ·
                  refine ⟨2265258475412170329778213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3020344633882893773037617 2265258475412170329778213)
                  ·
                    refine ⟨424735964139781936833415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2265258475412170329778213 424735964139781936833415)
                    ·
                      rfl

theorem cell23_2481511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_2481511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481511 prefixEnd_2481511 := by exact prefixLift 2481511
  have htrace : WordTrace (prefixWord ++ tailWord_2481511) baseStart_2481511 baseEnd_2481511 := by
    simpa [prefixWord, tailWord_2481511, baseEnd_2481511] using wordTrace_append hprefix tailTrace_2481511
  have hstable : (prefixWord ++ tailWord_2481511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481511).length < 2 ^ (prefixWord ++ tailWord_2481511).sum := by decide
  have hdescent : baseEnd_2481511 < baseStart_2481511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481580 : List Nat := [2, 2, 1, 1, 1, 1, 4, 4, 7]
def baseStart_2481580 : Nat := 118140960795 + 2481580 * 2 ^ 59
def prefixEnd_2481580 : Nat := 4983230072969 + 3 ^ 40 * 2481580 * 2
def baseEnd_2481580 : Nat := 141582591398278448948603

theorem tailTrace_2481580 : CollatzResearch.WordTrace tailWord_2481580 prefixEnd_2481580 141582591398278448948603 := by
  unfold tailWord_2481580
  simp only [CollatzResearch.WordTrace]
  refine ⟨45255329174833477483533097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60340438899777969978044129 45255329174833477483533097)
  ·
    refine ⟨33941496881125108112649823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45255329174833477483533097 33941496881125108112649823)
    ·
      refine ⟨50912245321687662168974735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33941496881125108112649823 50912245321687662168974735)
      ·
        refine ⟨76368367982531493253462103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50912245321687662168974735 76368367982531493253462103)
        ·
          refine ⟨114552551973797239880193155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76368367982531493253462103 114552551973797239880193155)
          ·
            refine ⟨171828827960695859820289733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114552551973797239880193155 171828827960695859820289733)
            ·
              refine ⟨32217905242630473716304325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 171828827960695859820289733 32217905242630473716304325)
              ·
                refine ⟨6040857232993213821807061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32217905242630473716304325 6040857232993213821807061)
                ·
                  refine ⟨141582591398278448948603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6040857232993213821807061 141582591398278448948603)
                  ·
                    rfl

theorem cell23_2481580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 7].length) (baseStart_2481580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481580 prefixEnd_2481580 := by exact prefixLift 2481580
  have htrace : WordTrace (prefixWord ++ tailWord_2481580) baseStart_2481580 baseEnd_2481580 := by
    simpa [prefixWord, tailWord_2481580, baseEnd_2481580] using wordTrace_append hprefix tailTrace_2481580
  have hstable : (prefixWord ++ tailWord_2481580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481580).length < 2 ^ (prefixWord ++ tailWord_2481580).sum := by decide
  have hdescent : baseEnd_2481580 < baseStart_2481580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481607 : List Nat := [1, 1, 4, 1, 1, 3, 2, 2, 2, 3, 3]
def baseStart_2481607 : Nat := 118140960795 + 2481607 * 2 ^ 59
def prefixEnd_2481607 : Nat := 4983230072969 + 3 ^ 40 * 2481607 * 2
def baseEnd_2481607 : Nat := 1274257186562177434899803

theorem tailTrace_2481607 : CollatzResearch.WordTrace tailWord_2481607 prefixEnd_2481607 1274257186562177434899803 := by
  unfold tailWord_2481607
  simp only [CollatzResearch.WordTrace]
  refine ⟨90511643120569138578299075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60341095413712759052199383 90511643120569138578299075)
  ·
    refine ⟨135767464680853707867448613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90511643120569138578299075 135767464680853707867448613)
    ·
      refine ⟨25456399627660070225146615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135767464680853707867448613 25456399627660070225146615)
      ·
        refine ⟨38184599441490105337719923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25456399627660070225146615 38184599441490105337719923)
        ·
          refine ⟨57276899162235158006579885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38184599441490105337719923 57276899162235158006579885)
          ·
            refine ⟨21478837185838184252467457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57276899162235158006579885 21478837185838184252467457)
            ·
              refine ⟨16109127889378638189350593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21478837185838184252467457 16109127889378638189350593)
              ·
                refine ⟨12081845917033978642012945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16109127889378638189350593 12081845917033978642012945)
                ·
                  refine ⟨9061384437775483981509709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12081845917033978642012945 9061384437775483981509709)
                  ·
                    refine ⟨3398019164165806493066141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9061384437775483981509709 3398019164165806493066141)
                    ·
                      refine ⟨1274257186562177434899803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3398019164165806493066141 1274257186562177434899803)
                      ·
                        rfl

theorem cell23_2481607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_2481607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481607 prefixEnd_2481607 := by exact prefixLift 2481607
  have htrace : WordTrace (prefixWord ++ tailWord_2481607) baseStart_2481607 baseEnd_2481607 := by
    simpa [prefixWord, tailWord_2481607, baseEnd_2481607] using wordTrace_append hprefix tailTrace_2481607
  have hstable : (prefixWord ++ tailWord_2481607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481607).length < 2 ^ (prefixWord ++ tailWord_2481607).sum := by decide
  have hdescent : baseEnd_2481607 < baseStart_2481607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481657 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 7, 4]
def baseStart_2481657 : Nat := 118140960795 + 2481657 * 2 ^ 59
def prefixEnd_2481657 : Nat := 4983230072969 + 3 ^ 40 * 2481657 * 2
def baseEnd_2481657 : Nat := 424760953531634079758191

theorem tailTrace_2481657 : CollatzResearch.WordTrace tailWord_2481657 prefixEnd_2481657 424760953531634079758191 := by
  unfold tailWord_2481657
  simp only [CollatzResearch.WordTrace]
  refine ⟨90513466770387997117619225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60342311180258664745079483 90513466770387997117619225)
  ·
    refine ⟨67885100077790997838214419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90513466770387997117619225 67885100077790997838214419)
    ·
      refine ⟨101827650116686496757321629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67885100077790997838214419 101827650116686496757321629)
      ·
        refine ⟨38185368793757436283995611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101827650116686496757321629 38185368793757436283995611)
        ·
          refine ⟨57278053190636154425993417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38185368793757436283995611 57278053190636154425993417)
          ·
            refine ⟨42958539892977115819495063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57278053190636154425993417 42958539892977115819495063)
            ·
              refine ⟨64437809839465673729242595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42958539892977115819495063 64437809839465673729242595)
              ·
                refine ⟨96656714759198510593863893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64437809839465673729242595 96656714759198510593863893)
                ·
                  refine ⟨2265391752168715092043685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 96656714759198510593863893 2265391752168715092043685)
                  ·
                    refine ⟨424760953531634079758191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2265391752168715092043685 424760953531634079758191)
                    ·
                      rfl

theorem cell23_2481657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7, 4].length) (baseStart_2481657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481657 prefixEnd_2481657 := by exact prefixLift 2481657
  have htrace : WordTrace (prefixWord ++ tailWord_2481657) baseStart_2481657 baseEnd_2481657 := by
    simpa [prefixWord, tailWord_2481657, baseEnd_2481657] using wordTrace_append hprefix tailTrace_2481657
  have hstable : (prefixWord ++ tailWord_2481657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481657).length < 2 ^ (prefixWord ++ tailWord_2481657).sum := by decide
  have hdescent : baseEnd_2481657 < baseStart_2481657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481674 : List Nat := [3, 1, 2, 2, 2, 2, 1, 3, 3, 4]
def baseStart_2481674 : Nat := 118140960795 + 2481674 * 2 ^ 59
def prefixEnd_2481674 : Nat := 4983230072969 + 3 ^ 40 * 2481674 * 2
def baseEnd_2481674 : Nat := 424763863255342890920665

theorem tailTrace_2481674 : CollatzResearch.WordTrace tailWord_2481674 prefixEnd_2481674 424763863255342890920665 := by
  unfold tailWord_2481674
  simp only [CollatzResearch.WordTrace]
  refine ⟨22628521702831602255247019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60342724540884272680658717 22628521702831602255247019)
  ·
    refine ⟨33942782554247403382870529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22628521702831602255247019 33942782554247403382870529)
    ·
      refine ⟨25457086915685552537152897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33942782554247403382870529 25457086915685552537152897)
      ·
        refine ⟨19092815186764164402864673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25457086915685552537152897 19092815186764164402864673)
        ·
          refine ⟨14319611390073123302148505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19092815186764164402864673 14319611390073123302148505)
          ·
            refine ⟨10739708542554842476611379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14319611390073123302148505 10739708542554842476611379)
            ·
              refine ⟨16109562813832263714917069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10739708542554842476611379 16109562813832263714917069)
              ·
                refine ⟨6041086055187098893093901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16109562813832263714917069 6041086055187098893093901)
                ·
                  refine ⟨2265407270695162084910213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6041086055187098893093901 2265407270695162084910213)
                  ·
                    refine ⟨424763863255342890920665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2265407270695162084910213 424763863255342890920665)
                    ·
                      rfl

theorem cell23_2481674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_2481674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481674 prefixEnd_2481674 := by exact prefixLift 2481674
  have htrace : WordTrace (prefixWord ++ tailWord_2481674) baseStart_2481674 baseEnd_2481674 := by
    simpa [prefixWord, tailWord_2481674, baseEnd_2481674] using wordTrace_append hprefix tailTrace_2481674
  have hstable : (prefixWord ++ tailWord_2481674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481674).length < 2 ^ (prefixWord ++ tailWord_2481674).sum := by decide
  have hdescent : baseEnd_2481674 < baseStart_2481674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481718 : List Nat := [5, 1, 2, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_2481718 : Nat := 118140960795 + 2481718 * 2 ^ 59
def prefixEnd_2481718 : Nat := 4983230072969 + 3 ^ 40 * 2481718 * 2
def baseEnd_2481718 : Nat := 1274314182914826500611793

theorem tailTrace_2481718 : CollatzResearch.WordTrace tailWord_2481718 prefixEnd_2481718 1274314182914826500611793 := by
  unfold tailWord_2481718
  simp only [CollatzResearch.WordTrace]
  refine ⟨5657230726447937783474363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60343794415444669690393205 5657230726447937783474363)
  ·
    refine ⟨8485846089671906675211545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5657230726447937783474363 8485846089671906675211545)
    ·
      refine ⟨6364384567253930006408659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8485846089671906675211545 6364384567253930006408659)
      ·
        refine ⟨9546576850880895009612989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6364384567253930006408659 9546576850880895009612989)
        ·
          refine ⟨3579966319080335628604871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9546576850880895009612989 3579966319080335628604871)
          ·
            refine ⟨5369949478620503442907307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3579966319080335628604871 5369949478620503442907307)
            ·
              refine ⟨8054924217930755164360961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5369949478620503442907307 8054924217930755164360961)
              ·
                refine ⟨6041193163448066373270721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8054924217930755164360961 6041193163448066373270721)
                ·
                  refine ⟨4530894872586049779953041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6041193163448066373270721 4530894872586049779953041)
                  ·
                    refine ⟨3398171154439537334964781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4530894872586049779953041 3398171154439537334964781)
                    ·
                      refine ⟨1274314182914826500611793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3398171154439537334964781 1274314182914826500611793)
                      ·
                        rfl

theorem cell23_2481718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_2481718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481718 prefixEnd_2481718 := by exact prefixLift 2481718
  have htrace : WordTrace (prefixWord ++ tailWord_2481718) baseStart_2481718 baseEnd_2481718 := by
    simpa [prefixWord, tailWord_2481718, baseEnd_2481718] using wordTrace_append hprefix tailTrace_2481718
  have hstable : (prefixWord ++ tailWord_2481718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481718).length < 2 ^ (prefixWord ++ tailWord_2481718).sum := by decide
  have hdescent : baseEnd_2481718 < baseStart_2481718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481725 : List Nat := [1, 4, 1, 3, 3, 1, 3, 2, 1, 4]
def baseStart_2481725 : Nat := 118140960795 + 2481725 * 2 ^ 59
def prefixEnd_2481725 : Nat := 4983230072969 + 3 ^ 40 * 2481725 * 2
def baseEnd_2481725 : Nat := 424772592426469324408087

theorem tailTrace_2481725 : CollatzResearch.WordTrace tailWord_2481725 prefixEnd_2481725 424772592426469324408087 := by
  unfold tailWord_2481725
  simp only [CollatzResearch.WordTrace]
  refine ⟨90515946934141644731094629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60343964622761096487396419 90515946934141644731094629)
  ·
    refine ⟨16971740050151558387080243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90515946934141644731094629 16971740050151558387080243)
    ·
      refine ⟨25457610075227337580620365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16971740050151558387080243 25457610075227337580620365)
      ·
        refine ⟨9546603778210251592732637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25457610075227337580620365 9546603778210251592732637)
        ·
          refine ⟨3579976416828844347274739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9546603778210251592732637 3579976416828844347274739)
          ·
            refine ⟨5369964625243266520912109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3579976416828844347274739 5369964625243266520912109)
            ·
              refine ⟨2013736734466224945342041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5369964625243266520912109 2013736734466224945342041)
              ·
                refine ⟨1510302550849668709006531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2013736734466224945342041 1510302550849668709006531)
                ·
                  refine ⟨2265453826274503063509797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1510302550849668709006531 2265453826274503063509797)
                  ·
                    refine ⟨424772592426469324408087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2265453826274503063509797 424772592426469324408087)
                    ·
                      rfl

theorem cell23_2481725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_2481725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481725 prefixEnd_2481725 := by exact prefixLift 2481725
  have htrace : WordTrace (prefixWord ++ tailWord_2481725) baseStart_2481725 baseEnd_2481725 := by
    simpa [prefixWord, tailWord_2481725, baseEnd_2481725] using wordTrace_append hprefix tailTrace_2481725
  have hstable : (prefixWord ++ tailWord_2481725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481725).length < 2 ^ (prefixWord ++ tailWord_2481725).sum := by decide
  have hdescent : baseEnd_2481725 < baseStart_2481725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481751 : List Nat := [1, 1, 3, 2, 2, 5, 1, 2, 1, 5]
def baseStart_2481751 : Nat := 118140960795 + 2481751 * 2 ^ 59
def prefixEnd_2481751 : Nat := 4983230072969 + 3 ^ 40 * 2481751 * 2
def baseEnd_2481751 : Nat := 424777042592141623833047

theorem tailTrace_2481751 : CollatzResearch.WordTrace tailWord_2481751 prefixEnd_2481751 424777042592141623833047 := by
  unfold tailWord_2481751
  simp only [CollatzResearch.WordTrace]
  refine ⟨90516895232047451171541107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60344596821364967447694071 90516895232047451171541107)
  ·
    refine ⟨135775342848071176757311661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90516895232047451171541107 135775342848071176757311661)
    ·
      refine ⟨50915753568026691283991873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135775342848071176757311661 50915753568026691283991873)
      ·
        refine ⟨38186815176020018462993905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50915753568026691283991873 38186815176020018462993905)
        ·
          refine ⟨28640111382015013847245429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38186815176020018462993905 28640111382015013847245429)
          ·
            refine ⟨2685010442063907548179259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28640111382015013847245429 2685010442063907548179259)
            ·
              refine ⟨4027515663095861322268889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2685010442063907548179259 4027515663095861322268889)
              ·
                refine ⟨3020636747321895991701667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4027515663095861322268889 3020636747321895991701667)
                ·
                  refine ⟨4530955120982843987552501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3020636747321895991701667 4530955120982843987552501)
                  ·
                    refine ⟨424777042592141623833047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4530955120982843987552501 424777042592141623833047)
                    ·
                      rfl

theorem cell23_2481751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 5].length) (baseStart_2481751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481751 prefixEnd_2481751 := by exact prefixLift 2481751
  have htrace : WordTrace (prefixWord ++ tailWord_2481751) baseStart_2481751 baseEnd_2481751 := by
    simpa [prefixWord, tailWord_2481751, baseEnd_2481751] using wordTrace_append hprefix tailTrace_2481751
  have hstable : (prefixWord ++ tailWord_2481751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481751).length < 2 ^ (prefixWord ++ tailWord_2481751).sum := by decide
  have hdescent : baseEnd_2481751 < baseStart_2481751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481754 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2]
def baseStart_2481754 : Nat := 118140960795 + 2481754 * 2 ^ 59
def prefixEnd_2481754 : Nat := 4983230072969 + 3 ^ 40 * 2481754 * 2
def baseEnd_2481754 : Nat := 1274332668218388359761627

theorem tailTrace_2481754 : CollatzResearch.WordTrace tailWord_2481754 prefixEnd_2481754 1274332668218388359761627 := by
  unfold tailWord_2481754
  simp only [CollatzResearch.WordTrace]
  refine ⟨22629251162759145670975079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60344669767357721789266877 22629251162759145670975079)
  ·
    refine ⟨33943876744138718506462619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22629251162759145670975079 33943876744138718506462619)
    ·
      refine ⟨50915815116208077759693929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33943876744138718506462619 50915815116208077759693929)
      ·
        refine ⟨38186861337156058319770447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50915815116208077759693929 38186861337156058319770447)
        ·
          refine ⟨57280292005734087479655671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38186861337156058319770447 57280292005734087479655671)
          ·
            refine ⟨85920438008601131219483507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57280292005734087479655671 85920438008601131219483507)
            ·
              refine ⟨128880657012901696829225261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85920438008601131219483507 128880657012901696829225261)
              ·
                refine ⟨48330246379838136310959473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128880657012901696829225261 48330246379838136310959473)
                ·
                  refine ⟨36247684784878602233219605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48330246379838136310959473 36247684784878602233219605)
                  ·
                    refine ⟨1699110224291184479682169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 36247684784878602233219605 1699110224291184479682169)
                    ·
                      refine ⟨1274332668218388359761627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1699110224291184479682169 1274332668218388359761627)
                      ·
                        rfl

theorem cell23_2481754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2].length) (baseStart_2481754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481754 prefixEnd_2481754 := by exact prefixLift 2481754
  have htrace : WordTrace (prefixWord ++ tailWord_2481754) baseStart_2481754 baseEnd_2481754 := by
    simpa [prefixWord, tailWord_2481754, baseEnd_2481754] using wordTrace_append hprefix tailTrace_2481754
  have hstable : (prefixWord ++ tailWord_2481754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481754).length < 2 ^ (prefixWord ++ tailWord_2481754).sum := by decide
  have hdescent : baseEnd_2481754 < baseStart_2481754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481764 : List Nat := [2, 3, 1, 1, 2, 4, 1, 2, 1, 6]
def baseStart_2481764 : Nat := 118140960795 + 2481764 * 2 ^ 59
def prefixEnd_2481764 : Nat := 4983230072969 + 3 ^ 40 * 2481764 * 2
def baseEnd_2481764 : Nat := 424779267674977773545527

theorem tailTrace_2481764 : CollatzResearch.WordTrace tailWord_2481764 prefixEnd_2481764 424779267674977773545527 := by
  unfold tailWord_2481764
  simp only [CollatzResearch.WordTrace]
  refine ⟨45258684690500177195882173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60344912920666902927842897 45258684690500177195882173)
  ·
    refine ⟨16972006758937566448455815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45258684690500177195882173 16972006758937566448455815)
    ·
      refine ⟨25458010138406349672683723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16972006758937566448455815 25458010138406349672683723)
      ·
        refine ⟨38187015207609524509025585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25458010138406349672683723 38187015207609524509025585)
        ·
          refine ⟨28640261405707143381769189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38187015207609524509025585 28640261405707143381769189)
          ·
            refine ⟨5370049013570089384081723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28640261405707143381769189 5370049013570089384081723)
            ·
              refine ⟨8055073520355134076122585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5370049013570089384081723 8055073520355134076122585)
              ·
                refine ⟨6041305140266350557091939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8055073520355134076122585 6041305140266350557091939)
                ·
                  refine ⟨9061957710399525835637909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6041305140266350557091939 9061957710399525835637909)
                  ·
                    refine ⟨424779267674977773545527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9061957710399525835637909 424779267674977773545527)
                    ·
                      rfl

theorem cell23_2481764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_2481764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481764 prefixEnd_2481764 := by exact prefixLift 2481764
  have htrace : WordTrace (prefixWord ++ tailWord_2481764) baseStart_2481764 baseEnd_2481764 := by
    simpa [prefixWord, tailWord_2481764, baseEnd_2481764] using wordTrace_append hprefix tailTrace_2481764
  have hstable : (prefixWord ++ tailWord_2481764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481764).length < 2 ^ (prefixWord ++ tailWord_2481764).sum := by decide
  have hdescent : baseEnd_2481764 < baseStart_2481764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481768 : List Nat := [2, 1, 4, 3, 1, 2, 3, 1, 1, 5]
def baseStart_2481768 : Nat := 118140960795 + 2481768 * 2 ^ 59
def prefixEnd_2481768 : Nat := 4983230072969 + 3 ^ 40 * 2481768 * 2
def baseEnd_2481768 : Nat := 424779952315850434995521

theorem tailTrace_2481768 : CollatzResearch.WordTrace tailWord_2481768 prefixEnd_2481768 424779952315850434995521 := by
  unfold tailWord_2481768
  simp only [CollatzResearch.WordTrace]
  refine ⟨45258757636492931537454979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60345010181990575383273305 45258757636492931537454979)
  ·
    refine ⟨67888136454739397306182469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45258757636492931537454979 67888136454739397306182469)
    ·
      refine ⟨12729025585263636994909213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67888136454739397306182469 12729025585263636994909213)
      ·
        refine ⟨4773384594473863873090955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12729025585263636994909213 4773384594473863873090955)
        ·
          refine ⟨7160076891710795809636433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4773384594473863873090955 7160076891710795809636433)
          ·
            refine ⟨5370057668783096857227325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7160076891710795809636433 5370057668783096857227325)
            ·
              refine ⟨2013771625793661321460247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5370057668783096857227325 2013771625793661321460247)
              ·
                refine ⟨3020657438690491982190371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2013771625793661321460247 3020657438690491982190371)
                ·
                  refine ⟨4530986158035737973285557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3020657438690491982190371 4530986158035737973285557)
                  ·
                    refine ⟨424779952315850434995521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4530986158035737973285557 424779952315850434995521)
                    ·
                      rfl

theorem cell23_2481768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_2481768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481768 prefixEnd_2481768 := by exact prefixLift 2481768
  have htrace : WordTrace (prefixWord ++ tailWord_2481768) baseStart_2481768 baseEnd_2481768 := by
    simpa [prefixWord, tailWord_2481768, baseEnd_2481768] using wordTrace_append hprefix tailTrace_2481768
  have hstable : (prefixWord ++ tailWord_2481768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481768).length < 2 ^ (prefixWord ++ tailWord_2481768).sum := by decide
  have hdescent : baseEnd_2481768 < baseStart_2481768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481782 : List Nat := [5, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3]
def baseStart_2481782 : Nat := 118140960795 + 2481782 * 2 ^ 59
def prefixEnd_2481782 : Nat := 4983230072969 + 3 ^ 40 * 2481782 * 2
def baseEnd_2481782 : Nat := 1274347045676714250211499

theorem tailTrace_2481782 : CollatzResearch.WordTrace tailWord_2481782 prefixEnd_2481782 1274347045676714250211499 := by
  unfold tailWord_2481782
  simp only [CollatzResearch.WordTrace]
  refine ⟨5657376618433446466619975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60345350596623428977279733 5657376618433446466619975)
  ·
    refine ⟨8486064927650169699929963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5657376618433446466619975 8486064927650169699929963)
    ·
      refine ⟨12729097391475254549894945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8486064927650169699929963 12729097391475254549894945)
      ·
        refine ⟨9546823043606440912421209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12729097391475254549894945 9546823043606440912421209)
        ·
          refine ⟨7160117282704830684315907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9546823043606440912421209 7160117282704830684315907)
          ·
            refine ⟨10740175924057246026473861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7160117282704830684315907 10740175924057246026473861)
            ·
              refine ⟨2013782985760733629963849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10740175924057246026473861 2013782985760733629963849)
              ·
                refine ⟨1510337239320550222472887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2013782985760733629963849 1510337239320550222472887)
                ·
                  refine ⟨2265505858980825333709331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1510337239320550222472887 2265505858980825333709331)
                  ·
                    refine ⟨3398258788471238000563997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2265505858980825333709331 3398258788471238000563997)
                    ·
                      refine ⟨1274347045676714250211499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3398258788471238000563997 1274347045676714250211499)
                      ·
                        rfl

theorem cell23_2481782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_2481782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481782 prefixEnd_2481782 := by exact prefixLift 2481782
  have htrace : WordTrace (prefixWord ++ tailWord_2481782) baseStart_2481782 baseEnd_2481782 := by
    simpa [prefixWord, tailWord_2481782, baseEnd_2481782] using wordTrace_append hprefix tailTrace_2481782
  have hstable : (prefixWord ++ tailWord_2481782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481782).length < 2 ^ (prefixWord ++ tailWord_2481782).sum := by decide
  have hdescent : baseEnd_2481782 < baseStart_2481782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481821 : List Nat := [1, 4, 2, 1, 1, 1, 1, 4, 4, 1, 3]
def baseStart_2481821 : Nat := 118140960795 + 2481821 * 2 ^ 59
def prefixEnd_2481821 : Nat := 4983230072969 + 3 ^ 40 * 2481821 * 2
def baseEnd_2481821 : Nat := 1274367071422239597623819

theorem tailTrace_2481821 : CollatzResearch.WordTrace tailWord_2481821 prefixEnd_2481821 1274367071422239597623819 := by
  unfold tailWord_2481821
  simp only [CollatzResearch.WordTrace]
  refine ⟨90519448341793853126589317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60346298894529235417726211 90519448341793853126589317)
  ·
    refine ⟨16972396564086347461235497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90519448341793853126589317 16972396564086347461235497)
    ·
      refine ⟨12729297423064760595926623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16972396564086347461235497 12729297423064760595926623)
      ·
        refine ⟨19093946134597140893889935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12729297423064760595926623 19093946134597140893889935)
        ·
          refine ⟨28640919201895711340834903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19093946134597140893889935 28640919201895711340834903)
          ·
            refine ⟨42961378802843567011252355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28640919201895711340834903 42961378802843567011252355)
            ·
              refine ⟨64442068204265350516878533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42961378802843567011252355 64442068204265350516878533)
              ·
                refine ⟨12082887788299753221914725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64442068204265350516878533 12082887788299753221914725)
                ·
                  refine ⟨2265541460306203729109011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12082887788299753221914725 2265541460306203729109011)
                  ·
                    refine ⟨3398312190459305593663517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2265541460306203729109011 3398312190459305593663517)
                    ·
                      refine ⟨1274367071422239597623819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3398312190459305593663517 1274367071422239597623819)
                      ·
                        rfl

theorem cell23_2481821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_2481821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481821 prefixEnd_2481821 := by exact prefixLift 2481821
  have htrace : WordTrace (prefixWord ++ tailWord_2481821) baseStart_2481821 baseEnd_2481821 := by
    simpa [prefixWord, tailWord_2481821, baseEnd_2481821] using wordTrace_append hprefix tailTrace_2481821
  have hstable : (prefixWord ++ tailWord_2481821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481821).length < 2 ^ (prefixWord ++ tailWord_2481821).sum := by decide
  have hdescent : baseEnd_2481821 < baseStart_2481821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481822 : List Nat := [4, 3, 1, 1, 1, 2, 1, 5, 1, 2, 2]
def baseStart_2481822 : Nat := 118140960795 + 2481822 * 2 ^ 59
def prefixEnd_2481822 : Nat := 4983230072969 + 3 ^ 40 * 2481822 * 2
def baseEnd_2481822 : Nat := 1274367584902894093711315

theorem tailTrace_2481822 : CollatzResearch.WordTrace tailWord_2481822 prefixEnd_2481822 1274367584902894093711315 := by
  unfold tailWord_2481822
  simp only [CollatzResearch.WordTrace]
  refine ⟨11314935601848778787171965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60346323209860153531583813 11314935601848778787171965)
  ·
    refine ⟨4243100850693292045189487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11314935601848778787171965 4243100850693292045189487)
    ·
      refine ⟨6364651276039938067784231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4243100850693292045189487 6364651276039938067784231)
      ·
        refine ⟨9546976914059907101676347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6364651276039938067784231 9546976914059907101676347)
        ·
          refine ⟨14320465371089860652514521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9546976914059907101676347 14320465371089860652514521)
          ·
            refine ⟨10740349028317395489385891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14320465371089860652514521 10740349028317395489385891)
            ·
              refine ⟨16110523542476093234078837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10740349028317395489385891 16110523542476093234078837)
              ·
                refine ⟨1510361582107133740694891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16110523542476093234078837 1510361582107133740694891)
                ·
                  refine ⟨2265542373160700611042337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1510361582107133740694891 2265542373160700611042337)
                  ·
                    refine ⟨1699156779870525458281753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2265542373160700611042337 1699156779870525458281753)
                    ·
                      refine ⟨1274367584902894093711315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1699156779870525458281753 1274367584902894093711315)
                      ·
                        rfl

theorem cell23_2481822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_2481822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481822 prefixEnd_2481822 := by exact prefixLift 2481822
  have htrace : WordTrace (prefixWord ++ tailWord_2481822) baseStart_2481822 baseEnd_2481822 := by
    simpa [prefixWord, tailWord_2481822, baseEnd_2481822] using wordTrace_append hprefix tailTrace_2481822
  have hstable : (prefixWord ++ tailWord_2481822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481822).length < 2 ^ (prefixWord ++ tailWord_2481822).sum := by decide
  have hdescent : baseEnd_2481822 < baseStart_2481822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481825 : List Nat := [1, 2, 3, 3, 2, 3, 2, 1, 1, 2, 3]
def baseStart_2481825 : Nat := 118140960795 + 2481825 * 2 ^ 59
def prefixEnd_2481825 : Nat := 4983230072969 + 3 ^ 40 * 2481825 * 2
def baseEnd_2481825 : Nat := 1274369125344857581973801

theorem tailTrace_2481825 : CollatzResearch.WordTrace tailWord_2481825 prefixEnd_2481825 1274369125344857581973801 := by
  unfold tailWord_2481825
  simp only [CollatzResearch.WordTrace]
  refine ⟨90519594233779361809734929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60346396155852907873156619 90519594233779361809734929)
  ·
    refine ⟨67889695675334521357301197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90519594233779361809734929 67889695675334521357301197)
    ·
      refine ⟨25458635878250445508987949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67889695675334521357301197 25458635878250445508987949)
      ·
        refine ⟨9546988454343917065870481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25458635878250445508987949 9546988454343917065870481)
        ·
          refine ⟨7160241340757937799402861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9546988454343917065870481 7160241340757937799402861)
          ·
            refine ⟨2685090502784226674776073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7160241340757937799402861 2685090502784226674776073)
            ·
              refine ⟨2013817877088170006082055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2685090502784226674776073 2013817877088170006082055)
              ·
                refine ⟨3020726815632255009123083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2013817877088170006082055 3020726815632255009123083)
                ·
                  refine ⟨4531090223448382513684625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3020726815632255009123083 4531090223448382513684625)
                  ·
                    refine ⟨3398317667586286885263469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4531090223448382513684625 3398317667586286885263469)
                    ·
                      refine ⟨1274369125344857581973801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3398317667586286885263469 1274369125344857581973801)
                      ·
                        rfl

theorem cell23_2481825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_2481825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481825 prefixEnd_2481825 := by exact prefixLift 2481825
  have htrace : WordTrace (prefixWord ++ tailWord_2481825) baseStart_2481825 baseEnd_2481825 := by
    simpa [prefixWord, tailWord_2481825, baseEnd_2481825] using wordTrace_append hprefix tailTrace_2481825
  have hstable : (prefixWord ++ tailWord_2481825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481825).length < 2 ^ (prefixWord ++ tailWord_2481825).sum := by decide
  have hdescent : baseEnd_2481825 < baseStart_2481825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481864 : List Nat := [2, 1, 3, 1, 2, 2, 2, 2, 2, 1, 5]
def baseStart_2481864 : Nat := 118140960795 + 2481864 * 2 ^ 59
def prefixEnd_2481864 : Nat := 4983230072969 + 3 ^ 40 * 2481864 * 2
def baseEnd_2481864 : Nat := 1274389151090382929386121

theorem tailTrace_2481864 : CollatzResearch.WordTrace tailWord_2481864 prefixEnd_2481864 1274389151090382929386121 := by
  unfold tailWord_2481864
  simp only [CollatzResearch.WordTrace]
  refine ⟨45260508340319035735202323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60347344453758714313603097 45260508340319035735202323)
  ·
    refine ⟨67890762510478553602803485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45260508340319035735202323 67890762510478553602803485)
    ·
      refine ⟨25459035941429457601051307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67890762510478553602803485 25459035941429457601051307)
      ·
        refine ⟨38188553912144186401576961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25459035941429457601051307 38188553912144186401576961)
        ·
          refine ⟨28641415434108139801182721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38188553912144186401576961 28641415434108139801182721)
          ·
            refine ⟨21481061575581104850887041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28641415434108139801182721 21481061575581104850887041)
            ·
              refine ⟨16110796181685828638165281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21481061575581104850887041 16110796181685828638165281)
              ·
                refine ⟨12083097136264371478623961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16110796181685828638165281 12083097136264371478623961)
                ·
                  refine ⟨9062322852198278608967971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12083097136264371478623961 9062322852198278608967971)
                  ·
                    refine ⟨13593484278297417913451957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9062322852198278608967971 13593484278297417913451957)
                    ·
                      refine ⟨1274389151090382929386121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13593484278297417913451957 1274389151090382929386121)
                      ·
                        rfl

theorem cell23_2481864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_2481864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481864 prefixEnd_2481864 := by exact prefixLift 2481864
  have htrace : WordTrace (prefixWord ++ tailWord_2481864) baseStart_2481864 baseEnd_2481864 := by
    simpa [prefixWord, tailWord_2481864, baseEnd_2481864] using wordTrace_append hprefix tailTrace_2481864
  have hstable : (prefixWord ++ tailWord_2481864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481864).length < 2 ^ (prefixWord ++ tailWord_2481864).sum := by decide
  have hdescent : baseEnd_2481864 < baseStart_2481864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481901 : List Nat := [1, 5, 1, 2, 1, 2, 3, 1, 7]
def baseStart_2481901 : Nat := 118140960795 + 2481901 * 2 ^ 59
def prefixEnd_2481901 : Nat := 4983230072969 + 3 ^ 40 * 2481901 * 2
def baseEnd_2481901 : Nat := 141600905541622142735939

theorem tailTrace_2481901 : CollatzResearch.WordTrace tailWord_2481901 prefixEnd_2481901 141600905541622142735939 := by
  unfold tailWord_2481901
  simp only [CollatzResearch.WordTrace]
  refine ⟨90522366181504026789501557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60348244121002684526334371 90522366181504026789501557)
  ·
    refine ⟨8486471829516002511515771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90522366181504026789501557 8486471829516002511515771)
    ·
      refine ⟨12729707744274003767273657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8486471829516002511515771 12729707744274003767273657)
      ·
        refine ⟨9547280808205502825455243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12729707744274003767273657 9547280808205502825455243)
        ·
          refine ⟨14320921212308254238182865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9547280808205502825455243 14320921212308254238182865)
          ·
            refine ⟨10740690909231190678637149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14320921212308254238182865 10740690909231190678637149)
            ·
              refine ⟨4027759090961696504488931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10740690909231190678637149 4027759090961696504488931)
              ·
                refine ⟨6041638636442544756733397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4027759090961696504488931 6041638636442544756733397)
                ·
                  refine ⟨141600905541622142735939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6041638636442544756733397 141600905541622142735939)
                  ·
                    rfl

theorem cell23_2481901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_2481901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481901 prefixEnd_2481901 := by exact prefixLift 2481901
  have htrace : WordTrace (prefixWord ++ tailWord_2481901) baseStart_2481901 baseEnd_2481901 := by
    simpa [prefixWord, tailWord_2481901, baseEnd_2481901] using wordTrace_append hprefix tailTrace_2481901
  have hstable : (prefixWord ++ tailWord_2481901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481901).length < 2 ^ (prefixWord ++ tailWord_2481901).sum := by decide
  have hdescent : baseEnd_2481901 < baseStart_2481901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481914 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 6, 5]
def baseStart_2481914 : Nat := 118140960795 + 2481914 * 2 ^ 59
def prefixEnd_2481914 : Nat := 4983230072969 + 3 ^ 40 * 2481914 * 2
def baseEnd_2481914 : Nat := 424804941707702577920297

theorem tailTrace_2481914 : CollatzResearch.WordTrace tailWord_2481914 prefixEnd_2481914 424804941707702577920297 := by
  unfold tailWord_2481914
  simp only [CollatzResearch.WordTrace]
  refine ⟨22630710082614232502431199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60348560220304620006483197 22630710082614232502431199)
  ·
    refine ⟨33946065123921348753646799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22630710082614232502431199 33946065123921348753646799)
    ·
      refine ⟨50919097685882023130470199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33946065123921348753646799 50919097685882023130470199)
      ·
        refine ⟨76378646528823034695705299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50919097685882023130470199 76378646528823034695705299)
        ·
          refine ⟨114567969793234552043557949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76378646528823034695705299 114567969793234552043557949)
          ·
            refine ⟨42962988672462957016334231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114567969793234552043557949 42962988672462957016334231)
            ·
              refine ⟨64444483008694435524501347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42962988672462957016334231 64444483008694435524501347)
              ·
                refine ⟨96666724513041653286752021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64444483008694435524501347 96666724513041653286752021)
                ·
                  refine ⟨4531252711548827497816501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 96666724513041653286752021 4531252711548827497816501)
                  ·
                    refine ⟨424804941707702577920297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4531252711548827497816501 424804941707702577920297)
                    ·
                      rfl

theorem cell23_2481914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 6, 5].length) (baseStart_2481914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481914 prefixEnd_2481914 := by exact prefixLift 2481914
  have htrace : WordTrace (prefixWord ++ tailWord_2481914) baseStart_2481914 baseEnd_2481914 := by
    simpa [prefixWord, tailWord_2481914, baseEnd_2481914] using wordTrace_append hprefix tailTrace_2481914
  have hstable : (prefixWord ++ tailWord_2481914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481914).length < 2 ^ (prefixWord ++ tailWord_2481914).sum := by decide
  have hdescent : baseEnd_2481914 < baseStart_2481914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481933 : List Nat := [1, 7, 2, 1, 1, 1, 3, 1, 1, 3, 2]
def baseStart_2481933 : Nat := 118140960795 + 2481933 * 2 ^ 59
def prefixEnd_2481933 : Nat := 4983230072969 + 3 ^ 40 * 2481933 * 2
def baseEnd_2481933 : Nat := 1274424581255543159423305

theorem tailTrace_2481933 : CollatzResearch.WordTrace tailWord_2481933 prefixEnd_2481933 1274424581255543159423305 := by
  unfold tailWord_2481933
  simp only [CollatzResearch.WordTrace]
  refine ⟨90523533317388096254666453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60349022211592064169777635 90523533317388096254666453)
  ·
    refine ⟨2121645312126283505968745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 90523533317388096254666453 2121645312126283505968745)
    ·
      refine ⟨1591233984094712629476559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2121645312126283505968745 1591233984094712629476559)
      ·
        refine ⟨2386850976142068944214839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1591233984094712629476559 2386850976142068944214839)
        ·
          refine ⟨3580276464213103416322259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2386850976142068944214839 3580276464213103416322259)
          ·
            refine ⟨5370414696319655124483389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3580276464213103416322259 5370414696319655124483389)
            ·
              refine ⟨2013905511119870671681271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5370414696319655124483389 2013905511119870671681271)
              ·
                refine ⟨3020858266679806007521907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2013905511119870671681271 3020858266679806007521907)
                ·
                  refine ⟨4531287400019709011282861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3020858266679806007521907 4531287400019709011282861)
                  ·
                    refine ⟨1699232775007390879231073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4531287400019709011282861 1699232775007390879231073)
                    ·
                      refine ⟨1274424581255543159423305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1699232775007390879231073 1274424581255543159423305)
                      ·
                        rfl

theorem cell23_2481933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_2481933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481933 prefixEnd_2481933 := by exact prefixLift 2481933
  have htrace : WordTrace (prefixWord ++ tailWord_2481933) baseStart_2481933 baseEnd_2481933 := by
    simpa [prefixWord, tailWord_2481933, baseEnd_2481933] using wordTrace_append hprefix tailTrace_2481933
  have hstable : (prefixWord ++ tailWord_2481933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481933).length < 2 ^ (prefixWord ++ tailWord_2481933).sum := by decide
  have hdescent : baseEnd_2481933 < baseStart_2481933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481951 : List Nat := [1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 4]
def baseStart_2481951 : Nat := 118140960795 + 2481951 * 2 ^ 59
def prefixEnd_2481951 : Nat := 4983230072969 + 3 ^ 40 * 2481951 * 2
def baseEnd_2481951 : Nat := 1274433823907324088998221

theorem tailTrace_2481951 : CollatzResearch.WordTrace tailWord_2481951 prefixEnd_2481951 1274433823907324088998221 := by
  unfold tailWord_2481951
  simp only [CollatzResearch.WordTrace]
  refine ⟨90524189831322885328821707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60349459887548590219214471 90524189831322885328821707)
  ·
    refine ⟨135786284746984327993232561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90524189831322885328821707 135786284746984327993232561)
    ·
      refine ⟨101839713560238245994924421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135786284746984327993232561 101839713560238245994924421)
      ·
        refine ⟨19094946292544671124048329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101839713560238245994924421 19094946292544671124048329)
        ·
          refine ⟨14321209719408503343036247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19094946292544671124048329 14321209719408503343036247)
          ·
            refine ⟨21481814579112755014554371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14321209719408503343036247 21481814579112755014554371)
            ·
              refine ⟨32222721868669132521831557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21481814579112755014554371 32222721868669132521831557)
              ·
                refine ⟨6041760350375462347843417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32222721868669132521831557 6041760350375462347843417)
                ·
                  refine ⟨4531320262781596760882563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6041760350375462347843417 4531320262781596760882563)
                  ·
                    refine ⟨6796980394172395141323845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4531320262781596760882563 6796980394172395141323845)
                    ·
                      refine ⟨1274433823907324088998221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6796980394172395141323845 1274433823907324088998221)
                      ·
                        rfl

theorem cell23_2481951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_2481951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481951 prefixEnd_2481951 := by exact prefixLift 2481951
  have htrace : WordTrace (prefixWord ++ tailWord_2481951) baseStart_2481951 baseEnd_2481951 := by
    simpa [prefixWord, tailWord_2481951, baseEnd_2481951] using wordTrace_append hprefix tailTrace_2481951
  have hstable : (prefixWord ++ tailWord_2481951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481951).length < 2 ^ (prefixWord ++ tailWord_2481951).sum := by decide
  have hdescent : baseEnd_2481951 < baseStart_2481951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481978 : List Nat := [3, 1, 1, 1, 5, 2, 1, 2, 3, 4]
def baseStart_2481978 : Nat := 118140960795 + 2481978 * 2 ^ 59
def prefixEnd_2481978 : Nat := 4983230072969 + 3 ^ 40 * 2481978 * 2
def baseEnd_2481978 : Nat := 424815895961665161120199

theorem tailTrace_2481978 : CollatzResearch.WordTrace tailWord_2481978 prefixEnd_2481978 424815895961665161120199 := by
  unfold tailWord_2481978
  simp only [CollatzResearch.WordTrace]
  refine ⟨22631293650556267235013647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60350116401483379293369725 22631293650556267235013647)
  ·
    refine ⟨33946940475834400852520471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22631293650556267235013647 33946940475834400852520471)
    ·
      refine ⟨50920410713751601278780707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33946940475834400852520471 50920410713751601278780707)
      ·
        refine ⟨76380616070627401918171061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50920410713751601278780707 76380616070627401918171061)
        ·
          refine ⟨7160682756621318929828537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76380616070627401918171061 7160682756621318929828537)
          ·
            refine ⟨5370512067465989197371403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7160682756621318929828537 5370512067465989197371403)
            ·
              refine ⟨8055768101198983796057105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5370512067465989197371403 8055768101198983796057105)
              ·
                refine ⟨6041826075899237847042829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8055768101198983796057105 6041826075899237847042829)
                ·
                  refine ⟨2265684778462214192641061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6041826075899237847042829 2265684778462214192641061)
                  ·
                    refine ⟨424815895961665161120199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2265684778462214192641061 424815895961665161120199)
                    ·
                      rfl

theorem cell23_2481978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 3, 4].length) (baseStart_2481978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2481978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2481978 prefixEnd_2481978 := by exact prefixLift 2481978
  have htrace : WordTrace (prefixWord ++ tailWord_2481978) baseStart_2481978 baseEnd_2481978 := by
    simpa [prefixWord, tailWord_2481978, baseEnd_2481978] using wordTrace_append hprefix tailTrace_2481978
  have hstable : (prefixWord ++ tailWord_2481978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481978).length < 2 ^ (prefixWord ++ tailWord_2481978).sum := by decide
  have hdescent : baseEnd_2481978 < baseStart_2481978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482028 : List Nat := [2, 2, 1, 1, 4, 2, 1, 2, 1, 5, 2]
def baseStart_2482028 : Nat := 118140960795 + 2482028 * 2 ^ 59
def prefixEnd_2482028 : Nat := 4983230072969 + 3 ^ 40 * 2482028 * 2
def baseEnd_2482028 : Nat := 1274473361917720287735367

theorem tailTrace_2482028 : CollatzResearch.WordTrace tailWord_2482028 prefixEnd_2482028 1274473361917720287735367 := by
  unfold tailWord_2482028
  simp only [CollatzResearch.WordTrace]
  refine ⟨45263499126021963739687369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60351332168029284986249825 45263499126021963739687369)
  ·
    refine ⟨33947624344516472804765527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45263499126021963739687369 33947624344516472804765527)
    ·
      refine ⟨50921436516774709207148291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33947624344516472804765527 50921436516774709207148291)
      ·
        refine ⟨76382154775162063810722437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50921436516774709207148291 76382154775162063810722437)
        ·
          refine ⟨14321654020342886964510457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76382154775162063810722437 14321654020342886964510457)
          ·
            refine ⟨10741240515257165223382843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14321654020342886964510457 10741240515257165223382843)
            ·
              refine ⟨16111860772885747835074265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10741240515257165223382843 16111860772885747835074265)
              ·
                refine ⟨12083895579664310876305699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16111860772885747835074265 12083895579664310876305699)
                ·
                  refine ⟨18125843369496466314458549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12083895579664310876305699 18125843369496466314458549)
                  ·
                    refine ⟨1699297815890293716980489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18125843369496466314458549 1699297815890293716980489)
                    ·
                      refine ⟨1274473361917720287735367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1699297815890293716980489 1274473361917720287735367)
                      ·
                        rfl

theorem cell23_2482028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 5, 2].length) (baseStart_2482028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482028 prefixEnd_2482028 := by exact prefixLift 2482028
  have htrace : WordTrace (prefixWord ++ tailWord_2482028) baseStart_2482028 baseEnd_2482028 := by
    simpa [prefixWord, tailWord_2482028, baseEnd_2482028] using wordTrace_append hprefix tailTrace_2482028
  have hstable : (prefixWord ++ tailWord_2482028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482028).length < 2 ^ (prefixWord ++ tailWord_2482028).sum := by decide
  have hdescent : baseEnd_2482028 < baseStart_2482028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482052 : List Nat := [2, 3, 2, 1, 1, 1, 5, 3, 1, 1, 3]
def baseStart_2482052 : Nat := 118140960795 + 2482052 * 2 ^ 59
def prefixEnd_2482052 : Nat := 4983230072969 + 3 ^ 40 * 2482052 * 2
def baseEnd_2482052 : Nat := 1274485685453428193835257

theorem tailTrace_2482052 : CollatzResearch.WordTrace tailWord_2482052 prefixEnd_2482052 1274485685453428193835257 := by
  unfold tailWord_2482052
  simp only [CollatzResearch.WordTrace]
  refine ⟨45263936801978489789124205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60351915735971319718832273 45263936801978489789124205)
  ·
    refine ⟨16973976300741933670921577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45263936801978489789124205 16973976300741933670921577)
    ·
      refine ⟨12730482225556450253191183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16973976300741933670921577 12730482225556450253191183)
      ·
        refine ⟨19095723338334675379786775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12730482225556450253191183 19095723338334675379786775)
        ·
          refine ⟨28643585007502013069680163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19095723338334675379786775 28643585007502013069680163)
          ·
            refine ⟨42965377511253019604520245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28643585007502013069680163 42965377511253019604520245)
            ·
              refine ⟨4028004141679970587923773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42965377511253019604520245 4028004141679970587923773)
              ·
                refine ⟨1510501553129988970471415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4028004141679970587923773 1510501553129988970471415)
                ·
                  refine ⟨2265752329694983455707123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1510501553129988970471415 2265752329694983455707123)
                  ·
                    refine ⟨3398628494542475183560685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2265752329694983455707123 3398628494542475183560685)
                    ·
                      refine ⟨1274485685453428193835257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3398628494542475183560685 1274485685453428193835257)
                      ·
                        rfl

theorem cell23_2482052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_2482052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482052 prefixEnd_2482052 := by exact prefixLift 2482052
  have htrace : WordTrace (prefixWord ++ tailWord_2482052) baseStart_2482052 baseEnd_2482052 := by
    simpa [prefixWord, tailWord_2482052, baseEnd_2482052] using wordTrace_append hprefix tailTrace_2482052
  have hstable : (prefixWord ++ tailWord_2482052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482052).length < 2 ^ (prefixWord ++ tailWord_2482052).sum := by decide
  have hdescent : baseEnd_2482052 < baseStart_2482052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482071 : List Nat := [1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 6]
def baseStart_2482071 : Nat := 118140960795 + 2482071 * 2 ^ 59
def prefixEnd_2482071 : Nat := 4983230072969 + 3 ^ 40 * 2482071 * 2
def baseEnd_2482071 : Nat := 1274495441585863619497669

theorem tailTrace_2482071 : CollatzResearch.WordTrace tailWord_2482071 prefixEnd_2482071 1274495441585863619497669 := by
  unfold tailWord_2482071
  simp only [CollatzResearch.WordTrace]
  refine ⟨90528566590888145823190067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60352377727258763882126711 90528566590888145823190067)
  ·
    refine ⟨135792849886332218734785101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90528566590888145823190067 135792849886332218734785101)
    ·
      refine ⟨50922318707374582025544413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135792849886332218734785101 50922318707374582025544413)
      ·
        refine ⟨19095869515265468259579155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50922318707374582025544413 19095869515265468259579155)
        ·
          refine ⟨28643804272898202389368733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19095869515265468259579155 28643804272898202389368733)
          ·
            refine ⟨10741426602336825896013275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28643804272898202389368733 10741426602336825896013275)
            ·
              refine ⟨16112139903505238844019913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10741426602336825896013275 16112139903505238844019913)
              ·
                refine ⟨12084104927628929133014935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16112139903505238844019913 12084104927628929133014935)
                ·
                  refine ⟨18126157391443393699522403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12084104927628929133014935 18126157391443393699522403)
                  ·
                    refine ⟨27189236087165090549283605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18126157391443393699522403 27189236087165090549283605)
                    ·
                      refine ⟨1274495441585863619497669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27189236087165090549283605 1274495441585863619497669)
                      ·
                        rfl

theorem cell23_2482071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_2482071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482071 prefixEnd_2482071 := by exact prefixLift 2482071
  have htrace : WordTrace (prefixWord ++ tailWord_2482071) baseStart_2482071 baseEnd_2482071 := by
    simpa [prefixWord, tailWord_2482071, baseEnd_2482071] using wordTrace_append hprefix tailTrace_2482071
  have hstable : (prefixWord ++ tailWord_2482071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482071).length < 2 ^ (prefixWord ++ tailWord_2482071).sum := by decide
  have hdescent : baseEnd_2482071 < baseStart_2482071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482169 : List Nat := [1, 2, 1, 3, 1, 6, 2, 1, 1, 3, 2]
def baseStart_2482169 : Nat := 118140960795 + 2482169 * 2 ^ 59
def prefixEnd_2482169 : Nat := 4983230072969 + 3 ^ 40 * 2482169 * 2
def baseEnd_2482169 : Nat := 1274545762690004236072219

theorem tailTrace_2482169 : CollatzResearch.WordTrace tailWord_2482169 prefixEnd_2482169 1274545762690004236072219 := by
  unfold tailWord_2482169
  simp only [CollatzResearch.WordTrace]
  refine ⟨90532140944533108560257561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60354760629688739040171707 90532140944533108560257561)
  ·
    refine ⟨67899105708399831420193171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90532140944533108560257561 67899105708399831420193171)
    ·
      refine ⟨101848658562599747130289757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67899105708399831420193171 101848658562599747130289757)
      ·
        refine ⟨38193246960974905173858659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101848658562599747130289757 38193246960974905173858659)
        ·
          refine ⟨57289870441462357760787989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38193246960974905173858659 57289870441462357760787989)
          ·
            refine ⟨2685462676943548020036937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57289870441462357760787989 2685462676943548020036937)
            ·
              refine ⟨2014097007707661015027703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2685462676943548020036937 2014097007707661015027703)
              ·
                refine ⟨3021145511561491522541555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2014097007707661015027703 3021145511561491522541555)
                ·
                  refine ⟨4531718267342237283812333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3021145511561491522541555 4531718267342237283812333)
                  ·
                    refine ⟨1699394350253338981429625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4531718267342237283812333 1699394350253338981429625)
                    ·
                      refine ⟨1274545762690004236072219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1699394350253338981429625 1274545762690004236072219)
                      ·
                        rfl

theorem cell23_2482169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 1, 3, 2].length) (baseStart_2482169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482169 prefixEnd_2482169 := by exact prefixLift 2482169
  have htrace : WordTrace (prefixWord ++ tailWord_2482169) baseStart_2482169 baseEnd_2482169 := by
    simpa [prefixWord, tailWord_2482169, baseEnd_2482169] using wordTrace_append hprefix tailTrace_2482169
  have hstable : (prefixWord ++ tailWord_2482169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482169).length < 2 ^ (prefixWord ++ tailWord_2482169).sum := by decide
  have hdescent : baseEnd_2482169 < baseStart_2482169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482188 : List Nat := [2, 2, 1, 2, 3, 1, 4, 1, 7]
def baseStart_2482188 : Nat := 118140960795 + 2482188 * 2 ^ 59
def prefixEnd_2482188 : Nat := 4983230072969 + 3 ^ 40 * 2482188 * 2
def baseEnd_2482188 : Nat := 141617279869159962414959

theorem tailTrace_2482188 : CollatzResearch.WordTrace tailWord_2482188 prefixEnd_2482188 141617279869159962414959 := by
  unfold tailWord_2482188
  simp only [CollatzResearch.WordTrace]
  refine ⟨45266416965732137402599609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60355222620976183203466145 45266416965732137402599609)
  ·
    refine ⟨33949812724299103051949707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45266416965732137402599609 33949812724299103051949707)
    ·
      refine ⟨50924719086448654577924561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33949812724299103051949707 50924719086448654577924561)
      ·
        refine ⟨38193539314836490933443421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50924719086448654577924561 38193539314836490933443421)
        ·
          refine ⟨14322577243063684100041283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38193539314836490933443421 14322577243063684100041283)
          ·
            refine ⟨21483865864595526150061925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14322577243063684100041283 21483865864595526150061925)
            ·
              refine ⟨4028224849611661153136611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21483865864595526150061925 4028224849611661153136611)
              ·
                refine ⟨6042337274417491729704917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4028224849611661153136611 6042337274417491729704917)
                ·
                  refine ⟨141617279869159962414959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6042337274417491729704917 141617279869159962414959)
                  ·
                    rfl

theorem cell23_2482188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 7].length) (baseStart_2482188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482188 prefixEnd_2482188 := by exact prefixLift 2482188
  have htrace : WordTrace (prefixWord ++ tailWord_2482188) baseStart_2482188 baseEnd_2482188 := by
    simpa [prefixWord, tailWord_2482188, baseEnd_2482188] using wordTrace_append hprefix tailTrace_2482188
  have hstable : (prefixWord ++ tailWord_2482188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482188).length < 2 ^ (prefixWord ++ tailWord_2482188).sum := by decide
  have hdescent : baseEnd_2482188 < baseStart_2482188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482199 : List Nat := [1, 1, 3, 5, 2, 2, 1, 1, 1, 4, 2]
def baseStart_2482199 : Nat := 118140960795 + 2482199 * 2 ^ 59
def prefixEnd_2482199 : Nat := 4983230072969 + 3 ^ 40 * 2482199 * 2
def baseEnd_2482199 : Nat := 1274561167109639118697081

theorem tailTrace_2482199 : CollatzResearch.WordTrace tailWord_2482199 prefixEnd_2482199 1274561167109639118697081 := by
  unfold tailWord_2482199
  simp only [CollatzResearch.WordTrace]
  refine ⟨90533235134424423683849651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60355490089616282455899767 90533235134424423683849651)
  ·
    refine ⟨135799852701636635525774477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90533235134424423683849651 135799852701636635525774477)
    ·
      refine ⟨50924944763113738322165429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135799852701636635525774477 50924944763113738322165429)
      ·
        refine ⟨4774213571541912967703009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50924944763113738322165429 4774213571541912967703009)
        ·
          refine ⟨3580660178656434725777257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4774213571541912967703009 3580660178656434725777257)
          ·
            refine ⟨2685495133992326044332943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3580660178656434725777257 2685495133992326044332943)
            ·
              refine ⟨4028242700988489066499415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2685495133992326044332943 4028242700988489066499415)
              ·
                refine ⟨6042364051482733599749123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4028242700988489066499415 6042364051482733599749123)
                ·
                  refine ⟨9063546077224100399623685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6042364051482733599749123 9063546077224100399623685)
                  ·
                    refine ⟨1699414889479518824929441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9063546077224100399623685 1699414889479518824929441)
                    ·
                      refine ⟨1274561167109639118697081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1699414889479518824929441 1274561167109639118697081)
                      ·
                        rfl

theorem cell23_2482199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_2482199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482199 prefixEnd_2482199 := by exact prefixLift 2482199
  have htrace : WordTrace (prefixWord ++ tailWord_2482199) baseStart_2482199 baseEnd_2482199 := by
    simpa [prefixWord, tailWord_2482199, baseEnd_2482199] using wordTrace_append hprefix tailTrace_2482199
  have hstable : (prefixWord ++ tailWord_2482199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482199).length < 2 ^ (prefixWord ++ tailWord_2482199).sum := by decide
  have hdescent : baseEnd_2482199 < baseStart_2482199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482222 : List Nat := [4, 1, 3, 1, 1, 2, 3, 3, 5]
def baseStart_2482222 : Nat := 118140960795 + 2482222 * 2 ^ 59
def prefixEnd_2482222 : Nat := 4983230072969 + 3 ^ 40 * 2482222 * 2
def baseEnd_2482222 : Nat := 141619219684965836523275

theorem tailTrace_2482222 : CollatzResearch.WordTrace tailWord_2482222 prefixEnd_2482222 141619219684965836523275 := by
  unfold tailWord_2482222
  simp only [CollatzResearch.WordTrace]
  refine ⟨11316759251667637326492115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60356049342227399074624613 11316759251667637326492115)
  ·
    refine ⟨16975138877501455989738173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11316759251667637326492115 16975138877501455989738173)
    ·
      refine ⟨6365677079063045996151815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16975138877501455989738173 6365677079063045996151815)
      ·
        refine ⟨9548515618594568994227723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6365677079063045996151815 9548515618594568994227723)
        ·
          refine ⟨14322773427891853491341585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9548515618594568994227723 14322773427891853491341585)
          ·
            refine ⟨10742080070918890118506189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14322773427891853491341585 10742080070918890118506189)
            ·
              refine ⟨4028280026594583794439821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10742080070918890118506189 4028280026594583794439821)
              ·
                refine ⟨1510605009972968922914933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4028280026594583794439821 1510605009972968922914933)
                ·
                  refine ⟨141619219684965836523275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1510605009972968922914933 141619219684965836523275)
                  ·
                    rfl

theorem cell23_2482222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3, 5].length) (baseStart_2482222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482222 prefixEnd_2482222 := by exact prefixLift 2482222
  have htrace : WordTrace (prefixWord ++ tailWord_2482222) baseStart_2482222 baseEnd_2482222 := by
    simpa [prefixWord, tailWord_2482222, baseEnd_2482222] using wordTrace_append hprefix tailTrace_2482222
  have hstable : (prefixWord ++ tailWord_2482222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482222).length < 2 ^ (prefixWord ++ tailWord_2482222).sum := by decide
  have hdescent : baseEnd_2482222 < baseStart_2482222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482275 : List Nat := [1, 1, 1, 5, 1, 1, 3, 3, 2, 2, 3]
def baseStart_2482275 : Nat := 118140960795 + 2482275 * 2 ^ 59
def prefixEnd_2482275 : Nat := 4983230072969 + 3 ^ 40 * 2482275 * 2
def baseEnd_2482275 : Nat := 1274600191639380821346731

theorem tailTrace_2482275 : CollatzResearch.WordTrace tailWord_2482275 prefixEnd_2482275 1274600191639380821346731 := by
  unfold tailWord_2482275
  simp only [CollatzResearch.WordTrace]
  refine ⟨90536007082149088663616279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60357338054766059109077519 90536007082149088663616279)
  ·
    refine ⟨135804010623223632995424419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90536007082149088663616279 135804010623223632995424419)
    ·
      refine ⟨203706015934835449493136629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135804010623223632995424419 203706015934835449493136629)
      ·
        refine ⟨19097438993890823389981559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 203706015934835449493136629 19097438993890823389981559)
        ·
          refine ⟨28646158490836235084972339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19097438993890823389981559 28646158490836235084972339)
          ·
            refine ⟨42969237736254352627458509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28646158490836235084972339 42969237736254352627458509)
            ·
              refine ⟨16113464151095382235296941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42969237736254352627458509 16113464151095382235296941)
              ·
                refine ⟨6042549056660768338236353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16113464151095382235296941 6042549056660768338236353)
                ·
                  refine ⟨4531911792495576253677265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6042549056660768338236353 4531911792495576253677265)
                  ·
                    refine ⟨3398933844371682190257949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4531911792495576253677265 3398933844371682190257949)
                    ·
                      refine ⟨1274600191639380821346731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3398933844371682190257949 1274600191639380821346731)
                      ·
                        rfl

theorem cell23_2482275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_2482275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482275 prefixEnd_2482275 := by exact prefixLift 2482275
  have htrace : WordTrace (prefixWord ++ tailWord_2482275) baseStart_2482275 baseEnd_2482275 := by
    simpa [prefixWord, tailWord_2482275, baseEnd_2482275] using wordTrace_append hprefix tailTrace_2482275
  have hstable : (prefixWord ++ tailWord_2482275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482275).length < 2 ^ (prefixWord ++ tailWord_2482275).sum := by decide
  have hdescent : baseEnd_2482275 < baseStart_2482275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482295 : List Nat := [1, 1, 3, 1, 1, 6, 2, 2, 6]
def baseStart_2482295 : Nat := 118140960795 + 2482295 * 2 ^ 59
def prefixEnd_2482295 : Nat := 4983230072969 + 3 ^ 40 * 2482295 * 2
def baseEnd_2482295 : Nat := 141623384583607860344071

theorem tailTrace_2482295 : CollatzResearch.WordTrace tailWord_2482295 prefixEnd_2482295 141623384583607860344071 := by
  unfold tailWord_2482295
  simp only [CollatzResearch.WordTrace]
  refine ⟨90536736542076632079344339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60357824361384421386229559 90536736542076632079344339)
  ·
    refine ⟨135805104813114948119016509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90536736542076632079344339 135805104813114948119016509)
    ·
      refine ⟨50926914304918105544631191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135805104813114948119016509 50926914304918105544631191)
      ·
        refine ⟨76390371457377158316946787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50926914304918105544631191 76390371457377158316946787)
        ·
          refine ⟨114585557186065737475420181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76390371457377158316946787 114585557186065737475420181)
          ·
            refine ⟨5371197993096831444160321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 114585557186065737475420181 5371197993096831444160321)
            ·
              refine ⟨4028398494822623583120241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5371197993096831444160321 4028398494822623583120241)
              ·
                refine ⟨3021298871116967687340181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4028398494822623583120241 3021298871116967687340181)
                ·
                  refine ⟨141623384583607860344071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3021298871116967687340181 141623384583607860344071)
                  ·
                    rfl

theorem cell23_2482295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 6].length) (baseStart_2482295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482295 prefixEnd_2482295 := by exact prefixLift 2482295
  have htrace : WordTrace (prefixWord ++ tailWord_2482295) baseStart_2482295 baseEnd_2482295 := by
    simpa [prefixWord, tailWord_2482295, baseEnd_2482295] using wordTrace_append hprefix tailTrace_2482295
  have hstable : (prefixWord ++ tailWord_2482295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482295).length < 2 ^ (prefixWord ++ tailWord_2482295).sum := by decide
  have hdescent : baseEnd_2482295 < baseStart_2482295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482325 : List Nat := [1, 3, 2, 1, 1, 1, 4, 4, 1, 5]
def baseStart_2482325 : Nat := 118140960795 + 2482325 * 2 ^ 59
def prefixEnd_2482325 : Nat := 4983230072969 + 3 ^ 40 * 2482325 * 2
def baseEnd_2482325 : Nat := 424875288557368541907167

theorem tailTrace_2482325 : CollatzResearch.WordTrace tailWord_2482325 prefixEnd_2482325 424875288557368541907167 := by
  unfold tailWord_2482325
  simp only [CollatzResearch.WordTrace]
  refine ⟨90537830731967947202936429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60358553821311964801957619 90537830731967947202936429)
  ·
    refine ⟨33951686524487980201101161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90537830731967947202936429 33951686524487980201101161)
    ·
      refine ⟨25463764893365985150825871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33951686524487980201101161 25463764893365985150825871)
      ·
        refine ⟨38195647340048977726238807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25463764893365985150825871 38195647340048977726238807)
        ·
          refine ⟨57293471010073466589358211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38195647340048977726238807 57293471010073466589358211)
          ·
            refine ⟨85940206515110199884037317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57293471010073466589358211 85940206515110199884037317)
            ·
              refine ⟨16113788721583162478256997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85940206515110199884037317 16113788721583162478256997)
              ·
                refine ⟨3021335385296842964673187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16113788721583162478256997 3021335385296842964673187)
                ·
                  refine ⟨4532003077945264447009781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3021335385296842964673187 4532003077945264447009781)
                  ·
                    refine ⟨424875288557368541907167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4532003077945264447009781 424875288557368541907167)
                    ·
                      rfl

theorem cell23_2482325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_2482325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482325 prefixEnd_2482325 := by exact prefixLift 2482325
  have htrace : WordTrace (prefixWord ++ tailWord_2482325) baseStart_2482325 baseEnd_2482325 := by
    simpa [prefixWord, tailWord_2482325, baseEnd_2482325] using wordTrace_append hprefix tailTrace_2482325
  have hstable : (prefixWord ++ tailWord_2482325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482325).length < 2 ^ (prefixWord ++ tailWord_2482325).sum := by decide
  have hdescent : baseEnd_2482325 < baseStart_2482325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482332 : List Nat := [2, 2, 3, 2, 1, 1, 3, 1, 1, 5, 2]
def baseStart_2482332 : Nat := 118140960795 + 2482332 * 2 ^ 59
def prefixEnd_2482332 : Nat := 4983230072969 + 3 ^ 40 * 2482332 * 2
def baseEnd_2482332 : Nat := 1274629460036687098333969

theorem tailTrace_2482332 : CollatzResearch.WordTrace tailWord_2482332 prefixEnd_2482332 1274629460036687098333969 := by
  unfold tailWord_2482332
  simp only [CollatzResearch.WordTrace]
  refine ⟨45269043021471293699220625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60358724028628391598960833 45269043021471293699220625)
  ·
    refine ⟨33951782266103470274415469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45269043021471293699220625 33951782266103470274415469)
    ·
      refine ⟨12731918349788801352905801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33951782266103470274415469 12731918349788801352905801)
      ·
        refine ⟨9548938762341601014679351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12731918349788801352905801 9548938762341601014679351)
        ·
          refine ⟨14323408143512401522019027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9548938762341601014679351 14323408143512401522019027)
          ·
            refine ⟨21485112215268602283028541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14323408143512401522019027 21485112215268602283028541)
            ·
              refine ⟨8056917080725725856135703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21485112215268602283028541 8056917080725725856135703)
              ·
                refine ⟨12085375621088588784203555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8056917080725725856135703 12085375621088588784203555)
                ·
                  refine ⟨18128063431632883176305333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12085375621088588784203555 18128063431632883176305333)
                  ·
                    refine ⟨1699505946715582797778625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18128063431632883176305333 1699505946715582797778625)
                    ·
                      refine ⟨1274629460036687098333969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1699505946715582797778625 1274629460036687098333969)
                      ·
                        rfl

theorem cell23_2482332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_2482332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482332 prefixEnd_2482332 := by exact prefixLift 2482332
  have htrace : WordTrace (prefixWord ++ tailWord_2482332) baseStart_2482332 baseEnd_2482332 := by
    simpa [prefixWord, tailWord_2482332, baseEnd_2482332] using wordTrace_append hprefix tailTrace_2482332
  have hstable : (prefixWord ++ tailWord_2482332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482332).length < 2 ^ (prefixWord ++ tailWord_2482332).sum := by decide
  have hdescent : baseEnd_2482332 < baseStart_2482332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482346 : List Nat := [3, 1, 5, 1, 3, 1, 1, 2, 6]
def baseStart_2482346 : Nat := 118140960795 + 2482346 * 2 ^ 59
def prefixEnd_2482346 : Nat := 4983230072969 + 3 ^ 40 * 2482346 * 2
def baseEnd_2482346 : Nat := 141626294307316671506545

theorem tailTrace_2482346 : CollatzResearch.WordTrace tailWord_2482346 prefixEnd_2482346 141626294307316671506545 := by
  unfold tailWord_2482346
  simp only [CollatzResearch.WordTrace]
  refine ⟨22634649166222966947362723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60359064443261245192967261 22634649166222966947362723)
  ·
    refine ⟨33951973749334450421044085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22634649166222966947362723 33951973749334450421044085)
    ·
      refine ⟨3182997539000104726972883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33951973749334450421044085 3182997539000104726972883)
      ·
        refine ⟨4774496308500157090459325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3182997539000104726972883 4774496308500157090459325)
        ·
          refine ⟨1790436115687558908922247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4774496308500157090459325 1790436115687558908922247)
          ·
            refine ⟨2685654173531338363383371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1790436115687558908922247 2685654173531338363383371)
            ·
              refine ⟨4028481260297007545075057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2685654173531338363383371 4028481260297007545075057)
              ·
                refine ⟨3021360945222755658806293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4028481260297007545075057 3021360945222755658806293)
                ·
                  refine ⟨141626294307316671506545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3021360945222755658806293 141626294307316671506545)
                  ·
                    rfl

theorem cell23_2482346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 6].length) (baseStart_2482346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482346 prefixEnd_2482346 := by exact prefixLift 2482346
  have htrace : WordTrace (prefixWord ++ tailWord_2482346) baseStart_2482346 baseEnd_2482346 := by
    simpa [prefixWord, tailWord_2482346, baseEnd_2482346] using wordTrace_append hprefix tailTrace_2482346
  have hstable : (prefixWord ++ tailWord_2482346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482346).length < 2 ^ (prefixWord ++ tailWord_2482346).sum := by decide
  have hdescent : baseEnd_2482346 < baseStart_2482346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482372 : List Nat := [2, 3, 3, 1, 2, 1, 3, 1, 1, 6]
def baseStart_2482372 : Nat := 118140960795 + 2482372 * 2 ^ 59
def prefixEnd_2482372 : Nat := 4983230072969 + 3 ^ 40 * 2482372 * 2
def baseEnd_2482372 : Nat := 424883333087622313944595

theorem tailTrace_2482372 : CollatzResearch.WordTrace tailWord_2482372 prefixEnd_2482372 424883333087622313944595 := by
  unfold tailWord_2482372
  simp only [CollatzResearch.WordTrace]
  refine ⟨45269772481398837114948685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60359696641865116153264913 45269772481398837114948685)
  ·
    refine ⟨16976164680524563918105757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45269772481398837114948685 16976164680524563918105757)
    ·
      refine ⟨6366061755196711469289659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16976164680524563918105757 6366061755196711469289659)
      ·
        refine ⟨9549092632795067203934489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6366061755196711469289659 9549092632795067203934489)
        ·
          refine ⟨7161819474596300402950867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9549092632795067203934489 7161819474596300402950867)
          ·
            refine ⟨10742729211894450604426301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7161819474596300402950867 10742729211894450604426301)
            ·
              refine ⟨4028523454460418976659863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10742729211894450604426301 4028523454460418976659863)
              ·
                refine ⟨6042785181690628464989795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4028523454460418976659863 6042785181690628464989795)
                ·
                  refine ⟨9064177772535942697484693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6042785181690628464989795 9064177772535942697484693)
                  ·
                    refine ⟨424883333087622313944595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9064177772535942697484693 424883333087622313944595)
                    ·
                      rfl

theorem cell23_2482372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_2482372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482372 prefixEnd_2482372 := by exact prefixLift 2482372
  have htrace : WordTrace (prefixWord ++ tailWord_2482372) baseStart_2482372 baseEnd_2482372 := by
    simpa [prefixWord, tailWord_2482372, baseEnd_2482372] using wordTrace_append hprefix tailTrace_2482372
  have hstable : (prefixWord ++ tailWord_2482372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482372).length < 2 ^ (prefixWord ++ tailWord_2482372).sum := by decide
  have hdescent : baseEnd_2482372 < baseStart_2482372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482385 : List Nat := [1, 2, 2, 1, 2, 2, 6, 7]
def baseStart_2482385 : Nat := 118140960795 + 2482385 * 2 ^ 59
def prefixEnd_2482385 : Nat := 4983230072969 + 3 ^ 40 * 2482385 * 2
def baseEnd_2482385 : Nat := 47209506463384273739675

theorem tailTrace_2482385 : CollatzResearch.WordTrace tailWord_2482385 prefixEnd_2482385 47209506463384273739675 := by
  unfold tailWord_2482385
  simp only [CollatzResearch.WordTrace]
  refine ⟨90540019111750577450120609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60360012741167051633413739 90540019111750577450120609)
  ·
    refine ⟨67905014333812933087590457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90540019111750577450120609 67905014333812933087590457)
    ·
      refine ⟨50928760750359699815692843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67905014333812933087590457 50928760750359699815692843)
      ·
        refine ⟨76393141125539549723539265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50928760750359699815692843 76393141125539549723539265)
        ·
          refine ⟨57294855844154662292654449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76393141125539549723539265 57294855844154662292654449)
          ·
            refine ⟨42971141883115996719490837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57294855844154662292654449 42971141883115996719490837)
            ·
              refine ⟨2014272275771062346226133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42971141883115996719490837 2014272275771062346226133)
              ·
                refine ⟨47209506463384273739675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2014272275771062346226133 47209506463384273739675)
                ·
                  rfl

theorem cell23_2482385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 7].length) (baseStart_2482385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482385 prefixEnd_2482385 := by exact prefixLift 2482385
  have htrace : WordTrace (prefixWord ++ tailWord_2482385) baseStart_2482385 baseEnd_2482385 := by
    simpa [prefixWord, tailWord_2482385, baseEnd_2482385] using wordTrace_append hprefix tailTrace_2482385
  have hstable : (prefixWord ++ tailWord_2482385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482385).length < 2 ^ (prefixWord ++ tailWord_2482385).sum := by decide
  have hdescent : baseEnd_2482385 < baseStart_2482385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482390 : List Nat := [5, 2, 1, 2, 1, 3, 1, 3, 1, 1, 3]
def baseStart_2482390 : Nat := 118140960795 + 2482390 * 2 ^ 59
def prefixEnd_2482390 : Nat := 4983230072969 + 3 ^ 40 * 2482390 * 2
def baseEnd_2482390 : Nat := 1274659241914647871408703

theorem tailTrace_2482390 : CollatzResearch.WordTrace tailWord_2482390 prefixEnd_2482390 1274659241914647871408703 := by
  unfold tailWord_2482390
  simp only [CollatzResearch.WordTrace]
  refine ⟨5658762592295778956503289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60360134317821642202701749 5658762592295778956503289)
  ·
    refine ⟨4244071944221834217377467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5658762592295778956503289 4244071944221834217377467)
    ·
      refine ⟨6366107916332751326066201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4244071944221834217377467 6366107916332751326066201)
      ·
        refine ⟨4774580937249563494549651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6366107916332751326066201 4774580937249563494549651)
        ·
          refine ⟨7161871405874345241824477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4774580937249563494549651 7161871405874345241824477)
          ·
            refine ⟨2685701777202879465684179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7161871405874345241824477 2685701777202879465684179)
            ·
              refine ⟨4028552665804319198526269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2685701777202879465684179 4028552665804319198526269)
              ·
                refine ⟨1510707249676619699447351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4028552665804319198526269 1510707249676619699447351)
                ·
                  refine ⟨2266060874514929549171027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1510707249676619699447351 2266060874514929549171027)
                  ·
                    refine ⟨3399091311772394323756541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2266060874514929549171027 3399091311772394323756541)
                    ·
                      refine ⟨1274659241914647871408703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3399091311772394323756541 1274659241914647871408703)
                      ·
                        rfl

theorem cell23_2482390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_2482390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482390 prefixEnd_2482390 := by exact prefixLift 2482390
  have htrace : WordTrace (prefixWord ++ tailWord_2482390) baseStart_2482390 baseEnd_2482390 := by
    simpa [prefixWord, tailWord_2482390, baseEnd_2482390] using wordTrace_append hprefix tailTrace_2482390
  have hstable : (prefixWord ++ tailWord_2482390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482390).length < 2 ^ (prefixWord ++ tailWord_2482390).sum := by decide
  have hdescent : baseEnd_2482390 < baseStart_2482390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482412 : List Nat := [2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 3]
def baseStart_2482412 : Nat := 118140960795 + 2482412 * 2 ^ 59
def prefixEnd_2482412 : Nat := 4983230072969 + 3 ^ 40 * 2482412 * 2
def baseEnd_2482412 : Nat := 1274670538489046785333601

theorem tailTrace_2482412 : CollatzResearch.WordTrace tailWord_2482412 prefixEnd_2482412 1274670538489046785333601 := by
  unfold tailWord_2482412
  simp only [CollatzResearch.WordTrace]
  refine ⟨45270501941326380530676745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60360669255101840707568993 45270501941326380530676745)
  ·
    refine ⟨33952876455994785398007559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45270501941326380530676745 33952876455994785398007559)
    ·
      refine ⟨50929314683992178097011339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33952876455994785398007559 50929314683992178097011339)
      ·
        refine ⟨76393972025988267145517009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50929314683992178097011339 76393972025988267145517009)
        ·
          refine ⟨57295479019491200359137757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76393972025988267145517009 57295479019491200359137757)
          ·
            refine ⟨21485804632309200134676659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57295479019491200359137757 21485804632309200134676659)
            ·
              refine ⟨32228706948463800202014989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21485804632309200134676659 32228706948463800202014989)
              ·
                refine ⟨12085765105673925075755621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32228706948463800202014989 12085765105673925075755621)
                ·
                  refine ⟨2266080957313860951704179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12085765105673925075755621 2266080957313860951704179)
                  ·
                    refine ⟨3399121435970791427556269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2266080957313860951704179 3399121435970791427556269)
                    ·
                      refine ⟨1274670538489046785333601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3399121435970791427556269 1274670538489046785333601)
                      ·
                        rfl

theorem cell23_2482412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 3].length) (baseStart_2482412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482412 prefixEnd_2482412 := by exact prefixLift 2482412
  have htrace : WordTrace (prefixWord ++ tailWord_2482412) baseStart_2482412 baseEnd_2482412 := by
    simpa [prefixWord, tailWord_2482412, baseEnd_2482412] using wordTrace_append hprefix tailTrace_2482412
  have hstable : (prefixWord ++ tailWord_2482412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482412).length < 2 ^ (prefixWord ++ tailWord_2482412).sum := by decide
  have hdescent : baseEnd_2482412 < baseStart_2482412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482413 : List Nat := [1, 5, 1, 2, 3, 2, 1, 1, 3, 2, 2]
def baseStart_2482413 : Nat := 118140960795 + 2482413 * 2 ^ 59
def prefixEnd_2482413 : Nat := 4983230072969 + 3 ^ 40 * 2482413 * 2
def baseEnd_2482413 : Nat := 1274671051969701281421097

theorem tailTrace_2482413 : CollatzResearch.WordTrace tailWord_2482413 prefixEnd_2482413 1274671051969701281421097 := by
  unfold tailWord_2482413
  simp only [CollatzResearch.WordTrace]
  refine ⟨90541040355649138232139893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60360693570432758821426595 90541040355649138232139893)
  ·
    refine ⟨8488222533342106709263115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90541040355649138232139893 8488222533342106709263115)
    ·
      refine ⟨12732333800013160063894673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8488222533342106709263115 12732333800013160063894673)
      ·
        refine ⟨9549250350009870047921005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12732333800013160063894673 9549250350009870047921005)
        ·
          refine ⟨3580968881253701267970377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9549250350009870047921005 3580968881253701267970377)
          ·
            refine ⟨2685726660940275950977783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3580968881253701267970377 2685726660940275950977783)
            ·
              refine ⟨4028589991410413926466675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2685726660940275950977783 4028589991410413926466675)
              ·
                refine ⟨6042884987115620889700013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4028589991410413926466675 6042884987115620889700013)
                ·
                  refine ⟨2266081870168357833637505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6042884987115620889700013 2266081870168357833637505)
                  ·
                    refine ⟨1699561402626268375228129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2266081870168357833637505 1699561402626268375228129)
                    ·
                      refine ⟨1274671051969701281421097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1699561402626268375228129 1274671051969701281421097)
                      ·
                        rfl

theorem cell23_2482413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_2482413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482413 prefixEnd_2482413 := by exact prefixLift 2482413
  have htrace : WordTrace (prefixWord ++ tailWord_2482413) baseStart_2482413 baseEnd_2482413 := by
    simpa [prefixWord, tailWord_2482413, baseEnd_2482413] using wordTrace_append hprefix tailTrace_2482413
  have hstable : (prefixWord ++ tailWord_2482413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482413).length < 2 ^ (prefixWord ++ tailWord_2482413).sum := by decide
  have hdescent : baseEnd_2482413 < baseStart_2482413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482456 : List Nat := [2, 1, 2, 3, 1, 2, 5, 1, 1, 3, 2]
def baseStart_2482456 : Nat := 118140960795 + 2482456 * 2 ^ 59
def prefixEnd_2482456 : Nat := 4983230072969 + 3 ^ 40 * 2482456 * 2
def baseEnd_2482456 : Nat := 1274693131637844613183399

theorem tailTrace_2482456 : CollatzResearch.WordTrace tailWord_2482456 prefixEnd_2482456 1274693131637844613183399 := by
  unfold tailWord_2482456
  simp only [CollatzResearch.WordTrace]
  refine ⟨45271304347246678287977611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60361739129662237717303481 45271304347246678287977611)
  ·
    refine ⟨67906956520870017431966417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45271304347246678287977611 67906956520870017431966417)
    ·
      refine ⟨50930217390652513073974813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67906956520870017431966417 50930217390652513073974813)
      ·
        refine ⟨19098831521494692402740555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50930217390652513073974813 19098831521494692402740555)
        ·
          refine ⟨28648247282242038604110833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19098831521494692402740555 28648247282242038604110833)
          ·
            refine ⟨21486185461681528953083125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28648247282242038604110833 21486185461681528953083125)
            ·
              refine ⟨2014329887032643339351543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21486185461681528953083125 2014329887032643339351543)
              ·
                refine ⟨3021494830548965009027315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2014329887032643339351543 3021494830548965009027315)
                ·
                  refine ⟨4532242245823447513540973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3021494830548965009027315 4532242245823447513540973)
                  ·
                    refine ⟨1699590842183792817577865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4532242245823447513540973 1699590842183792817577865)
                    ·
                      refine ⟨1274693131637844613183399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1699590842183792817577865 1274693131637844613183399)
                      ·
                        rfl

theorem cell23_2482456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_2482456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482456 prefixEnd_2482456 := by exact prefixLift 2482456
  have htrace : WordTrace (prefixWord ++ tailWord_2482456) baseStart_2482456 baseEnd_2482456 := by
    simpa [prefixWord, tailWord_2482456, baseEnd_2482456] using wordTrace_append hprefix tailTrace_2482456
  have hstable : (prefixWord ++ tailWord_2482456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482456).length < 2 ^ (prefixWord ++ tailWord_2482456).sum := by decide
  have hdescent : baseEnd_2482456 < baseStart_2482456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482515 : List Nat := [1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 5]
def baseStart_2482515 : Nat := 118140960795 + 2482515 * 2 ^ 59
def prefixEnd_2482515 : Nat := 4983230072969 + 3 ^ 40 * 2482515 * 2
def baseEnd_2482515 : Nat := 1274723426996459882345627

theorem tailTrace_2482515 : CollatzResearch.WordTrace tailWord_2482515 prefixEnd_2482515 1274723426996459882345627 := by
  unfold tailWord_2482515
  simp only [CollatzResearch.WordTrace]
  refine ⟨90544760601279609652352999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60363173734186406434901999 90544760601279609652352999)
  ·
    refine ⟨135817140901919414478529499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90544760601279609652352999 135817140901919414478529499)
    ·
      refine ⟨203725711352879121717794249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135817140901919414478529499 203725711352879121717794249)
      ·
        refine ⟨152794283514659341288345687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203725711352879121717794249 152794283514659341288345687)
        ·
          refine ⟨229191425271989011932518531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152794283514659341288345687 229191425271989011932518531)
          ·
            refine ⟨343787137907983517898777797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229191425271989011932518531 343787137907983517898777797)
            ·
              refine ⟨64460088357746909606020837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 343787137907983517898777797 64460088357746909606020837)
              ·
                refine ⟨12086266567077545551128907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64460088357746909606020837 12086266567077545551128907)
                ·
                  refine ⟨18129399850616318326693361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12086266567077545551128907 18129399850616318326693361)
                  ·
                    refine ⟨13597049887962238745020021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18129399850616318326693361 13597049887962238745020021)
                    ·
                      refine ⟨1274723426996459882345627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13597049887962238745020021 1274723426996459882345627)
                      ·
                        rfl

theorem cell23_2482515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 5].length) (baseStart_2482515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482515 prefixEnd_2482515 := by exact prefixLift 2482515
  have htrace : WordTrace (prefixWord ++ tailWord_2482515) baseStart_2482515 baseEnd_2482515 := by
    simpa [prefixWord, tailWord_2482515, baseEnd_2482515] using wordTrace_append hprefix tailTrace_2482515
  have hstable : (prefixWord ++ tailWord_2482515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482515).length < 2 ^ (prefixWord ++ tailWord_2482515).sum := by decide
  have hdescent : baseEnd_2482515 < baseStart_2482515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482586 : List Nat := [3, 1, 1, 4, 1, 4, 1, 1, 3, 4]
def baseStart_2482586 : Nat := 118140960795 + 2482586 * 2 ^ 59
def prefixEnd_2482586 : Nat := 4983230072969 + 3 ^ 40 * 2482586 * 2
def baseEnd_2482586 : Nat := 424919961374309701519267

theorem tailTrace_2482586 : CollatzResearch.WordTrace tailWord_2482586 prefixEnd_2482586 424919961374309701519267 := by
  unfold tailWord_2482586
  simp only [CollatzResearch.WordTrace]
  refine ⟨22636837546005597194546903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60364900122681592518791741 22636837546005597194546903)
  ·
    refine ⟨33955256319008395791820355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22636837546005597194546903 33955256319008395791820355)
    ·
      refine ⟨50932884478512593687730533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33955256319008395791820355 50932884478512593687730533)
      ·
        refine ⟨9549915839721111316449475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50932884478512593687730533 9549915839721111316449475)
        ·
          refine ⟨14324873759581666974674213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9549915839721111316449475 14324873759581666974674213)
          ·
            refine ⟨2685913829921562557751415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14324873759581666974674213 2685913829921562557751415)
            ·
              refine ⟨4028870744882343836627123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2685913829921562557751415 4028870744882343836627123)
              ·
                refine ⟨6043306117323515754940685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4028870744882343836627123 6043306117323515754940685)
                ·
                  refine ⟨2266239793996318408102757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6043306117323515754940685 2266239793996318408102757)
                  ·
                    refine ⟨424919961374309701519267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2266239793996318408102757 424919961374309701519267)
                    ·
                      rfl

theorem cell23_2482586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 3, 4].length) (baseStart_2482586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482586 prefixEnd_2482586 := by exact prefixLift 2482586
  have htrace : WordTrace (prefixWord ++ tailWord_2482586) baseStart_2482586 baseEnd_2482586 := by
    simpa [prefixWord, tailWord_2482586, baseEnd_2482586] using wordTrace_append hprefix tailTrace_2482586
  have hstable : (prefixWord ++ tailWord_2482586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482586).length < 2 ^ (prefixWord ++ tailWord_2482586).sum := by decide
  have hdescent : baseEnd_2482586 < baseStart_2482586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482599 : List Nat := [1, 1, 6, 1, 1, 3, 1, 3, 6]
def baseStart_2482599 : Nat := 118140960795 + 2482599 * 2 ^ 59
def prefixEnd_2482599 : Nat := 4983230072969 + 3 ^ 40 * 2482599 * 2
def baseEnd_2482599 : Nat := 141640728819048617077249

theorem tailTrace_2482599 : CollatzResearch.WordTrace tailWord_2482599 prefixEnd_2482599 141640728819048617077249 := by
  unfold tailWord_2482599
  simp only [CollatzResearch.WordTrace]
  refine ⟨90547824332975291998410851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60365216221983527998940567 90547824332975291998410851)
  ·
    refine ⟨135821736499462937997616277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90547824332975291998410851 135821736499462937997616277)
    ·
      refine ⟨6366643898412325218638263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 135821736499462937997616277 6366643898412325218638263)
      ·
        refine ⟨9549965847618487827957395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6366643898412325218638263 9549965847618487827957395)
        ·
          refine ⟨14324948771427731741936093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9549965847618487827957395 14324948771427731741936093)
          ·
            refine ⟨5371855789285399403226035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14324948771427731741936093 5371855789285399403226035)
            ·
              refine ⟨8057783683928099104839053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5371855789285399403226035 8057783683928099104839053)
              ·
                refine ⟨3021668881473037164314645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8057783683928099104839053 3021668881473037164314645)
                ·
                  refine ⟨141640728819048617077249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3021668881473037164314645 141640728819048617077249)
                  ·
                    rfl

theorem cell23_2482599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 6].length) (baseStart_2482599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482599 prefixEnd_2482599 := by exact prefixLift 2482599
  have htrace : WordTrace (prefixWord ++ tailWord_2482599) baseStart_2482599 baseEnd_2482599 := by
    simpa [prefixWord, tailWord_2482599, baseEnd_2482599] using wordTrace_append hprefix tailTrace_2482599
  have hstable : (prefixWord ++ tailWord_2482599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482599).length < 2 ^ (prefixWord ++ tailWord_2482599).sum := by decide
  have hdescent : baseEnd_2482599 < baseStart_2482599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482677 : List Nat := [1, 3, 5, 1, 2, 1, 2, 3, 1, 1, 3]
def baseStart_2482677 : Nat := 118140960795 + 2482677 * 2 ^ 59
def prefixEnd_2482677 : Nat := 4983230072969 + 3 ^ 40 * 2482677 * 2
def baseEnd_2482677 : Nat := 1274806610862488248519883

theorem tailTrace_2482677 : CollatzResearch.WordTrace tailWord_2482677 prefixEnd_2482677 1274806610862488248519883 := by
  unfold tailWord_2482677
  simp only [CollatzResearch.WordTrace]
  refine ⟨90550669226692711319750285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60367112817795140879833523 90550669226692711319750285)
  ·
    refine ⟨33956500960009766744906357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90550669226692711319750285 33956500960009766744906357)
    ·
      refine ⟨3183421965000915632334971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33956500960009766744906357 3183421965000915632334971)
      ·
        refine ⟨4775132947501373448502457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3183421965000915632334971 4775132947501373448502457)
        ·
          refine ⟨3581349710626030086376843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4775132947501373448502457 3581349710626030086376843)
          ·
            refine ⟨5372024565939045129565265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3581349710626030086376843 5372024565939045129565265)
            ·
              refine ⟨4029018424454283847173949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5372024565939045129565265 4029018424454283847173949)
              ·
                refine ⟨1510881909170356442690231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4029018424454283847173949 1510881909170356442690231)
                ·
                  refine ⟨2266322863755534664035347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1510881909170356442690231 2266322863755534664035347)
                  ·
                    refine ⟨3399484295633301996053021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2266322863755534664035347 3399484295633301996053021)
                    ·
                      refine ⟨1274806610862488248519883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3399484295633301996053021 1274806610862488248519883)
                      ·
                        rfl

theorem cell23_2482677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_2482677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482677 prefixEnd_2482677 := by exact prefixLift 2482677
  have htrace : WordTrace (prefixWord ++ tailWord_2482677) baseStart_2482677 baseEnd_2482677 := by
    simpa [prefixWord, tailWord_2482677, baseEnd_2482677] using wordTrace_append hprefix tailTrace_2482677
  have hstable : (prefixWord ++ tailWord_2482677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482677).length < 2 ^ (prefixWord ++ tailWord_2482677).sum := by decide
  have hdescent : baseEnd_2482677 < baseStart_2482677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482694 : List Nat := [6, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3]
def baseStart_2482694 : Nat := 118140960795 + 2482694 * 2 ^ 59
def prefixEnd_2482694 : Nat := 4983230072969 + 3 ^ 40 * 2482694 * 2
def baseEnd_2482694 : Nat := 1274815340033614682007305

theorem tailTrace_2482694 : CollatzResearch.WordTrace tailWord_2482694 prefixEnd_2482694 1274815340033614682007305 := by
  unfold tailWord_2482694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2829727789613472600722473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60367526178420748815412757 2829727789613472600722473)
  ·
    refine ⟨2122295842210104450541855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2829727789613472600722473 2122295842210104450541855)
    ·
      refine ⟨3183443763315156675812783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2122295842210104450541855 3183443763315156675812783)
      ·
        refine ⟨4775165644972735013719175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3183443763315156675812783 4775165644972735013719175)
        ·
          refine ⟨7162748467459102520578763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4775165644972735013719175 7162748467459102520578763)
          ·
            refine ⟨10744122701188653780868145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7162748467459102520578763 10744122701188653780868145)
            ·
              refine ⟨8058092025891490335651109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10744122701188653780868145 8058092025891490335651109)
              ·
                refine ⟨1510892254854654437934583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8058092025891490335651109 1510892254854654437934583)
                ·
                  refine ⟨2266338382281981656901875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1510892254854654437934583 2266338382281981656901875)
                  ·
                    refine ⟨3399507573422972485352813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2266338382281981656901875 3399507573422972485352813)
                    ·
                      refine ⟨1274815340033614682007305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3399507573422972485352813 1274815340033614682007305)
                      ·
                        rfl

theorem cell23_2482694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_2482694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482694 prefixEnd_2482694 := by exact prefixLift 2482694
  have htrace : WordTrace (prefixWord ++ tailWord_2482694) baseStart_2482694 baseEnd_2482694 := by
    simpa [prefixWord, tailWord_2482694, baseEnd_2482694] using wordTrace_append hprefix tailTrace_2482694
  have hstable : (prefixWord ++ tailWord_2482694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482694).length < 2 ^ (prefixWord ++ tailWord_2482694).sum := by decide
  have hdescent : baseEnd_2482694 < baseStart_2482694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482700 : List Nat := [2, 2, 1, 2, 4, 1, 2, 4, 1, 2, 2]
def baseStart_2482700 : Nat := 118140960795 + 2482700 * 2 ^ 59
def prefixEnd_2482700 : Nat := 4983230072969 + 3 ^ 40 * 2482700 * 2
def baseEnd_2482700 : Nat := 1274818420917541658532277

theorem tailTrace_2482700 : CollatzResearch.WordTrace tailWord_2482700 prefixEnd_2482700 1274818420917541658532277 := by
  unfold tailWord_2482700
  simp only [CollatzResearch.WordTrace]
  refine ⟨45275754052804693123918777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60367672070406257498558369 45275754052804693123918777)
  ·
    refine ⟨33956815539603519842939083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45275754052804693123918777 33956815539603519842939083)
    ·
      refine ⟨50935223309405279764408625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33956815539603519842939083 50935223309405279764408625)
      ·
        refine ⟨38201417482053959823306469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50935223309405279764408625 38201417482053959823306469)
        ·
          refine ⟨7162765777885117466869963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38201417482053959823306469 7162765777885117466869963)
          ·
            refine ⟨10744148666827676200304945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7162765777885117466869963 10744148666827676200304945)
            ·
              refine ⟨8058111500120757150228709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10744148666827676200304945 8058111500120757150228709)
              ·
                refine ⟨1510895906272641965667883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8058111500120757150228709 1510895906272641965667883)
                ·
                  refine ⟨2266343859408962948501825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1510895906272641965667883 2266343859408962948501825)
                  ·
                    refine ⟨1699757894556722211376369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2266343859408962948501825 1699757894556722211376369)
                    ·
                      refine ⟨1274818420917541658532277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1699757894556722211376369 1274818420917541658532277)
                      ·
                        rfl

theorem cell23_2482700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4, 1, 2, 2].length) (baseStart_2482700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482700 prefixEnd_2482700 := by exact prefixLift 2482700
  have htrace : WordTrace (prefixWord ++ tailWord_2482700) baseStart_2482700 baseEnd_2482700 := by
    simpa [prefixWord, tailWord_2482700, baseEnd_2482700] using wordTrace_append hprefix tailTrace_2482700
  have hstable : (prefixWord ++ tailWord_2482700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482700).length < 2 ^ (prefixWord ++ tailWord_2482700).sum := by decide
  have hdescent : baseEnd_2482700 < baseStart_2482700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482716 : List Nat := [2, 2, 3, 1, 2, 2, 3, 1, 1, 3, 3]
def baseStart_2482716 : Nat := 118140960795 + 2482716 * 2 ^ 59
def prefixEnd_2482716 : Nat := 4983230072969 + 3 ^ 40 * 2482716 * 2
def baseEnd_2482716 : Nat := 1274826636608013595932203

theorem tailTrace_2482716 : CollatzResearch.WordTrace tailWord_2482716 prefixEnd_2482716 1274826636608013595932203 := by
  unfold tailWord_2482716
  simp only [CollatzResearch.WordTrace]
  refine ⟨45276045836775710490210001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60368061115700947320280001 45276045836775710490210001)
  ·
    refine ⟨33957034377581782867657501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45276045836775710490210001 33957034377581782867657501)
    ·
      refine ⟨12733887891593168575371563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33957034377581782867657501 12733887891593168575371563)
      ·
        refine ⟨19100831837389752863057345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12733887891593168575371563 19100831837389752863057345)
        ·
          refine ⟨14325623878042314647293009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19100831837389752863057345 14325623878042314647293009)
          ·
            refine ⟨10744217908531735985469757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14325623878042314647293009 10744217908531735985469757)
            ·
              refine ⟨4029081715699400994551159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10744217908531735985469757 4029081715699400994551159)
              ·
                refine ⟨6043622573549101491826739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4029081715699400994551159 6043622573549101491826739)
                ·
                  refine ⟨9065433860323652237740109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6043622573549101491826739 9065433860323652237740109)
                  ·
                    refine ⟨3399537697621369589152541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9065433860323652237740109 3399537697621369589152541)
                    ·
                      refine ⟨1274826636608013595932203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3399537697621369589152541 1274826636608013595932203)
                      ·
                        rfl

theorem cell23_2482716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_2482716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482716 prefixEnd_2482716 := by exact prefixLift 2482716
  have htrace : WordTrace (prefixWord ++ tailWord_2482716) baseStart_2482716 baseEnd_2482716 := by
    simpa [prefixWord, tailWord_2482716, baseEnd_2482716] using wordTrace_append hprefix tailTrace_2482716
  have hstable : (prefixWord ++ tailWord_2482716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482716).length < 2 ^ (prefixWord ++ tailWord_2482716).sum := by decide
  have hdescent : baseEnd_2482716 < baseStart_2482716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482732 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 1, 8]
def baseStart_2482732 : Nat := 118140960795 + 2482732 * 2 ^ 59
def prefixEnd_2482732 : Nat := 4983230072969 + 3 ^ 40 * 2482732 * 2
def baseEnd_2482732 : Nat := 424944950766161844444043

theorem tailTrace_2482732 : CollatzResearch.WordTrace tailWord_2482732 prefixEnd_2482732 424944950766161844444043 := by
  unfold tailWord_2482732
  simp only [CollatzResearch.WordTrace]
  refine ⟨45276337620746727856501225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60368450160995637142001633 45276337620746727856501225)
  ·
    refine ⟨33957253215560045892375919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45276337620746727856501225 33957253215560045892375919)
    ·
      refine ⟨50935879823340068838563879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33957253215560045892375919 50935879823340068838563879)
      ·
        refine ⟨76403819735010103257845819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50935879823340068838563879 76403819735010103257845819)
        ·
          refine ⟨114605729602515154886768729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76403819735010103257845819 114605729602515154886768729)
          ·
            refine ⟨85954297201886366165076547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114605729602515154886768729 85954297201886366165076547)
            ·
              refine ⟨128931445802829549247614821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85954297201886366165076547 128931445802829549247614821)
              ·
                refine ⟨24174646088030540483927779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128931445802829549247614821 24174646088030540483927779)
                ·
                  refine ⟨36261969132045810725891669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24174646088030540483927779 36261969132045810725891669)
                  ·
                    refine ⟨424944950766161844444043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36261969132045810725891669 424944950766161844444043)
                    ·
                      rfl

theorem cell23_2482732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_2482732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482732 prefixEnd_2482732 := by exact prefixLift 2482732
  have htrace : WordTrace (prefixWord ++ tailWord_2482732) baseStart_2482732 baseEnd_2482732 := by
    simpa [prefixWord, tailWord_2482732, baseEnd_2482732] using wordTrace_append hprefix tailTrace_2482732
  have hstable : (prefixWord ++ tailWord_2482732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482732).length < 2 ^ (prefixWord ++ tailWord_2482732).sum := by decide
  have hdescent : baseEnd_2482732 < baseStart_2482732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482734 : List Nat := [4, 1, 3, 1, 3, 2, 1, 3, 1, 2, 2]
def baseStart_2482734 : Nat := 118140960795 + 2482734 * 2 ^ 59
def prefixEnd_2482734 : Nat := 4983230072969 + 3 ^ 40 * 2482734 * 2
def baseEnd_2482734 : Nat := 1274835879259794525507121

theorem tailTrace_2482734 : CollatzResearch.WordTrace tailWord_2482734 prefixEnd_2482734 1274835879259794525507121 := by
  unfold tailWord_2482734
  simp only [CollatzResearch.WordTrace]
  refine ⟨11319093523435776256821907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60368498791657473369716837 11319093523435776256821907)
  ·
    refine ⟨16978640285153664385232861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11319093523435776256821907 16978640285153664385232861)
    ·
      refine ⟨6366990106932624144462323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16978640285153664385232861 6366990106932624144462323)
      ·
        refine ⟨9550485160398936216693485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6366990106932624144462323 9550485160398936216693485)
        ·
          refine ⟨3581431935149601081260057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9550485160398936216693485 3581431935149601081260057)
          ·
            refine ⟨2686073951362200810945043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3581431935149601081260057 2686073951362200810945043)
            ·
              refine ⟨4029110927043301216417565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2686073951362200810945043 4029110927043301216417565)
              ·
                refine ⟨1510916597641237956156587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4029110927043301216417565 1510916597641237956156587)
                ·
                  refine ⟨2266374896461856934234881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1510916597641237956156587 2266374896461856934234881)
                  ·
                    refine ⟨1699781172346392700676161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2266374896461856934234881 1699781172346392700676161)
                    ·
                      refine ⟨1274835879259794525507121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1699781172346392700676161 1274835879259794525507121)
                      ·
                        rfl

theorem cell23_2482734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_2482734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482734 prefixEnd_2482734 := by exact prefixLift 2482734
  have htrace : WordTrace (prefixWord ++ tailWord_2482734) baseStart_2482734 baseEnd_2482734 := by
    simpa [prefixWord, tailWord_2482734, baseEnd_2482734] using wordTrace_append hprefix tailTrace_2482734
  have hstable : (prefixWord ++ tailWord_2482734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482734).length < 2 ^ (prefixWord ++ tailWord_2482734).sum := by decide
  have hdescent : baseEnd_2482734 < baseStart_2482734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482813 : List Nat := [1, 4, 1, 1, 5, 1, 1, 4, 5]
def baseStart_2482813 : Nat := 118140960795 + 2482813 * 2 ^ 59
def prefixEnd_2482813 : Nat := 4983230072969 + 3 ^ 40 * 2482813 * 2
def baseEnd_2482813 : Nat := 141652938247944412935473

theorem tailTrace_2482813 : CollatzResearch.WordTrace tailWord_2482813 prefixEnd_2482813 141652938247944412935473 := by
  unfold tailWord_2482813
  simp only [CollatzResearch.WordTrace]
  refine ⟨90555629554200006546701093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60370419702800004364467395 90555629554200006546701093)
  ·
    refine ⟨16979180541412501227506455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90555629554200006546701093 16979180541412501227506455)
    ·
      refine ⟨25468770812118751841259683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16979180541412501227506455 25468770812118751841259683)
      ·
        refine ⟨38203156218178127761889525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25468770812118751841259683 38203156218178127761889525)
        ·
          refine ⟨3581545895454199477677143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38203156218178127761889525 3581545895454199477677143)
          ·
            refine ⟨5372318843181299216515715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3581545895454199477677143 5372318843181299216515715)
            ·
              refine ⟨8058478264771948824773573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5372318843181299216515715 8058478264771948824773573)
              ·
                refine ⟨1510964674644740404645045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8058478264771948824773573 1510964674644740404645045)
                ·
                  refine ⟨141652938247944412935473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1510964674644740404645045 141652938247944412935473)
                  ·
                    rfl

theorem cell23_2482813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4, 5].length) (baseStart_2482813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482813 prefixEnd_2482813 := by exact prefixLift 2482813
  have htrace : WordTrace (prefixWord ++ tailWord_2482813) baseStart_2482813 baseEnd_2482813 := by
    simpa [prefixWord, tailWord_2482813, baseEnd_2482813] using wordTrace_append hprefix tailTrace_2482813
  have hstable : (prefixWord ++ tailWord_2482813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482813).length < 2 ^ (prefixWord ++ tailWord_2482813).sum := by decide
  have hdescent : baseEnd_2482813 < baseStart_2482813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482816 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 2, 5, 2]
def baseStart_2482816 : Nat := 118140960795 + 2482816 * 2 ^ 59
def prefixEnd_2482816 : Nat := 4983230072969 + 3 ^ 40 * 2482816 * 2
def baseEnd_2482816 : Nat := 1274877984673463204681743

theorem tailTrace_2482816 : CollatzResearch.WordTrace tailWord_2482816 prefixEnd_2482816 1274877984673463204681743 := by
  unfold tailWord_2482816
  simp only [CollatzResearch.WordTrace]
  refine ⟨45277869486594569029530151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60370492648792758706040201 45277869486594569029530151)
  ·
    refine ⟨67916804229891853544295227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45277869486594569029530151 67916804229891853544295227)
    ·
      refine ⟨101875206344837780316442841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67916804229891853544295227 101875206344837780316442841)
      ·
        refine ⟨76406404758628335237332131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101875206344837780316442841 76406404758628335237332131)
        ·
          refine ⟨114609607137942502855998197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76406404758628335237332131 114609607137942502855998197)
          ·
            refine ⟨10744650669182109642749831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114609607137942502855998197 10744650669182109642749831)
            ·
              refine ⟨16116976003773164464124747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10744650669182109642749831 16116976003773164464124747)
              ·
                refine ⟨24175464005659746696187121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16116976003773164464124747 24175464005659746696187121)
                ·
                  refine ⟨18131598004244810022140341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24175464005659746696187121 18131598004244810022140341)
                  ·
                    refine ⟨1699837312897950939575657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18131598004244810022140341 1699837312897950939575657)
                    ·
                      refine ⟨1274877984673463204681743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1699837312897950939575657 1274877984673463204681743)
                      ·
                        rfl

theorem cell23_2482816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 2, 5, 2].length) (baseStart_2482816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482816 prefixEnd_2482816 := by exact prefixLift 2482816
  have htrace : WordTrace (prefixWord ++ tailWord_2482816) baseStart_2482816 baseEnd_2482816 := by
    simpa [prefixWord, tailWord_2482816, baseEnd_2482816] using wordTrace_append hprefix tailTrace_2482816
  have hstable : (prefixWord ++ tailWord_2482816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482816).length < 2 ^ (prefixWord ++ tailWord_2482816).sum := by decide
  have hdescent : baseEnd_2482816 < baseStart_2482816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482819 : List Nat := [1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 5]
def baseStart_2482819 : Nat := 118140960795 + 2482819 * 2 ^ 59
def prefixEnd_2482819 : Nat := 4983230072969 + 3 ^ 40 * 2482819 * 2
def baseEnd_2482819 : Nat := 1274879525115426692944229

theorem tailTrace_2482819 : CollatzResearch.WordTrace tailWord_2482819 prefixEnd_2482819 1274879525115426692944229 := by
  unfold tailWord_2482819
  simp only [CollatzResearch.WordTrace]
  refine ⟨90555848392178269571419511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60370565594785513047613007 90555848392178269571419511)
  ·
    refine ⟨135833772588267404357129267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90555848392178269571419511 135833772588267404357129267)
    ·
      refine ⟨203750658882401106535693901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135833772588267404357129267 203750658882401106535693901)
      ·
        refine ⟨76406497080900414950885213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203750658882401106535693901 76406497080900414950885213)
        ·
          refine ⟨28652436405337655606581955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76406497080900414950885213 28652436405337655606581955)
          ·
            refine ⟨42978654608006483409872933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28652436405337655606581955 42978654608006483409872933)
            ·
              refine ⟨8058497739001215639351175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42978654608006483409872933 8058497739001215639351175)
              ·
                refine ⟨12087746608501823459026763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8058497739001215639351175 12087746608501823459026763)
                ·
                  refine ⟨18131619912752735188540145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12087746608501823459026763 18131619912752735188540145)
                  ·
                    refine ⟨13598714934564551391405109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18131619912752735188540145 13598714934564551391405109)
                    ·
                      refine ⟨1274879525115426692944229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13598714934564551391405109 1274879525115426692944229)
                      ·
                        rfl

theorem cell23_2482819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_2482819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482819 prefixEnd_2482819 := by exact prefixLift 2482819
  have htrace : WordTrace (prefixWord ++ tailWord_2482819) baseStart_2482819 baseEnd_2482819 := by
    simpa [prefixWord, tailWord_2482819, baseEnd_2482819] using wordTrace_append hprefix tailTrace_2482819
  have hstable : (prefixWord ++ tailWord_2482819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482819).length < 2 ^ (prefixWord ++ tailWord_2482819).sum := by decide
  have hdescent : baseEnd_2482819 < baseStart_2482819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482866 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3]
def baseStart_2482866 : Nat := 118140960795 + 2482866 * 2 ^ 59
def prefixEnd_2482866 : Nat := 4983230072969 + 3 ^ 40 * 2482866 * 2
def baseEnd_2482866 : Nat := 1274903658706188009056513

theorem tailTrace_2482866 : CollatzResearch.WordTrace tailWord_2482866 prefixEnd_2482866 1274903658706188009056513 := by
  unfold tailWord_2482866
  simp only [CollatzResearch.WordTrace]
  refine ⟨22639390655751999149595113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60371708415338664398920301 22639390655751999149595113)
  ·
    refine ⟨16979542991813999362196335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22639390655751999149595113 16979542991813999362196335)
    ·
      refine ⟨25469314487720999043294503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16979542991813999362196335 25469314487720999043294503)
      ·
        refine ⟨38203971731581498564941755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25469314487720999043294503 38203971731581498564941755)
        ·
          refine ⟨57305957597372247847412633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38203971731581498564941755 57305957597372247847412633)
          ·
            refine ⟨42979468198029185885559475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57305957597372247847412633 42979468198029185885559475)
            ·
              refine ⟨64469202297043778828339213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42979468198029185885559475 64469202297043778828339213)
              ·
                refine ⟨24175950861391417060627205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64469202297043778828339213 24175950861391417060627205)
                ·
                  refine ⟨4532990786510890698867601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24175950861391417060627205 4532990786510890698867601)
                  ·
                    refine ⟨3399743089883168024150701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4532990786510890698867601 3399743089883168024150701)
                    ·
                      refine ⟨1274903658706188009056513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3399743089883168024150701 1274903658706188009056513)
                      ·
                        rfl

theorem cell23_2482866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_2482866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482866 prefixEnd_2482866 := by exact prefixLift 2482866
  have htrace : WordTrace (prefixWord ++ tailWord_2482866) baseStart_2482866 baseEnd_2482866 := by
    simpa [prefixWord, tailWord_2482866, baseEnd_2482866] using wordTrace_append hprefix tailTrace_2482866
  have hstable : (prefixWord ++ tailWord_2482866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482866).length < 2 ^ (prefixWord ++ tailWord_2482866).sum := by decide
  have hdescent : baseEnd_2482866 < baseStart_2482866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482930 : List Nat := [3, 2, 1, 3, 1, 2, 3, 1, 3, 1, 3]
def baseStart_2482930 : Nat := 118140960795 + 2482930 * 2 ^ 59
def prefixEnd_2482930 : Nat := 4983230072969 + 3 ^ 40 * 2482930 * 2
def baseEnd_2482930 : Nat := 1274936521468075758656219

theorem tailTrace_2482930 : CollatzResearch.WordTrace tailWord_2482930 prefixEnd_2482930 1274936521468075758656219 := by
  unfold tailWord_2482930
  simp only [CollatzResearch.WordTrace]
  refine ⟨22639974223694033882177561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60373264596517423685806829 22639974223694033882177561)
  ·
    refine ⟨16979980667770525411633171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22639974223694033882177561 16979980667770525411633171)
    ·
      refine ⟨25469971001655788117449757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16979980667770525411633171 25469971001655788117449757)
      ·
        refine ⟨9551239125620920544043659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25469971001655788117449757 9551239125620920544043659)
        ·
          refine ⟨14326858688431380816065489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9551239125620920544043659 14326858688431380816065489)
          ·
            refine ⟨10745144016323535612049117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14326858688431380816065489 10745144016323535612049117)
            ·
              refine ⟨4029429006121325854518419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10745144016323535612049117 4029429006121325854518419)
              ·
                refine ⟨6044143509181988781777629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4029429006121325854518419 6044143509181988781777629)
                ·
                  refine ⟨2266553815943245793166611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6044143509181988781777629 2266553815943245793166611)
                  ·
                    refine ⟨3399830723914868689749917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2266553815943245793166611 3399830723914868689749917)
                    ·
                      refine ⟨1274936521468075758656219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3399830723914868689749917 1274936521468075758656219)
                      ·
                        rfl

theorem cell23_2482930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_2482930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482930 prefixEnd_2482930 := by exact prefixLift 2482930
  have htrace : WordTrace (prefixWord ++ tailWord_2482930) baseStart_2482930 baseEnd_2482930 := by
    simpa [prefixWord, tailWord_2482930, baseEnd_2482930] using wordTrace_append hprefix tailTrace_2482930
  have hstable : (prefixWord ++ tailWord_2482930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482930).length < 2 ^ (prefixWord ++ tailWord_2482930).sum := by decide
  have hdescent : baseEnd_2482930 < baseStart_2482930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482936 : List Nat := [2, 1, 2, 1, 1, 2, 4, 2, 3, 1, 4]
def baseStart_2482936 : Nat := 118140960795 + 2482936 * 2 ^ 59
def prefixEnd_2482936 : Nat := 4983230072969 + 3 ^ 40 * 2482936 * 2
def baseEnd_2482936 : Nat := 1274939602352002735181191

theorem tailTrace_2482936 : CollatzResearch.WordTrace tailWord_2482936 prefixEnd_2482936 1274939602352002735181191 := by
  unfold tailWord_2482936
  simp only [CollatzResearch.WordTrace]
  refine ⟨45280057866377199276714331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60373410488502932368952441 45280057866377199276714331)
  ·
    refine ⟨67920086799565798915071497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45280057866377199276714331 67920086799565798915071497)
    ·
      refine ⟨50940065099674349186303623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67920086799565798915071497 50940065099674349186303623)
      ·
        refine ⟨76410097649511523779455435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50940065099674349186303623 76410097649511523779455435)
        ·
          refine ⟨114615146474267285669183153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76410097649511523779455435 114615146474267285669183153)
          ·
            refine ⟨85961359855700464251887365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114615146474267285669183153 85961359855700464251887365)
            ·
              refine ⟨16117754972943837047228881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85961359855700464251887365 16117754972943837047228881)
              ·
                refine ⟨12088316229707877785421661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16117754972943837047228881 12088316229707877785421661)
                ·
                  refine ⟨4533118586140454169533123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12088316229707877785421661 4533118586140454169533123)
                  ·
                    refine ⟨6799677879210681254299685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4533118586140454169533123 6799677879210681254299685)
                    ·
                      refine ⟨1274939602352002735181191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6799677879210681254299685 1274939602352002735181191)
                      ·
                        rfl

theorem cell23_2482936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_2482936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482936 prefixEnd_2482936 := by exact prefixLift 2482936
  have htrace : WordTrace (prefixWord ++ tailWord_2482936) baseStart_2482936 baseEnd_2482936 := by
    simpa [prefixWord, tailWord_2482936, baseEnd_2482936] using wordTrace_append hprefix tailTrace_2482936
  have hstable : (prefixWord ++ tailWord_2482936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482936).length < 2 ^ (prefixWord ++ tailWord_2482936).sum := by decide
  have hdescent : baseEnd_2482936 < baseStart_2482936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482939 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 5]
def baseStart_2482939 : Nat := 118140960795 + 2482939 * 2 ^ 59
def prefixEnd_2482939 : Nat := 4983230072969 + 3 ^ 40 * 2482939 * 2
def baseEnd_2482939 : Nat := 1274941142793966223443677

theorem tailTrace_2482939 : CollatzResearch.WordTrace tailWord_2482939 prefixEnd_2482939 1274941142793966223443677 := by
  unfold tailWord_2482939
  simp only [CollatzResearch.WordTrace]
  refine ⟨90560225151743530065787871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60373483434495686710525247 90560225151743530065787871)
  ·
    refine ⟨135840337727615295098681807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90560225151743530065787871 135840337727615295098681807)
    ·
      refine ⟨203760506591422942648022711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135840337727615295098681807 203760506591422942648022711)
      ·
        refine ⟨305640759887134413972034067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203760506591422942648022711 305640759887134413972034067)
        ·
          refine ⟨458461139830701620958051101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305640759887134413972034067 458461139830701620958051101)
          ·
            refine ⟨171922927436513107859269163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 458461139830701620958051101 171922927436513107859269163)
            ·
              refine ⟨257884391154769661788903745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171922927436513107859269163 257884391154769661788903745)
              ·
                refine ⟨193413293366077246341677809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 257884391154769661788903745 193413293366077246341677809)
                ·
                  refine ⟨145059970024557934756258357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 193413293366077246341677809 145059970024557934756258357)
                  ·
                    refine ⟨13599372189802306383399221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 145059970024557934756258357 13599372189802306383399221)
                    ·
                      refine ⟨1274941142793966223443677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13599372189802306383399221 1274941142793966223443677)
                      ·
                        rfl

theorem cell23_2482939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 5].length) (baseStart_2482939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482939 prefixEnd_2482939 := by exact prefixLift 2482939
  have htrace : WordTrace (prefixWord ++ tailWord_2482939) baseStart_2482939 baseEnd_2482939 := by
    simpa [prefixWord, tailWord_2482939, baseEnd_2482939] using wordTrace_append hprefix tailTrace_2482939
  have hstable : (prefixWord ++ tailWord_2482939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482939).length < 2 ^ (prefixWord ++ tailWord_2482939).sum := by decide
  have hdescent : baseEnd_2482939 < baseStart_2482939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482953 : List Nat := [1, 2, 1, 1, 3, 2, 5, 2, 1, 1, 4]
def baseStart_2482953 : Nat := 118140960795 + 2482953 * 2 ^ 59
def prefixEnd_2482953 : Nat := 4983230072969 + 3 ^ 40 * 2482953 * 2
def baseEnd_2482953 : Nat := 1274948331523129168668613

theorem tailTrace_2482953 : CollatzResearch.WordTrace tailWord_2482953 prefixEnd_2482953 1274948331523129168668613 := by
  unfold tailWord_2482953
  simp only [CollatzResearch.WordTrace]
  refine ⟨90560735773692810456797513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60373823849128540304531675 90560735773692810456797513)
  ·
    refine ⟨67920551830269607842598135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90560735773692810456797513 67920551830269607842598135)
    ·
      refine ⟨101880827745404411763897203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67920551830269607842598135 101880827745404411763897203)
      ·
        refine ⟨152821241618106617645845805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101880827745404411763897203 152821241618106617645845805)
        ·
          refine ⟨57307965606789981617192177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152821241618106617645845805 57307965606789981617192177)
          ·
            refine ⟨42980974205092486212894133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57307965606789981617192177 42980974205092486212894133)
            ·
              refine ⟨4029466331727420582458825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42980974205092486212894133 4029466331727420582458825)
              ·
                refine ⟨3022099748795565436844119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4029466331727420582458825 3022099748795565436844119)
                ·
                  refine ⟨4533149623193348155266179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3022099748795565436844119 4533149623193348155266179)
                  ·
                    refine ⟨6799724434790022232899269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4533149623193348155266179 6799724434790022232899269)
                    ·
                      refine ⟨1274948331523129168668613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6799724434790022232899269 1274948331523129168668613)
                      ·
                        rfl

theorem cell23_2482953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 1, 4].length) (baseStart_2482953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482953 prefixEnd_2482953 := by exact prefixLift 2482953
  have htrace : WordTrace (prefixWord ++ tailWord_2482953) baseStart_2482953 baseEnd_2482953 := by
    simpa [prefixWord, tailWord_2482953, baseEnd_2482953] using wordTrace_append hprefix tailTrace_2482953
  have hstable : (prefixWord ++ tailWord_2482953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482953).length < 2 ^ (prefixWord ++ tailWord_2482953).sum := by decide
  have hdescent : baseEnd_2482953 < baseStart_2482953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482959 : List Nat := [1, 1, 2, 1, 1, 1, 5, 11]
def baseStart_2482959 : Nat := 118140960795 + 2482959 * 2 ^ 59
def prefixEnd_2482959 : Nat := 4983230072969 + 3 ^ 40 * 2482959 * 2
def baseEnd_2482959 : Nat := 47220422681742820192355

theorem tailTrace_2482959 : CollatzResearch.WordTrace tailWord_2482959 prefixEnd_2482959 47220422681742820192355 := by
  unfold tailWord_2482959
  simp only [CollatzResearch.WordTrace]
  refine ⟨90560954611671073481515931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60373969741114048987677287 90560954611671073481515931)
  ·
    refine ⟨135841431917506610222273897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90560954611671073481515931 135841431917506610222273897)
    ·
      refine ⟨101881073938129957666705423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135841431917506610222273897 101881073938129957666705423)
      ·
        refine ⟨152821610907194936500058135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101881073938129957666705423 152821610907194936500058135)
        ·
          refine ⟨229232416360792404750087203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152821610907194936500058135 229232416360792404750087203)
          ·
            refine ⟨343848624541188607125130805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229232416360792404750087203 343848624541188607125130805)
            ·
              refine ⟨32235808550736431917981013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 343848624541188607125130805 32235808550736431917981013)
              ·
                refine ⟨47220422681742820192355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 32235808550736431917981013 47220422681742820192355)
                ·
                  rfl

theorem cell23_2482959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 11].length) (baseStart_2482959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482959 prefixEnd_2482959 := by exact prefixLift 2482959
  have htrace : WordTrace (prefixWord ++ tailWord_2482959) baseStart_2482959 baseEnd_2482959 := by
    simpa [prefixWord, tailWord_2482959, baseEnd_2482959] using wordTrace_append hprefix tailTrace_2482959
  have hstable : (prefixWord ++ tailWord_2482959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482959).length < 2 ^ (prefixWord ++ tailWord_2482959).sum := by decide
  have hdescent : baseEnd_2482959 < baseStart_2482959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482970 : List Nat := [3, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4]
def baseStart_2482970 : Nat := 118140960795 + 2482970 * 2 ^ 59
def prefixEnd_2482970 : Nat := 4983230072969 + 3 ^ 40 * 2482970 * 2
def baseEnd_2482970 : Nat := 1274957060694255602156035

theorem tailTrace_2482970 : CollatzResearch.WordTrace tailWord_2482970 prefixEnd_2482970 1274957060694255602156035 := by
  unfold tailWord_2482970
  simp only [CollatzResearch.WordTrace]
  refine ⟨22640338953657805590041591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60374237209754148240110909 22640338953657805590041591)
  ·
    refine ⟨33960508430486708385062387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22640338953657805590041591 33960508430486708385062387)
    ·
      refine ⟨50940762645730062577593581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33960508430486708385062387 50940762645730062577593581)
      ·
        refine ⟨19102785992148773466597593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50940762645730062577593581 19102785992148773466597593)
        ·
          refine ⟨14327089494111580099948195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19102785992148773466597593 14327089494111580099948195)
          ·
            refine ⟨21490634241167370149922293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14327089494111580099948195 21490634241167370149922293)
            ·
              refine ⟨2014746960109440951555215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21490634241167370149922293 2014746960109440951555215)
              ·
                refine ⟨3022120440164161427332823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2014746960109440951555215 3022120440164161427332823)
                ·
                  refine ⟨4533180660246242140999235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3022120440164161427332823 4533180660246242140999235)
                  ·
                    refine ⟨6799770990369363211498853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4533180660246242140999235 6799770990369363211498853)
                    ·
                      refine ⟨1274957060694255602156035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6799770990369363211498853 1274957060694255602156035)
                      ·
                        rfl

theorem cell23_2482970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_2482970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482970 prefixEnd_2482970 := by exact prefixLift 2482970
  have htrace : WordTrace (prefixWord ++ tailWord_2482970) baseStart_2482970 baseEnd_2482970 := by
    simpa [prefixWord, tailWord_2482970, baseEnd_2482970] using wordTrace_append hprefix tailTrace_2482970
  have hstable : (prefixWord ++ tailWord_2482970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482970).length < 2 ^ (prefixWord ++ tailWord_2482970).sum := by decide
  have hdescent : baseEnd_2482970 < baseStart_2482970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482990 : List Nat := [4, 1, 3, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_2482990 : Nat := 118140960795 + 2482990 * 2 ^ 59
def prefixEnd_2482990 : Nat := 4983230072969 + 3 ^ 40 * 2482990 * 2
def baseEnd_2482990 : Nat := 1274967330307345523905943

theorem tailTrace_2482990 : CollatzResearch.WordTrace tailWord_2482990 prefixEnd_2482990 1274967330307345523905943 := by
  unfold tailWord_2482990
  simp only [CollatzResearch.WordTrace]
  refine ⟨11320260659319845721986803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60374723516372510517262949 11320260659319845721986803)
  ·
    refine ⟨16980390988979768582980205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11320260659319845721986803 16980390988979768582980205)
    ·
      refine ⟨6367646620867413218617577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16980390988979768582980205 6367646620867413218617577)
      ·
        refine ⟨4775734965650559913963183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6367646620867413218617577 4775734965650559913963183)
        ·
          refine ⟨7163602448475839870944775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4775734965650559913963183 7163602448475839870944775)
          ·
            refine ⟨10745403672713759806417163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7163602448475839870944775 10745403672713759806417163)
            ·
              refine ⟨16118105509070639709625745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10745403672713759806417163 16118105509070639709625745)
              ·
                refine ⟨12088579131802979782219309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16118105509070639709625745 12088579131802979782219309)
                ·
                  refine ⟨4533217174426117418332241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12088579131802979782219309 4533217174426117418332241)
                  ·
                    refine ⟨3399912880819588063749181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4533217174426117418332241 3399912880819588063749181)
                    ·
                      refine ⟨1274967330307345523905943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3399912880819588063749181 1274967330307345523905943)
                      ·
                        rfl

theorem cell23_2482990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_2482990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2482990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2482990 prefixEnd_2482990 := by exact prefixLift 2482990
  have htrace : WordTrace (prefixWord ++ tailWord_2482990) baseStart_2482990 baseEnd_2482990 := by
    simpa [prefixWord, tailWord_2482990, baseEnd_2482990] using wordTrace_append hprefix tailTrace_2482990
  have hstable : (prefixWord ++ tailWord_2482990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482990).length < 2 ^ (prefixWord ++ tailWord_2482990).sum := by decide
  have hdescent : baseEnd_2482990 < baseStart_2482990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483016 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 2, 2, 5]
def baseStart_2483016 : Nat := 118140960795 + 2483016 * 2 ^ 59
def prefixEnd_2483016 : Nat := 4983230072969 + 3 ^ 40 * 2483016 * 2
def baseEnd_2483016 : Nat := 1274980680804362422180823

theorem tailTrace_2483016 : CollatzResearch.WordTrace tailWord_2483016 prefixEnd_2483016 1274980680804362422180823 := by
  unfold tailWord_2483016
  simp only [CollatzResearch.WordTrace]
  refine ⟨45281516786232286108170451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60375355714976381477560601 45281516786232286108170451)
  ·
    refine ⟨67922275179348429162255677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45281516786232286108170451 67922275179348429162255677)
    ·
      refine ⟨25470853192255660935845879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67922275179348429162255677 25470853192255660935845879)
      ·
        refine ⟨38206279788383491403768819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25470853192255660935845879 38206279788383491403768819)
        ·
          refine ⟨57309419682575237105653229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38206279788383491403768819 57309419682575237105653229)
          ·
            refine ⟨21491032380965713914619961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57309419682575237105653229 21491032380965713914619961)
            ·
              refine ⟨16118274285724285435964971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21491032380965713914619961 16118274285724285435964971)
              ·
                refine ⟨24177411428586428153947457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16118274285724285435964971 24177411428586428153947457)
                ·
                  refine ⟨18133058571439821115460593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24177411428586428153947457 18133058571439821115460593)
                  ·
                    refine ⟨13599793928579865836595445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18133058571439821115460593 13599793928579865836595445)
                    ·
                      refine ⟨1274980680804362422180823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13599793928579865836595445 1274980680804362422180823)
                      ·
                        rfl

theorem cell23_2483016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_2483016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483016 prefixEnd_2483016 := by exact prefixLift 2483016
  have htrace : WordTrace (prefixWord ++ tailWord_2483016) baseStart_2483016 baseEnd_2483016 := by
    simpa [prefixWord, tailWord_2483016, baseEnd_2483016] using wordTrace_append hprefix tailTrace_2483016
  have hstable : (prefixWord ++ tailWord_2483016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483016).length < 2 ^ (prefixWord ++ tailWord_2483016).sum := by decide
  have hdescent : baseEnd_2483016 < baseStart_2483016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483021 : List Nat := [1, 6, 1, 2, 3, 1, 2, 1, 1, 1, 4]
def baseStart_2483021 : Nat := 118140960795 + 2483021 * 2 ^ 59
def prefixEnd_2483021 : Nat := 4983230072969 + 3 ^ 40 * 2483021 * 2
def baseEnd_2483021 : Nat := 1274983248207634902618301

theorem tailTrace_2483021 : CollatzResearch.WordTrace tailWord_2483021 prefixEnd_2483021 1274983248207634902618301 := by
  unfold tailWord_2483021
  simp only [CollatzResearch.WordTrace]
  refine ⟨90563215937446458070272917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60375477291630972046848611 90563215937446458070272917)
  ·
    refine ⟨4245150747067802722044043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 90563215937446458070272917 4245150747067802722044043)
    ·
      refine ⟨6367726120601704083066065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4245150747067802722044043 6367726120601704083066065)
      ·
        refine ⟨4775794590451278062299549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6367726120601704083066065 4775794590451278062299549)
        ·
          refine ⟨1790922971419229273362331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4775794590451278062299549 1790922971419229273362331)
          ·
            refine ⟨2686384457128843910043497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1790922971419229273362331 2686384457128843910043497)
            ·
              refine ⟨2014788342846632932532623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2686384457128843910043497 2014788342846632932532623)
              ·
                refine ⟨3022182514269949398798935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2014788342846632932532623 3022182514269949398798935)
                ·
                  refine ⟨4533273771404924098198403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3022182514269949398798935 4533273771404924098198403)
                  ·
                    refine ⟨6799910657107386147297605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4533273771404924098198403 6799910657107386147297605)
                    ·
                      refine ⟨1274983248207634902618301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6799910657107386147297605 1274983248207634902618301)
                      ·
                        rfl

theorem cell23_2483021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_2483021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483021 prefixEnd_2483021 := by exact prefixLift 2483021
  have htrace : WordTrace (prefixWord ++ tailWord_2483021) baseStart_2483021 baseEnd_2483021 := by
    simpa [prefixWord, tailWord_2483021, baseEnd_2483021] using wordTrace_append hprefix tailTrace_2483021
  have hstable : (prefixWord ++ tailWord_2483021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483021).length < 2 ^ (prefixWord ++ tailWord_2483021).sum := by decide
  have hdescent : baseEnd_2483021 < baseStart_2483021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483054 : List Nat := [4, 1, 2, 3, 3, 1, 1, 1, 1, 3, 3]
def baseStart_2483054 : Nat := 118140960795 + 2483054 * 2 ^ 59
def prefixEnd_2483054 : Nat := 4983230072969 + 3 ^ 40 * 2483054 * 2
def baseEnd_2483054 : Nat := 1275000193069233273505649

theorem tailTrace_2483054 : CollatzResearch.WordTrace tailWord_2483054 prefixEnd_2483054 1275000193069233273505649 := by
  unfold tailWord_2483054
  simp only [CollatzResearch.WordTrace]
  refine ⟨11320552443290863088278027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60376279697551269804149477 11320552443290863088278027)
  ·
    refine ⟨16980828664936294632417041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11320552443290863088278027 16980828664936294632417041)
    ·
      refine ⟨12735621498702220974312781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16980828664936294632417041 12735621498702220974312781)
      ·
        refine ⟨4775858062013332865367293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12735621498702220974312781 4775858062013332865367293)
        ·
          refine ⟨1790946773254999824512735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4775858062013332865367293 1790946773254999824512735)
          ·
            refine ⟨2686420159882499736769103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1790946773254999824512735 2686420159882499736769103)
            ·
              refine ⟨4029630239823749605153655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2686420159882499736769103 4029630239823749605153655)
              ·
                refine ⟨6044445359735624407730483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4029630239823749605153655 6044445359735624407730483)
                ·
                  refine ⟨9066668039603436611595725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6044445359735624407730483 9066668039603436611595725)
                  ·
                    refine ⟨3400000514851288729348397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9066668039603436611595725 3400000514851288729348397)
                    ·
                      refine ⟨1275000193069233273505649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3400000514851288729348397 1275000193069233273505649)
                      ·
                        rfl

theorem cell23_2483054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_2483054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483054 prefixEnd_2483054 := by exact prefixLift 2483054
  have htrace : WordTrace (prefixWord ++ tailWord_2483054) baseStart_2483054 baseEnd_2483054 := by
    simpa [prefixWord, tailWord_2483054, baseEnd_2483054] using wordTrace_append hprefix tailTrace_2483054
  have hstable : (prefixWord ++ tailWord_2483054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483054).length < 2 ^ (prefixWord ++ tailWord_2483054).sum := by decide
  have hdescent : baseEnd_2483054 < baseStart_2483054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483150 : List Nat := [4, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4]
def baseStart_2483150 : Nat := 118140960795 + 2483150 * 2 ^ 59
def prefixEnd_2483150 : Nat := 4983230072969 + 3 ^ 40 * 2483150 * 2
def baseEnd_2483150 : Nat := 1275049487212064897905207

theorem tailTrace_2483150 : CollatzResearch.WordTrace tailWord_2483150 prefixEnd_2483150 1275049487212064897905207 := by
  unfold tailWord_2483150
  simp only [CollatzResearch.WordTrace]
  refine ⟨11320990119247389137714863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60378613969319408734479269 11320990119247389137714863)
  ·
    refine ⟨16981485178871083706572295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11320990119247389137714863 16981485178871083706572295)
    ·
      refine ⟨25472227768306625559858443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16981485178871083706572295 25472227768306625559858443)
      ·
        refine ⟨38208341652459938339787665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25472227768306625559858443 38208341652459938339787665)
        ·
          refine ⟨28656256239344953754840749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38208341652459938339787665 28656256239344953754840749)
          ·
            refine ⟨10746096089754357658065281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28656256239344953754840749 10746096089754357658065281)
            ·
              refine ⟨8059572067315768243548961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10746096089754357658065281 8059572067315768243548961)
              ·
                refine ⟨6044679050486826182661721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8059572067315768243548961 6044679050486826182661721)
                ·
                  refine ⟨4533509287865119636996291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6044679050486826182661721 4533509287865119636996291)
                  ·
                    refine ⟨6800263931797679455494437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4533509287865119636996291 6800263931797679455494437)
                    ·
                      refine ⟨1275049487212064897905207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6800263931797679455494437 1275049487212064897905207)
                      ·
                        rfl

theorem cell23_2483150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_2483150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483150 prefixEnd_2483150 := by exact prefixLift 2483150
  have htrace : WordTrace (prefixWord ++ tailWord_2483150) baseStart_2483150 baseEnd_2483150 := by
    simpa [prefixWord, tailWord_2483150, baseEnd_2483150] using wordTrace_append hprefix tailTrace_2483150
  have hstable : (prefixWord ++ tailWord_2483150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483150).length < 2 ^ (prefixWord ++ tailWord_2483150).sum := by decide
  have hdescent : baseEnd_2483150 < baseStart_2483150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483167 : List Nat := [1, 1, 2, 3, 5, 1, 1, 1, 2, 4, 2]
def baseStart_2483167 : Nat := 118140960795 + 2483167 * 2 ^ 59
def prefixEnd_2483167 : Nat := 4983230072969 + 3 ^ 40 * 2483167 * 2
def baseEnd_2483167 : Nat := 1275058216383191331392629

theorem tailTrace_2483167 : CollatzResearch.WordTrace tailWord_2483167 prefixEnd_2483167 1275058216383191331392629 := by
  unfold tailWord_2483167
  simp only [CollatzResearch.WordTrace]
  refine ⟨90568540994917525005087755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60379027329945016670058503 90568540994917525005087755)
  ·
    refine ⟨135852811492376287507631633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90568540994917525005087755 135852811492376287507631633)
    ·
      refine ⟨101889608619282215630723725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135852811492376287507631633 101889608619282215630723725)
      ·
        refine ⟨38208603232230830861521397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101889608619282215630723725 38208603232230830861521397)
        ·
          refine ⟨3582056553021640393267631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38208603232230830861521397 3582056553021640393267631)
          ·
            refine ⟨5373084829532460589901447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3582056553021640393267631 5373084829532460589901447)
            ·
              refine ⟨8059627244298690884852171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5373084829532460589901447 8059627244298690884852171)
              ·
                refine ⟨12089440866448036327278257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8059627244298690884852171 12089440866448036327278257)
                ·
                  refine ⟨9067080649836027245458693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12089440866448036327278257 9067080649836027245458693)
                  ·
                    refine ⟨1700077621844255108523505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9067080649836027245458693 1700077621844255108523505)
                    ·
                      refine ⟨1275058216383191331392629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1700077621844255108523505 1275058216383191331392629)
                      ·
                        rfl

theorem cell23_2483167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 4, 2].length) (baseStart_2483167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483167 prefixEnd_2483167 := by exact prefixLift 2483167
  have htrace : WordTrace (prefixWord ++ tailWord_2483167) baseStart_2483167 baseEnd_2483167 := by
    simpa [prefixWord, tailWord_2483167, baseEnd_2483167] using wordTrace_append hprefix tailTrace_2483167
  have hstable : (prefixWord ++ tailWord_2483167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483167).length < 2 ^ (prefixWord ++ tailWord_2483167).sum := by decide
  have hdescent : baseEnd_2483167 < baseStart_2483167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483243 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 5]
def baseStart_2483243 : Nat := 118140960795 + 2483243 * 2 ^ 59
def prefixEnd_2483243 : Nat := 4983230072969 + 3 ^ 40 * 2483243 * 2
def baseEnd_2483243 : Nat := 1275097240912933034042279

theorem tailTrace_2483243 : CollatzResearch.WordTrace tailWord_2483243 prefixEnd_2483243 1275097240912933034042279 := by
  unfold tailWord_2483243
  simp only [CollatzResearch.WordTrace]
  refine ⟨90571312942642189984854383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60380875295094793323236255 90571312942642189984854383)
  ·
    refine ⟨135856969413963284977281575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90571312942642189984854383 135856969413963284977281575)
    ·
      refine ⟨203785454120944927465922363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135856969413963284977281575 203785454120944927465922363)
      ·
        refine ⟨305678181181417391198883545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203785454120944927465922363 305678181181417391198883545)
        ·
          refine ⟨229258635886063043399162659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305678181181417391198883545 229258635886063043399162659)
          ·
            refine ⟨343887953829094565098743989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229258635886063043399162659 343887953829094565098743989)
            ·
              refine ⟨32239495671477615478007249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 343887953829094565098743989 32239495671477615478007249)
              ·
                refine ⟨24179621753608211608505437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32239495671477615478007249 24179621753608211608505437)
                ·
                  refine ⟨9067358157603079353189539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24179621753608211608505437 9067358157603079353189539)
                  ·
                    refine ⟨13601037236404619029784309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9067358157603079353189539 13601037236404619029784309)
                    ·
                      refine ⟨1275097240912933034042279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13601037236404619029784309 1275097240912933034042279)
                      ·
                        rfl

theorem cell23_2483243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 5].length) (baseStart_2483243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483243 prefixEnd_2483243 := by exact prefixLift 2483243
  have htrace : WordTrace (prefixWord ++ tailWord_2483243) baseStart_2483243 baseEnd_2483243 := by
    simpa [prefixWord, tailWord_2483243, baseEnd_2483243] using wordTrace_append hprefix tailTrace_2483243
  have hstable : (prefixWord ++ tailWord_2483243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483243).length < 2 ^ (prefixWord ++ tailWord_2483243).sum := by decide
  have hdescent : baseEnd_2483243 < baseStart_2483243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
